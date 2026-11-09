using System.Globalization;
using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Straight-line instance methods of structs: `this` is a reference to the caller's struct, whose scalar fields
// the body loads and stores through it.
internal static partial class ProofOutline
{
    /// <summary>A scalar field of the receiver the body reaches: where it lives, the binder naming its value on
    /// entry when the body reads it first, and whether the body stores it.</summary>
    sealed class StructField(string name, int offset, int width, string receiver)
    {
        internal string Name { get; } = name;
        internal int Offset { get; } = offset;
        internal int Width { get; } = width;

        /// <summary>The field's address, the receiver itself at offset zero.</summary>
        internal string Address { get; } = offset == 0 ? receiver : $"({receiver}.element 1 {offset})";

        internal string? Initial { get; set; }
        internal bool Stored { get; set; }
    }

    /// <summary>What a struct method's body does, in order: field loads and stores, with the
    /// facts each needs; null `Stopped` when the walk reached the return.</summary>
    sealed class StructWalk
    {
        internal List<StructField> Fields { get; } = [];
        internal List<(StructField Field, string Value, string Source)> Stores { get; } = [];
        internal string? Returned { get; set; }
        internal string? Stopped { get; set; }
    }

    /// <summary>A scalar literal with its stack width in bytes; conversions preserve this source width.</summary>
    static (string Term, int Width)? StructLiteral(string op)
    {
        var match = Regex.Match(op,
            @"\A\.const(32|64) (?:(\d+)|(\(BitVec\.ofInt \1 \(-?\d+\)\)))\z");
        if (!match.Success) return null;
        var term = match.Groups[2].Success ? $"({match.Groups[2].Value}#{match.Groups[1].Value})"
            : match.Groups[3].Value;
        return (term, match.Groups[1].Value == "64" ? 8 : 4);
    }

    /// <summary>Walks a branch-free body over the receiver's disjoint scalar fields and integer arguments.</summary>
    static StructWalk WalkStruct(Specification spec, string[] ops, Names names)
    {
        var walk = new StructWalk();
        var receiver = spec.Parameters[0];
        var stack = new Stack<string?>();
        const string Receiver = "\u0000receiver";
        StructWalk Stop(string reason, int pc)
        {
            walk.Stopped = $"{reason} at {Location(spec.Method, pc)}";
            return walk;
        }
        StructField? Field(int pc, int offset, int width)
        {
            if (spec.Method.Body.Instructions[pc].Operand is not FieldReference reference) return null;
            var field = walk.Fields.FirstOrDefault(known => known.Offset == offset);
            if (field is not null) return field.Width == width ? field : null;
            if (walk.Fields.Any(known => known.Offset < offset + width && offset < known.Offset + known.Width))
                return null;
            field = new StructField(reference.Name, offset, width, receiver.Name);
            walk.Fields.Add(field);
            return field;
        }
        for (var pc = 0; pc < ops.Length; pc++)
        {
            var op = ops[pc];
            Match match;
            if ((match = Regex.Match(op, @"\A\.arg (\d+)\z")).Success)
            {
                var parameter = spec.Parameters[int.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture)];
                if (parameter.Shape == ParameterShape.StructReference) stack.Push(Receiver);
                else if (parameter.Shape == ParameterShape.Scalar) stack.Push(parameter.Name);
                else if (parameter.Shape == ParameterShape.Narrow)
                    stack.Push($"({parameter.Name}.{(parameter.Signed ? "signExtend" : "setWidth")} 32)");
                else return Stop($"the argument `{parameter.Name}`", pc);
            }
            else if (StructLiteral(op) is { } literal) stack.Push(literal.Term);
            else if ((match = Regex.Match(op, @"\A\.conv([UI])([1248])\z")).Success)
            {
                if (stack.Count == 0 || stack.Pop() is not { } value || value == Receiver)
                    return Stop("a conversion of a value the outline does not name", pc);
                var bits = int.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture) * 8;
                var extension = match.Groups[1].Value == "I" ? "signExtend" : "setWidth";
                stack.Push(bits < 32 ? $"(({value}).setWidth {bits}).{extension} 32"
                    : $"({value}).{extension} {bits}");
            }
            else if ((match = Regex.Match(op, @"\A\.(add|sub|mul|band|bor|bxor)\z")).Success)
            {
                if (stack.Count < 2) return Stop($"`{op}` on a short stack", pc);
                var (right, left) = (stack.Pop(), stack.Pop());
                if (left is null or Receiver || right is null or Receiver)
                    return Stop($"`{op}` on a value the outline does not name", pc);
                var symbol = match.Groups[1].Value switch
                {
                    "add" => "+", "sub" => "-", "mul" => "*", "band" => "&&&", "bor" => "|||", _ => "^^^"
                };
                stack.Push($"{Operand(left)} {symbol} {Operand(right)}");
            }
            else if ((match = Regex.Match(op, @"\A\.fieldAt (\d+) (1|2|4|8)(?: (false|true))?\z")).Success)
            {
                if (stack.Count == 0 || stack.Pop() != Receiver) return Stop("a field load of another value", pc);
                if (Field(pc, int.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture),
                        int.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture)) is not { } field)
                    return Stop("a field load the outline cannot name", pc);
                var written = walk.Stores.LastOrDefault(store => store.Field == field);
                if (written.Field is not null)
                {
                    stack.Push(Loaded(written.Value));
                }
                else
                {
                    field.Initial ??= names.Claim(receiver.Name + Capitalized(field.Name), "field" + field.Offset);
                    stack.Push(Loaded(field.Initial));
                }
                string Loaded(string value) => field.Width < 4
                    ? $"({value}).{(match.Groups[3].Value == "true" ? "signExtend" : "setWidth")} 32" : value;
            }
            else if ((match = Regex.Match(op, @"\A\.setFieldAt (\d+) (1|2|4|8)\z")).Success)
            {
                if (stack.Count < 2) return Stop("a field store on a short stack", pc);
                var value = stack.Pop();
                if (stack.Pop() != Receiver) return Stop("a field store into another value", pc);
                if (value is null or Receiver) return Stop("a field store of a value the outline does not name", pc);
                if (Field(pc, int.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture),
                        int.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture)) is not { } field)
                    return Stop("a field store the outline cannot name", pc);
                field.Stored = true;
                walk.Stores.Add((field, field.Width < 4 ? $"({value}).setWidth {field.Width * 8}" : value, value));
            }
            else if (op == ".dup")
            {
                if (stack.Count == 0) return Stop("a duplicate of an empty stack", pc);
                stack.Push(stack.Peek());
            }
            else if (op == ".nop") { }
            else if (op == ".ret" && pc == ops.Length - 1)
            {
                if (spec.Result is not null)
                {
                    if (stack.Count == 0 || stack.Peek() is not { } result || result == Receiver ||
                        spec.Result.Boolean || spec.Result.Constructor is not (".i64" or ".i32"))
                        return Stop("a result the outline does not name", pc);
                    walk.Returned = result;
                }
                return walk;
            }
            else return Stop($"`{op}`, which the outline does not step through a struct", pc);
        }
        return Stop("the end of the body without a return", ops.Length - 1);
    }

    /// <summary>The binders the specification names: the receiver, the integer arguments, and the value each field
    /// read on entry holds.</summary>
    static IEnumerable<(string Name, string Type)> StructBinders(Specification spec, StructWalk walk) =>
        spec.Parameters.Select(parameter => (parameter.Name, parameter.Lean))
            .Concat(walk.Fields.Where(field => field.Initial is not null).Select(field =>
                (field.Initial!, field.Width == 8 ? "W64" : field.Width == 4 ? "W32" : $"BitVec {field.Width * 8}")));

    /// <summary>A struct instance method stepped through its field loads and stores, leaving the
    /// postcondition, or one hole naming where the walk stopped.</summary>
    static string StructStraightLine(Specification spec, Body body, Names names, Writer lean)
    {
        var walk = WalkStruct(spec, body.Ops, names);
        var stepped = walk.Stopped is null;
        Header(lean, spec, ["CIL.Verification", "CIL.Safety.SymbolicExecution", "CIL.Safety.BufferContents",
            "CIL.Safety.LoopCallerFacts", "CIL.Safety.AggregateFields"], stepped ? "`postcondition`" : null);
        var binders = StructBinders(spec, walk).ToArray();
        var arguments = string.Join(" ", binders.Select(binder => binder.Name));
        var receiver = spec.Parameters[0].Name;
        lean.Line("/-- Replace with what callers must guarantee about the arguments, or `True`. -/");
        lean.Wrapped("def Precondition", Grouped(binders.Append(("initial", "Memory"))), ": Prop := sorry");
        lean.Line();
        lean.Line($"/-- Replace with what `{spec.Method.Name}` guarantees about its result and the caller's " +
            "memory. -/");
        var post = binders.Concat([("initial", "Memory"), ("final", "Memory")]);
        if (spec.Result is not null) post = post.Append(("result", spec.Result.Lean));
        lean.Wrapped("def Postcondition", Grouped(post), ": Prop := sorry");
        lean.Line();
        var footprint = "[" + string.Join(", ", walk.Fields.Where(field => field.Stored)
            .Select(field => $"({field.Address}, {field.Width})")) + "]";
        lean.Wrapped("theorem correctness", Grouped(binders), ": Ensures Extracted.program 0");
        var premises = new List<string>
        {
            $"args = {spec.ArgumentValues}", "initial.WellFormed", $"form initial {receiver} = .ok {receiver}"
        };
        var facts = new List<string> { receiver + "Form" };
        foreach (var field in walk.Fields)
        {
            if (field.Initial is not null)
            {
                premises.Add($"Contents initial {field.Address} {field.Width} [{field.Initial}]");
                facts.Add(field.Initial + "Read");
            }
            if (field.Stored)
            {
                premises.Add($"Writable initial {field.Address} {field.Width} 0 1");
                facts.Add(receiver + Capitalized(field.Name) + "Owned");
            }
        }
        premises.Add($"Precondition {arguments} initial");
        lean.Conjunction("    (fun args initial => ", premises, ")");
        var encodedResult = spec.Result?.Encode(spec.Result.Boolean ? "(if result then 1#32 else 0#32)" : "result");
        var returned = spec.Result is null ? "results = []"
            : $"∃ result : {spec.Result.Lean}, results = [{encodedResult}]";
        var postcondition = new Writer();
        postcondition.Wrapped("      Postcondition", arguments.Split(' '),
            $"initial final{(spec.Result is null ? "" : " result")}");
        lean.Conjunction("    (fun _ initial final results => ", [returned,
            $"Confined {footprint} initial final",
            postcondition.ToString().Trim()], ") := by");
        lean.Line($"  rintro args initial ⟨rfl, wellFormed, {string.Join(", ", facts)}, assumed⟩");
        if (!stepped)
        {
            lean.Line("  -- Step the body with `cil_checked_steps [facts]`, giving each field access its `add` and");
            lean.Line("  -- `loadValue` facts and the store its `write`.");
            lean.Noted("  ", "sorry", $"{NotOutlined}the body meets {walk.Stopped}; prove its run and Postcondition");
            Footer(lean);
            return lean.ToString();
        }
        var steps = new List<string> { receiver + "Form", "CIL.NarrowKind.extend" };
        foreach (var width in walk.Fields.Select(field => field.Width).Where(width => width < 4).Distinct())
        {
            lean.Line($"  have loadSigned{width} (memory : Memory) (address : Reference) (value : BitVec {8 * width})");
            lean.Line($"      (contents : Contents memory address {width} [value]) :");
            lean.Line($"      loadValue memory (.address address) {width} true = " +
                ".ok (.i32 (value.signExtend 32)) := by");
            lean.Line("    have loaded := loadValue_signed_of_read (by decide) (contents 0 value rfl)");
            lean.Line($"    simpa only [Reference.element_zero, element_value (width := {width}) value, " +
                "signedOfWidth,");
            lean.Line("      BitVec.ofNat_toNat, BitVec.setWidth_eq] using loaded");
        }
        // Each field's address and value at entry, from its contents or its write authority.
        foreach (var field in walk.Fields)
        {
            var access = field.Initial is not null
                ? $"read_access ({field.Initial}Read 0 _ rfl)"
                : $"{receiver}{Capitalized(field.Name)}Owned 0 (by omega)";
            FieldAddress(lean, "initial", "wellFormed", receiver + "Form", receiver, field, access,
                "added" + field.Offset);
            steps.Add("added" + field.Offset);
            if (field.Initial is not null)
            {
                LoadStructField(lean, field, field.Initial + "Read", "loaded" + field.Offset);
                steps.Add("loaded" + field.Offset);
                if (field.Width < 4) steps.Add("loaded" + field.Offset + "Signed");
            }
        }
        var final = "initial";
        var confined = "Confined.refl _ _";
        var contents = walk.Fields.Where(field => field.Initial is not null)
            .ToDictionary(field => field, field => field.Initial + "Read");
        var ownership = walk.Fields.Where(field => field.Stored)
            .ToDictionary(field => field, field => receiver + Capitalized(field.Name) + "Owned");
        for (var index = 0; index < walk.Stores.Count; index++)
        {
            var written = walk.Stores[index];
            var level = index + 1;
            var owned = ownership[written.Field];
            lean.Line($"  obtain ⟨stored{level}, written{level}, -, confined{level}, held{level}⟩ :=");
            lean.Line($"    {owned}.write_one");
            lean.Wrapped("     ", $"({written.Value})".Terms(), "");
            if (written.Field.Width < 4)
            {
                lean.Line($"  have encoded{level} : write {final} {written.Field.Address}");
                lean.Wrapped("     ", $"(numberBytes ({written.Source}).toNat {written.Field.Width})".Terms(),
                    $"1 = .ok stored{level} := by");
                lean.Wrapped("    have bytes :=", $"numberBytes_mod (({written.Source}) : W32).toNat".Terms(),
                    written.Field.Width.ToString(CultureInfo.InvariantCulture));
                lean.Line($"    exact (congrArg (fun bytes => write {final} {written.Field.Address} bytes 1)");
                lean.Line($"      bytes).symm.trans written{level}");
                steps.Add($"encoded{level}");
            }
            var formed = index == 0 ? "wellFormed" : $"formed{index}";
            lean.Line($"  have formed{level} := write_preserves_wellFormed _ _ _ _ _ {formed} written{level}");
            // A write changes bytes only, so the receiver still forms.
            var previousForm = index == 0 ? receiver + "Form" : $"form{index}";
            lean.Line($"  have form{level} : form stored{level} {receiver} = .ok {receiver} :=");
            lean.Line($"    (form_congr (by rw [write_allocations _ _ _ _ _ written{level}])).trans {previousForm}");
            steps.AddRange([$"written{level}", $"form{level}"]);
            foreach (var field in contents.Keys.ToArray())
            {
                if (field == written.Field) continue;
                var held = $"kept{level}Field{field.Offset}";
                lean.Line($"  have {held} := {contents[field]}.after_write_apart written{level}");
                lean.Line("    (by simp [Apart, Reference.element, numberBytes_length] <;> omega)");
                contents[field] = held;
            }
            contents[written.Field] = $"held{level}";
            foreach (var field in ownership.Keys.ToArray())
            {
                var name = $"owned{level}Field{field.Offset}";
                lean.Line($"  have {name} := {ownership[field]}.after_write written{level}");
                ownership[field] = name;
            }
            foreach (var field in walk.Fields)
            {
                var access = contents.TryGetValue(field, out var held)
                    ? $"read_access ({held} 0 _ rfl)"
                    : $"{ownership[field]} 0 (by omega)";
                var added = $"added{level}Field{field.Offset}";
                FieldAddress(lean, $"stored{level}", $"formed{level}", $"form{level}", receiver, field, access, added);
                steps.Add(added);
                if (held is not null)
                {
                    var loaded = $"loaded{level}Field{field.Offset}";
                    LoadStructField(lean, field, held, loaded);
                    steps.Add(loaded);
                    if (field.Width < 4) steps.Add(loaded + "Signed");
                }
            }
            final = $"stored{level}";
            var previousMemory = index == 0 ? "initial" : $"stored{index}";
            lean.Line($"  have changed{level} : Confined {footprint} {previousMemory} {final} :=");
            lean.Line($"    confined{level}.widen (by simp)");
            if (index > 0)
                lean.Line($"  have combined{level} := {confined}.trans changed{level}");
            confined = index == 0 ? $"changed{level}" : $"combined{level}";
        }
        var loads = steps.Where(step => step.StartsWith("loaded", StringComparison.Ordinal) &&
            !step.EndsWith("Signed", StringComparison.Ordinal)).ToArray();
        foreach (var load in loads) lean.Line($"  simp only [Reference.element_zero] at {load}");
        if (spec.Result is null)
            lean.Line($"  refine ⟨CIL.executionBound Extracted.program 0, {final}, [], ?run, rfl, {confined}, " +
                "?postcondition⟩");
        else
        {
            lean.Line($"  refine ⟨CIL.executionBound Extracted.program 0, {final},");
            lean.Wrapped("   ", $"[.scalar ({spec.Result.Constructor} ({walk.Returned}))], ?run,".Terms(), "");
            lean.Wrapped("   ", $"{walk.Returned}, rfl, {confined}, ?postcondition⟩".Terms(), "");
        }
        lean.Wrapped("  case run => cil_checked_steps", $"[{string.Join(", ", steps)}]".Terms(), "");
        var postHint = walk.Stores.Count == 0 ? "" : ", with " +
            string.Join(", ", contents.Values.Select(fact => $"`{fact}`")) + " the final field contents";
        lean.Noted("  ", "case postcondition => sorry", "Postcondition of the result" + postHint);
        Footer(lean);
        return lean.ToString();
    }

    /// <summary>A scalar field's loaded value, normalized to the stack's word width.</summary>
    static void LoadStructField(Writer lean, StructField field, string contents, string name)
    {
        if (field.Width == 8)
            lean.Line($"  have {name} := {contents}.load_word (index := 0) rfl");
        else
        {
            lean.Line($"  have {name} := {contents}.load (by decide) (index := 0) rfl");
            var normalized = field.Width == 4 ? ", BitVec.setWidth_eq" : "";
            lean.Line($"  simp only [numericOfWidth, BitVec.ofNat_toNat{normalized}] at {name}");
            if (field.Width < 4)
            {
                lean.Line($"  have {name}Signed := loadSigned{field.Width} _ _ _ {contents}");
            }
        }
    }

    /// <summary>The fact that the field access's `add` of its offset to the receiver reaches the field.</summary>
    static void FieldAddress(Writer lean, string memory, string wellFormed, string form, string receiver,
        StructField field, string access, string name)
    {
        lean.Line($"  have {name} : add {memory} {receiver} 1 (BitVec.ofNat 64 {field.Offset}) =");
        lean.Line($"      .ok {field.Address} := by");
        lean.Line($"    simpa using add_field (offset := {field.Offset}) {wellFormed} {form}");
        lean.Line($"      (by simpa using {access})");
    }
}
