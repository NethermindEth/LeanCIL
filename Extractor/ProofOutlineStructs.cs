using System.Globalization;
using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Straight-line instance methods of structs: `this` is a reference to the caller's struct, whose word fields
// the body loads and stores through it.
internal static partial class ProofOutline
{
    /// <summary>A word field of the receiver the body reaches: where it lives, the binder naming its value on
    /// entry when the body reads it first, and whether the body stores it.</summary>
    sealed class StructField(string name, int offset, string receiver)
    {
        internal string Name { get; } = name;
        internal int Offset { get; } = offset;

        /// <summary>The field's address, the receiver itself at offset zero.</summary>
        internal string Address { get; } = offset == 0 ? receiver : $"({receiver}.element 1 {offset})";

        internal string? Initial { get; set; }
        internal bool Stored { get; set; }
    }

    /// <summary>What a struct method's body does, in order: a field load or the one field store, with the
    /// facts each needs; null `Stopped` when the walk reached the return.</summary>
    sealed class StructWalk
    {
        internal List<StructField> Fields { get; } = [];
        internal List<(StructField Field, bool AfterStore)> Loads { get; } = [];
        internal (StructField Field, string Value)? Store { get; set; }
        internal string? Returned { get; set; }
        internal string? Stopped { get; set; }
    }

    /// <summary>Walks a branch-free body over the receiver's 64-bit fields and word arguments; it stops at
    /// anything else, at a second store, and at a load after the store of a field other than the stored one,
    /// whose contents the outline carries only for the field it wrote.</summary>
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
        StructField? Field(int pc, int offset)
        {
            if (spec.Method.Body.Instructions[pc].Operand is not FieldReference reference) return null;
            var field = walk.Fields.FirstOrDefault(known => known.Offset == offset);
            if (field is not null) return field;
            field = new StructField(reference.Name, offset, receiver.Name);
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
                else return Stop($"the argument `{parameter.Name}`", pc);
            }
            else if ((match = Regex.Match(op, @"\A\.const64 (\d+)\z")).Success) stack.Push(match.Groups[1].Value);
            // A small literal the compiler loads as an int and widens is the same 64-bit literal.
            else if ((match = Regex.Match(op, @"\A\.const32 (\d+)\z")).Success && pc + 1 < ops.Length &&
                ops[pc + 1] is ".convU8" or ".convI8")
            {
                stack.Push(match.Groups[1].Value);
                pc++;
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
            else if ((match = Regex.Match(op, @"\A\.fieldAt (\d+) 8(?: false)?\z")).Success)
            {
                if (stack.Count == 0 || stack.Pop() != Receiver) return Stop("a field load of another value", pc);
                if (Field(pc, int.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture)) is not { } field)
                    return Stop("a field load the outline cannot name", pc);
                if (walk.Store is { } store && store.Field != field)
                    return Stop($"a load of `{field.Name}` after the store of `{store.Field.Name}`", pc);
                if (walk.Store is { } written)
                {
                    walk.Loads.Add((field, true));
                    stack.Push(written.Value);
                }
                else
                {
                    field.Initial ??= names.Claim(receiver.Name + Capitalized(field.Name), "field" + field.Offset);
                    walk.Loads.Add((field, false));
                    stack.Push(field.Initial);
                }
            }
            else if ((match = Regex.Match(op, @"\A\.setFieldAt (\d+) 8\z")).Success)
            {
                if (stack.Count < 2) return Stop("a field store on a short stack", pc);
                var value = stack.Pop();
                if (stack.Pop() != Receiver) return Stop("a field store into another value", pc);
                if (value is null or Receiver) return Stop("a field store of a value the outline does not name", pc);
                if (walk.Store is not null) return Stop("a second field store", pc);
                if (Field(pc, int.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture)) is not { } field)
                    return Stop("a field store the outline cannot name", pc);
                field.Stored = true;
                walk.Store = (field, value);
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
                        spec.Result.Constructor != ".i64")
                        return Stop("a result the outline does not name", pc);
                    walk.Returned = result;
                }
                return walk;
            }
            else return Stop($"`{op}`, which the outline does not step through a struct", pc);
        }
        return Stop("the end of the body without a return", ops.Length - 1);
    }

    /// <summary>The binders the specification names: the receiver, the word arguments, and the value each field
    /// read on entry holds.</summary>
    static IEnumerable<(string Name, string Type)> StructBinders(Specification spec, StructWalk walk) =>
        spec.Parameters.Select(parameter => (parameter.Name, parameter.Lean))
            .Concat(walk.Fields.Where(field => field.Initial is not null).Select(field => (field.Initial!, "W64")));

    /// <summary>A struct instance method stepped through its field loads and its store, leaving the
    /// postcondition, or one hole naming where the walk stopped.</summary>
    static string StructStraightLine(Specification spec, Body body, Names names, Writer lean)
    {
        var walk = WalkStruct(spec, body.Ops, names);
        var stepped = walk.Stopped is null;
        Header(lean, spec, ["CIL.Verification", "CIL.Safety.SymbolicExecution", "CIL.Safety.BufferContents",
            "CIL.Safety.LoopCallerFacts"], stepped ? "`postcondition`" : null);
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
        var footprint = walk.Store is { } store ? $"[({store.Field.Address}, 8)]" : "[]";
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
                premises.Add($"Contents initial {field.Address} 8 [{field.Initial}]");
                facts.Add(field.Initial + "Read");
            }
            if (field.Stored)
            {
                premises.Add($"Writable initial {field.Address} 8 0 1");
                facts.Add(receiver + Capitalized(field.Name) + "Owned");
            }
        }
        premises.Add($"Precondition {arguments} initial");
        lean.Conjunction("    (fun args initial => ", premises, ")");
        var returned = spec.Result is null ? "results = []" : "∃ result : W64, results = [.scalar (.i64 result)]";
        lean.Conjunction("    (fun _ initial final results => ", [returned,
            $"Confined {footprint} initial final",
            $"Postcondition {arguments} initial final{(spec.Result is null ? "" : " result")}"], ") := by");
        lean.Line($"  rintro args initial ⟨rfl, wellFormed, {string.Join(", ", facts)}, assumed⟩");
        if (!stepped)
        {
            lean.Line("  -- Step the body with `cil_checked_steps [facts]`, giving each field access its `add` and");
            lean.Line("  -- `loadValue` facts and the store its `write`.");
            lean.Noted("  ", "sorry", $"{NotOutlined}the body meets {walk.Stopped}; prove its run and Postcondition");
            Footer(lean);
            return lean.ToString();
        }
        var steps = new List<string> { receiver + "Form" };
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
                lean.Line($"  have loaded{field.Offset} := {field.Initial}Read.load_word (index := 0) rfl");
                steps.Add("loaded" + field.Offset);
            }
        }
        var final = "initial";
        var confined = "Confined.refl _ _";
        if (walk.Store is { } written)
        {
            var owned = receiver + Capitalized(written.Field.Name) + "Owned";
            lean.Line("  obtain ⟨stored1, written1, -, confined1, held1⟩ :=");
            lean.Line($"    {owned}.write_one ({written.Value})");
            lean.Line("  have formed1 := write_preserves_wellFormed _ _ _ _ _ wellFormed written1");
            // A write changes bytes only, so the receiver still forms.
            lean.Line($"  have form1 : form stored1 {receiver} = .ok {receiver} :=");
            lean.Line($"    (form_congr (by rw [write_allocations _ _ _ _ _ written1])).trans {receiver}Form");
            steps.Add("written1");
            if (walk.Loads.Any(load => load.AfterStore))
            {
                FieldAddress(lean, "stored1", "formed1", "form1", receiver, written.Field,
                    "read_access (held1 0 _ rfl)",
                    "addedAfter");
                lean.Line("  have loadedAfter := held1.load_word (index := 0) rfl");
                steps.AddRange(["form1", "addedAfter", "loadedAfter"]);
            }
            (final, confined) = ("stored1", "confined1");
        }
        var loads = steps.Where(step => step.StartsWith("loaded", StringComparison.Ordinal)).ToArray();
        if (loads.Length > 0) lean.Line($"  simp only [Reference.element_zero] at {string.Join(" ", loads)}");
        if (spec.Result is null)
            lean.Line($"  refine ⟨CIL.executionBound Extracted.program 0, {final}, [], ?run, rfl, {confined}, " +
                "?postcondition⟩");
        else
        {
            lean.Line($"  refine ⟨CIL.executionBound Extracted.program 0, {final},");
            lean.Line($"    [.scalar (.i64 ({walk.Returned}))], ?run,");
            lean.Line($"    {walk.Returned}, rfl, {confined}, ?postcondition⟩");
        }
        lean.Line($"  case run => cil_checked_steps [{string.Join(", ", steps)}]");
        var held = walk.Store is null ? "" : ", with `held1` the stored field's contents";
        lean.Noted("  ", "case postcondition => sorry", "Postcondition of the result" + held);
        Footer(lean);
        return lean.ToString();
    }

    /// <summary>The fact that the field access's `add` of its offset to the receiver reaches the field.</summary>
    static void FieldAddress(Writer lean, string memory, string wellFormed, string form, string receiver,
        StructField field, string access, string name)
    {
        lean.Line($"  have {name} : add {memory} {receiver} 1 (BitVec.ofNat 64 {field.Offset}) = " +
            $".ok {field.Address} := by");
        lean.Line($"    simpa using add_field (offset := {field.Offset}) {wellFormed} {form}");
        lean.Line($"      (by simpa using {access})");
    }
}