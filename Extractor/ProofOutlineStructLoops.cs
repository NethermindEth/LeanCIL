using System.Globalization;
using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal static partial class ProofOutline
{
    /// <summary>A scalar field kept across iterations of a receiver loop.</summary>
    sealed record ReceiverField(string Name, string ReadName, string OwnedName, int Offset, bool Written)
    {
        internal string Address(string receiver) => Offset == 0 ? receiver : $"({receiver}.element 1 {Offset})";
    }

    /// <summary>A receiver loop with no frame-owned locals: its state records caller field contents and
    /// authority, and every generated path is checked against the extracted instructions.</summary>
    sealed class ReceiverLoop(Specification spec, Body body, Writer lean)
    {
        string receiver => spec.Parameters[0].Name;
        readonly List<ReceiverField> fields = [];
        readonly Names identifiers = new();
        int header;
        int names;
        string Footprint => "[" + string.Join(", ", fields.Where(item => item.Written)
            .Select(item => $"({item.Address(receiver)}, 8)")) + "]";
        string Parameters => string.Join(" ", spec.Parameters.Select(parameter => parameter.Name));
        string StateType => $"State {receiver} initial";
        string HeaderTerm => $"(header {receiver} initial)";

        void Line(string text = "")
        {
            if (text.Length <= Writer.Limit) { lean.Line(text); return; }
            var terms = text.TrimStart().Terms().ToArray();
            lean.Wrapped(text[..(text.Length - text.TrimStart().Length)] + terms[0], terms.Skip(1), "");
        }

        internal string Generate()
        {
            foreach (var local in new[]
                { "state", "same", "checked", "next", "invariantHeld", "initialState", "formed" })
                identifiers.Claim(local, local);
            // User binders cannot capture the path facts or the state introduced below.
            var parameters = spec.Parameters.Select(parameter => parameter with
            {
                Name = identifiers.Claim(SafeName(parameter.Name), "argument")
            }).ToArray();
            spec = new(spec.Method, parameters, spec.Result, spec.Symbolic, spec.Classes);
            var loops = body.Loops();
            if (loops.Count != 1 || !Body.Conditional(body.Ops[loops[0].Latch]) ||
                spec.Method.Body.Variables.Count != 0 || spec.Parameters.Any(parameter =>
                    parameter.Shape is not (ParameterShape.StructReference or ParameterShape.Scalar) ||
                    parameter.Shape == ParameterShape.Scalar && parameter.Width != 8) ||
                spec.Result is { Constructor: not ".i64" })
                throw Unsupported("A struct receiver loop needs one conditional back edge, no local homes, " +
                    "and word arguments with a void or 64-bit result");
            header = body.BlockStart(loops[0].Latch);
            for (var pc = 0; pc < body.Ops.Length; pc++)
            {
                var match = Regex.Match(body.Ops[pc], @"\A\.(fieldAt|setFieldAt) (\d+) 8(?: false)?\z");
                if (!match.Success) continue;
                var offset = int.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture);
                if (spec.Method.Body.Instructions[pc].Operand is not FieldReference reference)
                    throw Unsupported("A receiver field has no metadata name");
                var known = fields.FindIndex(field => field.Offset == offset);
                var written = match.Groups[1].Value == "setFieldAt";
                if (known >= 0) fields[known] = fields[known] with { Written = fields[known].Written || written };
                else
                {
                    if (fields.Any(field => field.Offset < offset + 8 && offset < field.Offset + 8))
                        throw Unsupported("A receiver loop touches overlapping fields");
                    var fieldName = char.ToLowerInvariant(reference.Name[0]) + reference.Name[1..];
                    var name = identifiers.Claim(SafeName(fieldName),
                        "valueAt" + offset);
                    fields.Add(new(name, identifiers.Claim(name + "Read", "readAt" + offset),
                        identifiers.Claim(name + "Owned", "ownedAt" + offset), offset, written));
                }
            }
            if (fields.Count == 0) throw Unsupported("A receiver loop has no scalar fields to bind");
            Header(lean, spec, ["CIL.Verification", "CIL.Safety.LoopScaffold", "CIL.Safety.BufferContents",
                "CIL.Safety.LoopCallerFacts"], "`invariant`, `measure` and `postcondition`");
            var binders = spec.Parameters.Select(parameter => (parameter.Name, parameter.Lean)).ToArray();
            Line("/-- Caller assumptions beyond the stated field access and initialization facts. -/");
            lean.Wrapped("def Precondition", Grouped(binders.Append(("initial", "Memory"))), ": Prop := sorry");
            Line("/-- The required result and final caller-memory contents. -/");
            lean.Wrapped("def Postcondition", Grouped(binders.Concat([("initial", "Memory"), ("final", "Memory")])
                .Concat(spec.Result is null ? [] : [("result", "W64")])), ": Prop := sorry");
            Line();
            Line("/-- Field values and the memory facts needed to execute another iteration. -/");
            Line($"structure State ({receiver} : Reference) (initial : Memory) where");
            Line("  memory : Memory");
            foreach (var field in fields) Line($"  {field.Name} : W64");
            Line("  wellFormed : memory.WellFormed");
            Line($"  formed : form memory {receiver} = .ok {receiver}");
            foreach (var field in fields)
            {
                Line($"  {field.ReadName} : Contents memory {field.Address(receiver)} 8 [{field.Name}]");
                if (field.Written)
                    Line($"  {field.OwnedName} : Writable memory {field.Address(receiver)} 8 0 1");
            }
            Line($"  confined : Confined {Footprint} initial memory");
            Line();
            Line("/-- The checked cutpoint just before the loop condition loads its fields. -/");
            Line($"def header ({receiver} : Reference) (initial : Memory) (state : {StateType}) : LoopState :=");
            Line($"  ⟨{header}, ⟨initial.nextIdentity, [], [], [], 0⟩, [], state.memory⟩");
            Line("/-- The property preserved at the loop condition. -/");
            lean.Wrapped("def invariant", Grouped(binders.Concat([("initial", "Memory"), ("state", StateType)])),
                ": Prop := sorry");
            Line("/-- A natural number strictly decreasing on each continuing iteration. -/");
            lean.Wrapped("def measure", Grouped(binders.Concat([("initial", "Memory"), ("state", StateType)])),
                ": Nat := sorry");
            lean.Wrapped("theorem correctness", Grouped(binders), ": Ensures Extracted.program 0");
            lean.Conjunction("    (fun args initial => ", [$"args = {spec.ArgumentValues}",
                $"∃ state : {StateType},\n        state.memory = initial ∧ Precondition {Parameters} initial"], ")");
            var result = spec.Result is null ? "results = []" : "∃ result : W64, results = [.scalar (.i64 result)]";
            lean.Conjunction("    (fun _ initial final results => ", [result,
                $"Confined {Footprint} initial final",
                $"Postcondition {Parameters} initial final{(spec.Result is null ? "" : " result")}"], ") := by");
            Line("  rintro args initial ⟨rfl, state, same, assumed⟩");
            Line($"  have checked : {spec.ArgumentValues}.mapM (checkedValue initial) =");
            Line($"      .ok {spec.ArgumentValues} := by simp [cil_checked, ← same, state.formed]");
            Line($"  have setup : enterFrame Extracted.method0 {spec.ArgumentValues} initial =");
            Line("      .ok (⟨initial.nextIdentity, [], [], [], 0⟩, initial) := by rfl");
            Line($"  refine invoke_loop_satisfies Extracted.lookup0 checked setup {HeaderTerm}");
            Line($"    (invariant {Parameters} initial) (measure {Parameters} initial) (fun start => ?_) ?_");
            Line("  ·");
            var entry = Path("state");
            entry.Memory = "initial";
            entry.Facts.Add("same");
            foreach (var field in fields)
            {
                Line($"    have {field.ReadName} := state.{field.ReadName}");
                Line($"    rw [same] at {field.ReadName}");
                entry.Reads[field.Offset] = field.ReadName;
                if (field.Written)
                {
                    Line($"    have {field.OwnedName} := state.{field.OwnedName}");
                    Line($"    rw [same] at {field.OwnedName}");
                    entry.Owned[field.Offset] = field.OwnedName;
                }
            }
            Line("    have formed : form initial " + receiver + " = .ok " + receiver + " := by");
            Line("      simpa only [same] using state.formed");
            Line("    have wellFormed : initial.WellFormed := by simpa only [same] using state.wellFormed");
            entry.Formed = "formed";
            entry.WellFormed = "wellFormed";
            entry.Confined = "Confined.refl _ _";
            Walk(entry, 0, "    ", "start", false);
            Line("  · intro state invariantHeld next");
            Walk(Path("state"), header, "    ", "next", true);
            Footer(lean);
            return lean.ToString();
        }

        sealed class ReceiverPath
        {
            internal string Memory = "";
            internal string Formed = "";
            internal string WellFormed = "";
            internal string Confined = "";
            internal Dictionary<int, string> Values = [];
            internal Dictionary<int, string> Reads = [];
            internal Dictionary<int, string> Owned = [];
            internal List<string> Facts = [];
            internal List<string> Stack = [];
            internal bool Stepped;
            internal ReceiverPath Copy() => new()
            {
                Memory = Memory, Formed = Formed, WellFormed = WellFormed, Confined = Confined,
                Values = new(Values), Reads = new(Reads), Owned = new(Owned), Facts = [.. Facts], Stack = [.. Stack],
                Stepped = Stepped
            };
        }

        ReceiverPath Path(string state) => new()
        {
            Memory = state + ".memory", Formed = state + ".formed", WellFormed = state + ".wellFormed",
            Confined = state + ".confined", Values = fields.ToDictionary(field => field.Offset,
                field => state + "." + field.Name), Reads = fields.ToDictionary(field => field.Offset,
                field => state + "." + field.ReadName),
            Owned = fields.Where(field => field.Written).ToDictionary(field => field.Offset,
                field => state + "." + field.OwnedName), Facts = ["header", state + ".formed"]
        };

        string State(ReceiverPath path) => "⟨" + string.Join(", ", new[] { path.Memory }
            .Concat(fields.Select(field => path.Values[field.Offset]))
            .Concat([path.WellFormed, path.Formed]).Concat(fields.SelectMany(field => field.Written
                ? new[] { path.Reads[field.Offset], path.Owned[field.Offset] } : [path.Reads[field.Offset]]))
            .Append(path.Confined)) + "⟩";

        void Walk(ReceiverPath path, int pc, string indent, string hypothesis, bool iteration)
        {
            var visited = new HashSet<int>();
            while (pc < body.Ops.Length)
            {
                if (pc == header && (path.Stepped || !iteration))
                {
                    if (path.Stack.Count != 0)
                        throw Unsupported("A receiver loop carries an operand stack at its head");
                    lean.Wrapped(indent + "refine loop_reaches_terminates ?_", [$"({hypothesis}", State(path),
                        "?invariant" + (iteration ? " ?measure)" : ")")], "");
                    lean.Wrapped(indent + "· cil_loop_steps", ["[" + string.Join(", ", path.Facts) + "]"], "");
                    lean.Noted(indent, "case invariant => sorry", "Establish the invariant at this loop head");
                    if (iteration) lean.Noted(indent, "case measure => sorry", "The continuing iteration decreases");
                    return;
                }
                if (!visited.Add(pc)) throw Unsupported("A receiver loop path cycles outside its cutpoint");
                path.Stepped = true;
                var op = body.Ops[pc];
                string Pop()
                {
                    if (path.Stack.Count == 0) throw Unsupported("A receiver loop has a short symbolic stack");
                    var value = path.Stack[^1];
                    path.Stack.RemoveAt(path.Stack.Count - 1);
                    return value;
                }
                Match match;
                if ((match = Regex.Match(op, @"\A\.arg (\d+)\z")).Success)
                    path.Stack.Add(spec.Parameters[int.Parse(match.Groups[1].Value)].Name);
                else if ((match = Regex.Match(op, @"\A\.const(?:32|64) (\d+)\z")).Success)
                    path.Stack.Add(match.Groups[1].Value);
                else if (op is ".convU8" or ".convI8" or ".nop") { }
                else if (op == ".dup") path.Stack.Add(path.Stack[^1]);
                else if ((match = Regex.Match(op, @"\A\.(add|sub|mul|band|bor|bxor)\z")).Success)
                {
                    var right = Pop();
                    var left = Pop();
                    var symbol = match.Groups[1].Value switch
                    { "add" => "+", "sub" => "-", "mul" => "*", "band" => "&&&", "bor" => "|||", _ => "^^^" };
                    path.Stack.Add($"({left} {symbol} {right})");
                }
                else if ((match = Regex.Match(op, @"\A\.(fieldAt|setFieldAt) (\d+) 8(?: false)?\z")).Success)
                {
                    var field = fields.Single(field => field.Offset == int.Parse(match.Groups[2].Value));
                    var store = match.Groups[1].Value == "setFieldAt";
                    var value = store ? Pop() : "";
                    if (Pop() != receiver) throw Unsupported("A receiver loop accesses another struct's field");
                    Access(path, field, store ? value : null, indent);
                    if (!store) path.Stack.Add(path.Values[field.Offset]);
                }
                else if (Body.Target(op) is { } target)
                {
                    if (!Body.Conditional(op)) { pc = target; continue; }
                    var instruction = op.Split(' ')[0][1..];
                    var right = Pop();
                    var operands = instruction is "brzero" or "brnonzero" ? new[] { right } : [Pop(), right];
                    var (condition, taken) = Body.Test(instruction, operands, 64);
                    var fact = "branch" + ++names;
                    Line($"{indent}by_cases {fact} : {condition}");
                    var yes = path.Copy();
                    var no = path.Copy();
                    yes.Facts.Add(fact);
                    no.Facts.Add(fact);
                    Line(indent + "·");
                    Walk(yes, taken ? target : pc + 1, indent + "  ", hypothesis, iteration);
                    Line(indent + "·");
                    Walk(no, taken ? pc + 1 : target, indent + "  ", hypothesis, iteration);
                    return;
                }
                else if (op == ".ret")
                {
                    lean.Wrapped(indent + "cil_loop_finish", ["[" + string.Join(", ", path.Facts
                        .Concat([path.Confined])) + "]"], "");
                    if (spec.Result is not null)
                        Line($"{indent}refine ⟨{Pop()}, rfl, {path.Confined}, ?_⟩");
                    else Line($"{indent}all_goals try (first | rfl | exact {path.Confined})");
                    lean.Noted(indent, "all_goals sorry", "Required postcondition at this return");
                    return;
                }
                else throw Unsupported($"A receiver loop does not yet outline `{op}` at {Location(spec.Method, pc)}");
                pc++;
            }
            throw Unsupported("A receiver loop path has no return or continuing head");
        }

        /// <summary>A user name outside the numbered path-fact names emitted by the walk.</summary>
        static string SafeName(string name) => Regex.IsMatch(name,
            @"\A(?:(?:added|loaded|memory|written|confined|held|formed|wellFormed|changed|confinedTotal|branch)\d+|" +
            @"(?:kept|owned)\d+Field\d+)\z") ? name + "Argument" : name;

        void Access(ReceiverPath path, ReceiverField field, string? value, string indent)
        {
            var index = ++names;
            var address = field.Address(receiver);
            Line($"{indent}have added{index} : add {path.Memory} {receiver} 1 {field.Offset} = .ok {address} := by");
            Line($"{indent}  simpa using add_field (offset := {field.Offset}) {path.WellFormed} {path.Formed}");
            Line($"{indent}    (by simpa using read_access ({path.Reads[field.Offset]} 0 _ rfl))");
            path.Facts.Add("added" + index);
            if (value is null)
            {
                Line($"{indent}have loaded{index} := {path.Reads[field.Offset]}.load_word (index := 0) rfl");
                Line($"{indent}simp only [Reference.element_zero] at loaded{index}");
                path.Facts.Add("loaded" + index);
                return;
            }
            Line($"{indent}obtain ⟨memory{index}, written{index}, -, confined{index}, held{index}⟩ :=");
            Line($"{indent}  {path.Owned[field.Offset]}.write_one {value}");
            Line($"{indent}have formed{index} : form memory{index} {receiver} = .ok {receiver} :=");
            Line($"{indent}  (form_congr (by rw [write_allocations _ _ _ _ _ written{index}])).trans {path.Formed}");
            Line($"{indent}have wellFormed{index} := write_preserves_wellFormed _ _ _ _ _ " +
                $"{path.WellFormed} written{index}");
            foreach (var other in fields)
            {
                if (other != field)
                {
                    Line($"{indent}have kept{index}Field{other.Offset} := " +
                        $"{path.Reads[other.Offset]}.after_write_apart");
                    Line($"{indent}  written{index} " +
                        "(by simp [Apart, Reference.element, numberBytes_length] <;> omega)");
                    path.Reads[other.Offset] = $"kept{index}Field{other.Offset}";
                }
                if (other.Written)
                {
                    Line($"{indent}have owned{index}Field{other.Offset} := " +
                        $"{path.Owned[other.Offset]}.after_write written{index}");
                    path.Owned[other.Offset] = $"owned{index}Field{other.Offset}";
                }
            }
            Line($"{indent}have changed{index} : Confined {Footprint} {path.Memory} memory{index} :=");
            Line($"{indent}  confined{index}.widen (by simp)");
            Line($"{indent}have confinedTotal{index} := {path.Confined}.trans changed{index}");
            path.Memory = "memory" + index;
            path.Formed = "formed" + index;
            path.WellFormed = "wellFormed" + index;
            path.Confined = "confinedTotal" + index;
            path.Reads[field.Offset] = "held" + index;
            path.Values[field.Offset] = value;
            path.Facts.Add("written" + index);
            path.Facts.Add(path.Formed);
        }
    }
}
