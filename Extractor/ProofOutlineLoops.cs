using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// A loop's state, cutpoint and per-path obligations, derived by evaluating the emitted
// operations symbolically. A path the evaluation cannot follow becomes a hole, never a guess.
internal static partial class ProofOutline
{
    /// <summary>The emitted operations of one method and its control flow.</summary>
    sealed class Body(string[] ops)
    {
        internal string[] Ops { get; } = ops;

        internal static int? Target(string op) =>
            Regex.Match(op, @"\A\.(branch|brzero|brnonzero|beq|bne|blt|ble|bgt|bge|bltu|bleu|bgtu|bgeu) (\d+)\z")
                is { Success: true } match ? int.Parse(match.Groups[2].Value) : null;

        internal static bool Conditional(string op) => Target(op) is not null && !op.StartsWith(".branch ");

        /// <summary>The proposition a conditional branch tests of its `bits`-bit operands' terms, and whether it
        /// is taken when the proposition holds; signed comparisons read the words through `toInt`. A literal
        /// operand is written as default `simp` writes it, so the split's fact rewrites a simplified goal.</summary>
        internal static (string Condition, bool TakenWhenTrue) Test(string name, string[] terms, int bits)
        {
            string Word(int index) => Literal(terms[index], bits);
            string Signed(int index) => Regex.IsMatch(terms[index], @"\A\d+\z")
                ? SignedValue(terms[index], bits) : $"{terms[index]}.toInt";
            return name switch
            {
                "brzero" => ($"{terms[0]} = {Literal("0", bits)}", true),
                "brnonzero" => ($"{terms[0]} = {Literal("0", bits)}", false),
                "beq" => ($"{Word(0)} = {Word(1)}", true),
                "bne" => ($"{Word(0)} = {Word(1)}", false),
                "blt" => ($"{Signed(0)} < {Signed(1)}", true),
                "ble" => ($"{Signed(0)} ≤ {Signed(1)}", true),
                "bgt" => ($"{Signed(1)} < {Signed(0)}", true),
                "bge" => ($"{Signed(1)} ≤ {Signed(0)}", true),
                "bltu" => ($"{Word(0)} < {Word(1)}", true),
                "bleu" => ($"{Word(0)} ≤ {Word(1)}", true),
                "bgtu" => ($"{Word(1)} < {Word(0)}", true),
                "bgeu" => ($"{Word(1)} ≤ {Word(0)}", true),
                _ => throw new ArgumentException($"`{name}` is not a conditional branch", nameof(name))
            };
        }

        /// <summary>A decimal literal as the `bits`-bit word `simp` normalizes it to, such as `0#32`; any
        /// other term is returned as it is.</summary>
        internal static string Literal(string term, int bits) =>
            Regex.IsMatch(term, @"\A\d+\z") ? $"{term}#{bits}" : term;

        /// <summary>The integer a `bits`-bit decimal literal reads as through `toInt`, as `simp` writes it.</summary>
        static string SignedValue(string term, int bits)
        {
            var value = System.Numerics.BigInteger.Parse(term, System.Globalization.CultureInfo.InvariantCulture) %
                (System.Numerics.BigInteger.One << bits);
            if (value >= System.Numerics.BigInteger.One << (bits - 1)) value -= System.Numerics.BigInteger.One << bits;
            return value.Sign < 0 ? $"({value})" : value.ToString(System.Globalization.CultureInfo.InvariantCulture);
        }

        /// <summary>Each loop as its head and latch, the last pc branching back to it, in head order.</summary>
        internal List<(int Head, int Latch)> Loops() => Ops.Select((op, pc) => (Target: Target(op), Pc: pc))
            .Where(edge => edge.Target is { } target && target <= edge.Pc)
            .GroupBy(edge => edge.Target!.Value).OrderBy(group => group.Key)
            .Select(group => (group.Key, group.Max(edge => edge.Pc))).ToList();

        /// <summary>The first pc of the basic block holding `pc`.</summary>
        internal int BlockStart(int pc)
        {
            var leaders = new SortedSet<int> { 0 };
            for (var index = 0; index < Ops.Length; index++)
            {
                if (Target(Ops[index]) is { } target) leaders.Add(target);
                if (Target(Ops[index]) is not null || Ops[index].StartsWith(".ret")) leaders.Add(index + 1);
            }
            return leaders.Where(leader => leader <= pc).Max();
        }

        /// <summary>An operation that steps without a branch, a call, a fault or memory: arithmetic, conversions
        /// and the bit counts, which are total.</summary>
        internal static bool Pure(string op) => Regex.IsMatch(op,
            @"\A\.(arg \d+|const32 \S.*|const64 \S.*|add|sub|mul|band|bor|bxor|nop|ret|convI8|convU8|convU4|" +
            @"convI4)\z") ||
            Regex.IsMatch(op, @"\A\.intrinsic \(\.scalar \(\.(log2|popCount|leadingZeroCount|trailingZeroCount) " +
                @"\d+ \.word(32|64)\)\) 1\z");
    }

    enum Part { Word, Field, Span, Object }

    /// <summary>One value of the loop state: a numeric local, a struct field, a span's suffix or an object
    /// reference local.</summary>
    sealed record Component(string Name, Part Part, int Width, int Slot, int Offset, Parameter? Span);

    /// <summary>A frame slot: a local's home, or a span parameter's home. A parameter's span slot holds the
    /// argument on entry, so the entry frame names it; a span local's holds nothing until it is assigned.
    /// </summary>
    sealed record Slot(int Index, string Kind, string? Home, int Layout, Component[] Components,
        bool Argument = false);

    abstract record Value;
    /// <summary>A word the outline names by `Term`; `Stacked` is its stack entry when the step leaves it in a
    /// form other than `Term`, which a test reads simplified.</summary>
    sealed record Number(string Term, int Width, bool Literal = false, bool Narrow = false, string? Stacked = null)
        : Value;
    sealed record Unknown(string What) : Value;
    sealed record LocalValue(int Slot) : Value;
    sealed record LocalAddress(int Slot) : Value;
    sealed record Element(int Component) : Value;
    sealed record SpanLength(int Component) : Value;
    sealed record Sliced(int Component) : Value;
    sealed record ReferenceArgument(string Name) : Value;
    sealed record ObjectTerm(string Term) : Value;
    /// <summary>An array argument, destructured into its base and length before the loop.</summary>
    sealed record WordArrayArgument(Parameter Array) : Value;
    /// <summary>The 64-bit length `ldlen` pushes for an array argument.</summary>
    sealed record ArrayLength(Parameter Array) : Value;
    /// <summary>A span argument, which a span local copies before the loop.</summary>
    sealed record SpanArgument(Parameter Span) : Value;
    /// <summary>The span over a whole array argument that a span local holds before the loop.</summary>
    sealed record SpannedArray(Parameter Array) : Value;
    /// <summary>`Unsafe.Add` of a reference argument and a word index, scaled by `Width` bytes.</summary>
    sealed record AddedReference(string Base, string Index, int Width) : Value;

    /// <summary>A span's suffix at a point of a path: its view, remaining elements and checked fact. A
    /// Written span's remaining part is its length, and its fact a `WritableSpan`.</summary>
    sealed record SpanTerm(string View, string Remaining, string Checked, bool Caseable, string? Head = null,
        string? Tail = null, bool Written = false);

    /// <summary>One point of a symbolic path: where it is, its stack and loop state, and the case-split
    /// facts the tactics need, with the pc at which the proof goal currently stands.</summary>
    sealed class PathState
    {
        internal int Pc;
        internal int GoalPc;
        internal List<Value> Stack = [];
        internal object[] State = [];
        internal List<string> Facts = [];
        internal bool Called;
        // A store replaces the head's memory, at which liveness and write authority are asked.
        internal bool Moved;
        internal HashSet<string> Obtained = [];

        internal PathState Copy() => new()
        {
            Pc = Pc, GoalPc = GoalPc, Stack = [.. Stack], State = [.. State], Facts = [.. Facts],
            Called = Called, Moved = Moved, Obtained = [.. Obtained]
        };
    }

    /// <summary>What an evaluated operation does to the walk.</summary>
    enum Event { Continue, Branch, Call, Return, Stop }

    sealed class LoopOutline(Extraction extraction, Specification spec, Body body,
        IReadOnlyList<(int Head, int Latch)> loops, Names names)
    {
        // The loop a walk is in; a path leaving it for the next loop's head chains into that loop.
        int active;
        (int Head, int Latch) loop => loops[active];

        /// <summary>The suffix of the names bound for loop `index`: none for the first, its ordinal after.</summary>
        static string Suffix(int index) =>
            index == 0 ? "" : (index + 1).ToString(System.Globalization.CultureInfo.InvariantCulture);

        readonly MethodDefinition method = extraction.Methods[0];
        readonly FieldViews views = new(extraction);
        readonly List<Slot> slots = [];
        readonly List<Component> components = [];
        readonly Dictionary<int, string> callees = [];
        int branches;
        string stopReason = "";

        internal string Emit(Writer lean)
        {
            Frame();
            Callees();
            var imports = new List<string> { "CIL.Verification", "CIL.StructuralLabels" };
            if (callees.Count > 0) imports.Add("CIL.MethodIdentity");
            imports.Add("CIL.Safety.LoopScaffold");
            if (body.Ops.Any(op => op.StartsWith(".memory (.add ", StringComparison.Ordinal)) &&
                spec.Parameters.Any(parameter => parameter.Shape == ParameterShape.Reference) ||
                callees.Keys.Any(index => Branches(extraction, index)) || Indexed.Any())
                imports.Add("CIL.Safety.LoopObligations");
            if (spec.Framed) imports.Add("CIL.Safety.ObjectFields");
            if (spec.Parameters.Any(parameter => parameter.Writable)) imports.Add("CIL.Safety.SpanWrites");
            else if (SpanParameters.Any()) imports.Add("CIL.Safety.SpanContents");
            if (WordArrays.Any()) imports.Add("CIL.Safety.ArrayContents");
            Header(lean, spec, imports, "`invariant`, `measure`, `postcondition` and `precondition` (at a call)");
            foreach (var index in callees.Keys.Order()) Contract(lean, index);
            spec.NonNull = [.. Indexed];
            spec.Placeholders(lean);
            Entry(lean);
            StateAndHeader(lean);
            spec.Statement(lean);
            Proof(lean);
            Footer(lean);
            return lean.ToString();
        }

        string Memory => spec.Symbolic ? "memory" : "Memory.empty";
        string[] Homes => slots.Where(slot => slot.Home is not null).Select(slot => slot.Home!).ToArray();
        IEnumerable<Parameter> SpanParameters => spec.Parameters.Where(p => p.Shape == ParameterShape.Span);
        IEnumerable<Parameter> WordArrays => spec.Parameters.Where(p => p.Shape == ParameterShape.WordArray);

        // WordArrays a span local spans whole; the loop reaches them through the span, never by index.
        readonly List<Parameter> spanned = [];

        /// <summary>The array arguments the loop indexes, destructured into a base and a length.</summary>
        IEnumerable<Parameter> Indexed => WordArrays.Except(spanned);

        /// <summary>An array argument as the proof writes it once destructured: addressed, at its length.</summary>
        static string Destructured(Parameter array) =>
            $"⟨.address {array.Name}Base, {array.Name}Length, {array.ArrayElement}⟩";

        /// <summary>The theorem's arguments as the proof names them after the arrays are destructured.</summary>
        string Arguments => string.Join(" ", spec.Binders.Select(binder =>
            Indexed.FirstOrDefault(array => array.Name == binder.Name) is { } array
                ? Destructured(array) : binder.Name));

        /// <summary>Close a side condition of an array access from the author's definitions, with the steps that
        /// reduce a destructured array's storage span and footprint.</summary>
        void ArrayObligation(Writer lean, string indent)
        {
            lean.Line($"{indent}  cil_loop_obligation [invariant, Precondition, {(Writes ? "footprint, " : "")}" +
                "ArrayView.storage,");
            var footprint = Indexed.Any(array => array.Writable) ? "SpanView.footprint, " : "";
            lean.Line($"{indent}    {footprint}ManagedReference.address.injEq, forall_eq', CIL.ArrayElement.width]");
        }

        string Location(int pc) => ProofOutline.Location(method, pc);

        void Frame()
        {
            var metadata = extraction.Emitted[0].Metadata;
            var kinds = Items(Regex.Match(metadata, @"localKinds := \[(.*?)\], opaqueVectorLocals").Groups[1].Value);
            var homeList = Regex.Match(metadata, @"parameterHomes := \[(.*?)\], staticSites").Groups[1].Value;
            var homes = Regex.Matches(homeList, @"\((\d+), ([^)]*)\)")
                .Select(match => (Index: int.Parse(match.Groups[1].Value), Kind: match.Groups[2].Value));
            var localNames = method.Body.Variables.Select(variable =>
                method.DebugInformation.TryGetName(variable, out var name) ? name : null).ToArray();
            for (var index = 0; index < kinds.Length; index++)
            {
                var kind = kinds[index];
                var name = names.Claim(localNames[index], "local" + index);
                var home = $"home{index}";
                if (Regex.Match(kind, @"\A\.word(32|64)\z") is { Success: true } word)
                {
                    var width = word.Groups[1].Value == "64" ? 8 : 4;
                    Add(new(index, kind, home, -1, [new(name, Part.Word, width, index, 0, null)]));
                }
                else if (Regex.Match(kind, @"\A\.aggregate (\d+)\z").Success)
                    Add(Aggregate(index, kind, home, name));
                else if (kind == ".object")
                    Add(new(index, kind, null, -1, [new(name, Part.Object, 8, index, 0, null)]));
                else if (kind.StartsWith(".span ", StringComparison.Ordinal))
                {
                    var source = SpanSource(index, kind, name);
                    Add(new(index, kind, null, -1, [new(name, Part.Span, source.Width, index, 0, source)]));
                }
                else throw Unsupported($"local `{name}` has kind {kind}");
            }
            foreach (var (argument, kind) in homes)
            {
                var parameter = spec.Parameters[argument];
                if (parameter.Shape != ParameterShape.Span || kind != SpanKind(parameter))
                    throw Unsupported($"parameter `{parameter.Name}` is assigned or addressed in the body; new-proof " +
                        "follows reassigned span parameters only");
                if (components.Any(component => component.Span == parameter))
                    throw Unsupported($"span parameter `{parameter.Name}` is both reassigned and copied to a local");
                Add(new(slots.Count, kind, null, -1,
                    [new(parameter.Name, Part.Span, parameter.Width, slots.Count, 0, parameter)], Argument: true));
            }
            if (components.Count == 0) throw Unsupported("its loop keeps no state in locals");
        }

        static string SpanKind(Parameter span) => $".span {span.Width} {(span.Writable ? "true" : "false")}";

        /// <summary>The argument a span local is assigned once, before its loop, from: a span argument it copies or
        /// an array argument it spans whole. Its other stores are the loop's `Slice(1)` of itself.</summary>
        Parameter SpanSource(int local, string kind, string name)
        {
            var ops = body.Ops;
            var stores = Enumerable.Range(1, ops.Length - 1).Where(pc => ops[pc] == $".setLocal {local}" &&
                ops[pc - 1] != ".memory (.spanSlice false)").ToArray();
            var refused = Unsupported($"span local `{name}` is not assigned once from a span argument or from the " +
                "whole of an array argument");
            if (stores.Length != 1 || stores[0] >= loops[0].Head) throw refused;
            var store = stores[0];
            Parameter Argument(int pc) => Regex.Match(ops[pc], @"\A\.arg (\d+)\z") is { Success: true } match
                ? spec.Parameters[int.Parse(match.Groups[1].Value)] : throw refused;
            Parameter source;
            if (Regex.IsMatch(ops[store - 1], @"\A\.arg \d+\z"))
                source = Argument(store - 1);
            else if (store >= 2 && Argument(store - 2) is { Shape: ParameterShape.WordArray } array &&
                ops[store - 1] ==
                    $".memory (.arraySpan {array.ArrayElement} {(array.Writable ? "true" : "false")} .whole)")
                source = array;
            else throw refused;
            if (source.Shape is not (ParameterShape.Span or ParameterShape.WordArray) || kind != SpanKind(source))
                throw refused;
            if (components.Any(component => component.Span == source))
                throw Unsupported($"span local `{name}` copies an argument another span local holds");
            if (source.Shape == ParameterShape.WordArray)
            {
                // An array read other than through the span is indexed, which a spanned array is not destructured for.
                var argument = $".arg {Array.IndexOf(spec.Parameters, source)}";
                if (Enumerable.Range(0, ops.Length).Any(pc => ops[pc] == argument && pc != store - 2))
                    throw Unsupported($"array `{source.Name}` is both spanned by `{name}` and read directly");
                spanned.Add(source);
            }
            return source;
        }

        void Add(Slot slot)
        {
            slots.Add(slot);
            components.AddRange(slot.Components);
        }

        Slot Aggregate(int index, string kind, string home, string name)
        {
            var type = method.Body.Variables[index].VariableType;
            var layout = Array.IndexOf(extraction.LayoutIdentities, LayoutEvidence.Identity(type));
            var definition = Regex.Match(Source, $@"^def layout{layout} : AggregateLayout := ⟨\d+, \[(.*)\]⟩\r?$",
                RegexOptions.Multiline);
            if (layout < 0 || !definition.Success) throw Unsupported($"no layout for local `{name}`");
            var fields = Regex.Matches(definition.Groups[1].Value, @"⟨(\d+), (\d+), (true|false)⟩").ToArray();
            var named = type.Resolve()?.Fields.Where(field => !field.IsStatic).ToArray() ?? [];
            if (fields.Any(field => field.Groups[3].Value == "true") || named.Length != fields.Length)
                throw Unsupported($"struct local `{name}` nests a struct");
            return new(index, kind, home, layout, fields.Select((field, position) =>
            {
                var fieldName = named[position].Name;
                var component = names.Claim(name + char.ToUpperInvariant(fieldName[0]) + fieldName[1..],
                    $"{name}Field{position}");
                return new Component(component, Part.Field, int.Parse(field.Groups[2].Value), index,
                    int.Parse(field.Groups[1].Value), null);
            }).ToArray());
        }

        string Source => extraction.Source;

        static string[] Items(string list)
        {
            var items = new List<string>();
            var depth = 0;
            var start = 0;
            for (var index = 0; index < list.Length; index++)
            {
                if (list[index] is '(' or '[' or '⟨') depth++;
                else if (list[index] is ')' or ']' or '⟩') depth--;
                else if (list[index] == ',' && depth == 0)
                {
                    items.Add(list[start..index].Trim());
                    start = index + 1;
                }
            }
            if (list.Trim().Length > 0) items.Add(list[start..].Trim());
            return [.. items];
        }

        // Callees are named for their methods so a reader can match each contract to its call.
        void Callees()
        {
            foreach (var op in body.Ops)
                if (Regex.Match(op, @"\A\.call(?:Instance)? (\d+) \d+\z") is { Success: true } call)
                {
                    var index = int.Parse(call.Groups[1].Value);
                    if (callees.ContainsKey(index)) continue;
                    var callee = extraction.Methods[index];
                    callees[index] = names.Claim(char.ToLowerInvariant(callee.Name[0]) + callee.Name[1..],
                        "callee" + index);
                }
        }

        // A product type, parenthesized only when it has several factors.
        static string Product(IEnumerable<string> factors)
        {
            var all = factors.ToArray();
            return all.Length == 1 && !all[0].Contains(' ') ? all[0] : "(" + string.Join(" × ", all) + ")";
        }

        static string Projection(string root, int index, int count) =>
            count == 1 ? root : root + string.Concat(Enumerable.Repeat(".2", index)) + (index == count - 1 ? "" : ".1");

        string ValuesType => Product(components.Select(component => component.Part switch
        {
            Part.Span => component.Span!.Writable ? $"WritableSuffix {Memory} written {component.Width}"
                : $"SpanSuffix {Memory} {component.Width} false",
            Part.Object => "ManagedReference",
            _ => WordType(component.Width)
        }));

        void Contract(Writer lean, int index)
        {
            var callee = extraction.Methods[index];
            var name = callees[index];
            var receiver = callee.DeclaringType.Name;
            var declared = (callee.HasThis
                ? new[]
                {
                    (Name: char.ToLowerInvariant(receiver[0]) + receiver[1..], Type: (TypeReference)callee.DeclaringType)
                }
                : []).Concat(callee.Parameters.Select(parameter => (parameter.Name, Type: parameter.ParameterType)))
                .ToArray();
            var inputs = declared.Select(parameter => parameter.Type switch
            {
                ByReferenceType reference when ElementWidth(reference.ElementType) is { } width =>
                    (Type: "Reference", Width: width, Reference: true, Object: (TypeReference?)null, Span: false),
                var type when WrittenSpanWidth(type) is { } width =>
                    (Type: "SpanView", Width: width, Reference: false, Object: null, Span: true),
                var type when ElementWidth(type) is { } width =>
                    (Type: WordType(width), Width: width, Reference: false, Object: null, Span: false),
                var type when ObjectTypes.Is(type) =>
                    (Type: "Reference", Width: 8, Reference: false, Object: type, Span: false),
                var type => throw Unsupported($"callee {callee.Name} takes {type.FullName}")
            }).ToArray();
            var output = callee.ReturnType.FullName == "System.Void" ? (int?)null : ElementWidth(callee.ReturnType)
                ?? throw Unsupported($"callee {callee.Name} returns {callee.ReturnType.FullName}");
            var binding = $"bind_callee {name} {name}Body := ";
            lean.Line(binding + Quoted(callee.FullName, binding.Length));
            lean.Line("  from Extracted.method0");
            lean.Line();
            // An object callee whose body the outline reads gets the contract that body meets, proved.
            if (inputs.Any(input => input.Object is not null) && Summarize(extraction, index, name, views) is { } read)
            {
                CalleeContract(lean, read, name);
                return;
            }
            var single = inputs.Length == 1 ? Variable(declared[0].Name) : "input";
            string Input(int position) => inputs.Length == 1 ? single : Projection("input", position, inputs.Length);
            var inputType = inputs.Length == 0 ? "Unit" : Product(inputs.Select(input => input.Type));
            var outputType = output is { } width ? WordType(width) : "Unit";
            var store = Stores(index);
            var spanStore = SpanStores(extraction, index);
            if (store is not null)
            {
                lean.Line($"/-- `{callee.Name}` stores its argument through its reference, given write authority over");
                lean.Line("    the element, and touches nothing else: the contract its body meets. -/");
            }
            else if (spanStore is not null)
            {
                lean.Line($"/-- `{callee.Name}` stores its argument into the first element of a nonempty");
                lean.Line("    writable span, and touches nothing outside the span's bytes: the contract its body");
                lean.Line("    meets. -/");
            }
            else
            {
                lean.Line($"/-- `{callee.Name}` at its calls from the loop: replace `pre` and `post`, and widen");
                lean.Line("    `footprint` if it changes more of the caller's memory. -/");
            }
            lean.Line($"def {name}Contract : MethodContract {inputType} {outputType} where");
            var arguments = string.Join(", ", inputs.Select((input, position) =>
                input.Reference ? $".reference (.address {Input(position)})"
                : input.Span ? $".bufferSpan {Input(position)}"
                : input.Object is not null ? $".object (.address {Input(position)})"
                : $".scalar ({ScalarConstructor(input.Width)} {Input(position)})"));
            lean.Line($"  args {(inputs.Length == 0 ? "_" : single)} := [{arguments}]");
            lean.Line(output is { } returned ? $"  results result := [.scalar ({ScalarConstructor(returned)} result)]"
                : "  results _ := []");
            lean.Line(store is { } stored
                ? $"  pre {single} memory := Writable memory {Input(stored.Slot)} {stored.Width} 0 1"
                : spanStore is { } lent
                    ? $"  pre {single} memory := ∃ rest, WritableSpan memory {Input(0)}.footprint {Input(0)} " +
                        $"{lent.Width} (rest + 1)"
                : "  pre _ _ := sorry");
            var entries = string.Join(", ", inputs.SelectMany((input, position) =>
                input.Reference ? [$"({Input(position)}, {input.Width})"]
                : input.Object is { } type ? views.Of(type).Where(field => field.Stored)
                    .Select(field => $"{field.Lean}.entry {Input(position)}")
                : Enumerable.Empty<string>()));
            // A span argument may be written anywhere in its bytes.
            var footprint = (entries.Length == 0 ? [] : new[] { $"[{entries}]" }).Concat(inputs
                .Select((input, position) => input.Span ? $"{Input(position)}.footprint" : null).OfType<string>())
                .ToArray();
            lean.Line(footprint.Length == 0 ? "  footprint _ := []"
                : $"  footprint {single} := {string.Join(" ++ ", footprint)}");
            if (spanStore is { } filled)
            {
                lean.Line($"  post {single} _ final _ := ∀ base, {Input(0)}.reference = .address base →");
                lean.Line($"    Contents final base {filled.Width} [{Input(1)}]");
            }
            else
                lean.Line(store is { } written
                    ? $"  post {single} _ final _ := Contents final {Input(written.Slot)} {written.Width} " +
                        $"[{Input(written.Value)}]"
                    : "  post _ _ _ _ := sorry");
            lean.Line();
            var steppable = output is not null &&
                inputs.All(input => !input.Reference && !input.Span && input.Object is null) &&
                extraction.Emitted[index].Metadata.Contains("locals := [],") &&
                extraction.Emitted[index].Ops.All(Body.Pure);
            var pattern = inputs.Length switch
            {
                0 => "-",
                1 => single,
                _ => "⟨" + string.Join(", ", declared.Select(parameter => Variable(parameter.Name))) + "⟩"
            };
            lean.Line($"/-- `{callee.Name}` meets its contract; the loop proof uses only the contract. -/");
            lean.Line($"theorem {name}_holds : {name}Contract.Holds Extracted.program {name} := by");
            if (steppable)
            {
                lean.Line($"  rintro {pattern} memory permitted");
                ContractEvidence.Returns(lean, "  ", "");
                lean.Line("  case run => cil_checked_steps");
                lean.Noted("  ", "case postcondition => sorry", $"{name}Contract.post of the returned value");
            }
            else if (store is { } body)
            {
                var value = Variable(declared[body.Value].Name);
                lean.Line($"  rintro {pattern} memory writable");
                lean.Line($"  dsimp only [{name}Contract] at writable");
                lean.Line($"  obtain ⟨after, wrote, formed, confined, filled⟩ := writable.write_one {value}");
                lean.Line("  refine MethodContract.Holds.intro after () ?_ confined filled");
                lean.Line($"  cil_checked_steps [{StoreLemma(body.Op)} wrote, formed]");
            }
            else if (spanStore is { } spanBody)
                SpanStoreContract(lean, index, name, pattern, Variable(declared[1].Name), spanBody.Op);
            else if (Branches(extraction, index))
            {
                lean.Line($"  rintro {pattern} memory permitted");
                var sides = 0;
                BranchedCallee(lean, extraction, index, name,
                    declared.Select(parameter => Variable(parameter.Name)).ToArray(), 0, [], [], "  ",
                    ref sides, kept: false);
            }
            else
            {
                var reason = inputs.Any(input => input.Reference) ? "it writes through a reference"
                    : inputs.Any(input => input.Span) ? "it writes through a span"
                    : inputs.Any(input => input.Object is not null) ? "it takes an object, whose fields need facts"
                    : output is null ? "it returns nothing to state"
                    : !extraction.Emitted[index].Metadata.Contains("locals := [],") ? "it has locals"
                    : Unstepped(callee, extraction.Emitted[index].Ops, []);
                lean.Noted("  ", "sorry", $"{NotOutlined}{callee.Name}'s body against the contract, since " +
                    reason);
            }
            lean.Line();
        }

        /// <summary>The reference and value parameters, width and store of a static callee whose body only
        /// stores one word argument through one reference argument of that word's width.</summary>
        (int Slot, int Value, int Width, string Op)? Stores(int index)
        {
            var callee = extraction.Methods[index];
            var ops = extraction.Emitted[index].Ops.Where(op => op != ".nop").ToArray();
            if (callee.HasThis || callee.ReturnType.FullName != "System.Void" || ops.Length != 4 ||
                !extraction.Emitted[index].Metadata.Contains("locals := [],") || ops[3] != ".ret") return null;
            var slot = Regex.Match(ops[0], @"\A\.arg (\d+)\z");
            var value = Regex.Match(ops[1], @"\A\.arg (\d+)\z");
            if (!slot.Success || !value.Success) return null;
            var (reference, word) = (int.Parse(slot.Groups[1].Value), int.Parse(value.Groups[1].Value));
            if (callee.Parameters[reference].ParameterType is not ByReferenceType target ||
                ElementWidth(target.ElementType) is not { } width ||
                ElementWidth(callee.Parameters[word].ParameterType) != width) return null;
            var stores = width == 4 ? ops[2] == ".storeScalar 4" : ops[2] is ".store64" or ".storeScalar 8";
            return stores ? (reference, word, width, ops[2]) : null;
        }

        /// <summary>Whether a callee of words with no locals tests its arguments and returns a word or throws on
        /// each side, so its contract proof splits on each test and steps every returning side.</summary>
        internal static bool Branches(Extraction extraction, int index)
        {
            var callee = extraction.Methods[index];
            var ops = extraction.Emitted[index].Ops;
            return !callee.HasThis &&
                callee.Parameters.All(parameter => ElementWidth(parameter.ParameterType) is not null) &&
                callee.ReturnType.FullName != "System.Void" && ElementWidth(callee.ReturnType) is not null &&
                extraction.Emitted[index].Metadata.Contains("locals := [],") &&
                ops.Any(op => Body.Conditional(op) || op.StartsWith(".throw ", StringComparison.Ordinal)) &&
                ops.All(op =>
                    Regex.IsMatch(op, @"\A\.(arg \d+|const(32|64) \S.*|add|sub|mul|band|bor|bxor|nop|ret)\z") ||
                    Body.Target(op) is not null || op.StartsWith(".throw ", StringComparison.Ordinal));
        }

        /// <summary>The contract proof of a branching callee from `pc`: a `by_cases` on each test, each returning
        /// side stepped with the tests' facts, and each throwing side closed from the precondition. A `kept`
        /// contract's `post` first states that the memory is as it was, which each returning side proves.
        /// </summary>
        internal static void BranchedCallee(Writer lean, Extraction extraction, int index, string name,
            string[] arguments, int pc, List<(string Term, int Bits)> stack, List<(string Fact, string Text)> facts,
            string indent, ref int sides, bool kept)
        {
            var callee = extraction.Methods[index];
            var ops = extraction.Emitted[index].Ops;
            string Where() => facts.Count == 0 ? "" : " where " + string.Join(" and ", facts.Select(fact => fact.Text));
            while (true)
            {
                var op = ops[pc];
                Match match;
                if ((match = Regex.Match(op, @"\A\.arg (\d+)\z")).Success)
                {
                    var argument = int.Parse(match.Groups[1].Value);
                    var bits = 8 * ElementWidth(callee.Parameters[argument].ParameterType)!.Value;
                    stack.Add((arguments[argument], bits));
                }
                else if ((match = Regex.Match(op, @"\A\.const(32|64) (.+)\z")).Success)
                    stack.Add((match.Groups[2].Value, int.Parse(match.Groups[1].Value)));
                else if ((match = Regex.Match(op, @"\A\.(add|sub|mul|band|bor|bxor)\z")).Success)
                {
                    var right = stack[^1];
                    var left = stack[^2];
                    stack.RemoveRange(stack.Count - 2, 2);
                    var symbol = match.Groups[1].Value switch
                    {
                        "add" => "+", "sub" => "-", "mul" => "*", "band" => "&&&", "bor" => "|||", _ => "^^^"
                    };
                    stack.Add(($"({left.Term} {symbol} {right.Term})", left.Bits));
                }
                else if (op == ".ret")
                {
                    var suffix = (++sides).ToString(System.Globalization.CultureInfo.InvariantCulture);
                    var steps = facts.Count == 0 ? "" : $" [{string.Join(", ", facts.Select(fact => fact.Fact))}]";
                    ContractEvidence.Returns(lean, indent, suffix);
                    lean.Line($"{indent}case run{suffix} => cil_checked_steps{steps}");
                    if (kept) KeptPost(lean, indent, name, suffix, Where());
                    else lean.Noted(indent, $"case postcondition{suffix} => sorry",
                        $"{name}Contract.post of the returned value{Where()}");
                    return;
                }
                else if (op.StartsWith(".throw ", StringComparison.Ordinal))
                {
                    lean.Comment($"{indent}-- ", $"{indent}-- ", $"`{callee.Name}` throws at " +
                        $"{ProofOutline.Location(callee, pc)}{Where()}, which its precondition must rule out");
                    lean.Line($"{indent}exfalso");
                    lean.Line($"{indent}cil_loop_obligation [{name}Contract]");
                    return;
                }
                else if (Body.Target(op) is { } target && !Body.Conditional(op))
                {
                    pc = target;
                    continue;
                }
                else if (Body.Conditional(op))
                {
                    var taken = Body.Target(op)!.Value;
                    var opName = Regex.Match(op, @"\A\.(\w+)").Groups[1].Value;
                    var arity = opName is "brzero" or "brnonzero" ? 1 : 2;
                    var operands = stack.TakeLast(arity).ToArray();
                    var rest = stack.Take(stack.Count - arity).ToList();
                    var (condition, takenWhenTrue) = Body.Test(opName, [.. operands.Select(operand => operand.Term)],
                        operands[0].Bits);
                    var fact = $"branch{facts.Count + 1}";
                    lean.Line($"{indent}by_cases {fact} : {condition}");
                    foreach (var holds in new[] { true, false })
                    {
                        var next = holds == takenWhenTrue ? taken : pc + 1;
                        var text = holds ? $"`{condition}`" : $"not `{condition}`";
                        lean.Line($"{indent}· -- {text}");
                        BranchedCallee(lean, extraction, index, name, arguments, next, [.. rest],
                            [.. facts, (fact, text)], indent + "  ", ref sides, kept);
                    }
                    return;
                }
                pc++;
            }
        }

        static string Variable(string name) => Regex.IsMatch(name, @"\A[A-Za-z][A-Za-z0-9_]*\z") &&
            !Reserved.Contains(name) ? name : "argument";

        // A long signature literal continues on the next line through a Lean string gap.
        static string Quoted(string text, int column)
        {
            const int Room = 96;
            if (column + text.Length + 2 <= Room) return $"\"{text}\"";
            var cut = text.LastIndexOf(',', Math.Min(text.Length - 1, Room - column - 3));
            if (cut < 0) cut = text.IndexOf('(');
            return $"\"{text[..(cut + 1)]}\\\n    {text[(cut + 1)..]}\"";
        }

        IEnumerable<(string Name, string Type)> EntryBinders =>
            (spec.Symbolic ? new[] { ("memory", "Memory") } : [])
            .Concat(spec.Parameters.Select(parameter => (parameter.Name, parameter.Lean)))
            .Concat(spec.Symbolic ? [("wellFormed", "memory.WellFormed")] : [])
            .Concat(SpanParameters.SelectMany(parameter => new[]
            {
                (parameter.Name + "Valid", $"{parameter.Name}.validate memory = .ok ()"),
                (parameter.Name + "Width", $"{parameter.Name}.width = {parameter.Width}"),
                (parameter.Mode, parameter.ModeStatement)
            }))
            .Concat(WordArrays.Select(array => (array.Name + "Valid", $"{array.Name}.validate memory = .ok ()")));

        void Entry(Writer lean)
        {
            var binders = EntryBinders.Select(binder => (binder.Name, binder.Type)).ToArray();
            var grouped = spec.Symbolic ? binders.Select(binder => $"({binder.Name} : {binder.Type})")
                : Grouped(binders);
            lean.Wrapped("bind_entry entry", grouped, ":= Extracted.method0");
            lean.Line($"  with {spec.ArgumentValues} from {(spec.Symbolic ? "memory" : "Memory.empty")}");
            lean.Line(spec.Symbolic ? "  allocating wellFormed" : "  allocating Memory.empty_wellFormed");
            var facts = SpanParameters.SelectMany(parameter => new[]
                { parameter.Name + "Valid", parameter.Name + "Width", parameter.Mode })
                .Concat(WordArrays.Select(array => array.Name + "Valid")).ToArray();
            if (facts.Length > 0) lean.Line($"  simplifying [{string.Join(", ", facts)}]");
            for (var index = 0; index < loops.Count; index++)
                lean.Line($"bind_loop loop{Suffix(index)} := Extracted.method0" +
                    (loops.Count > 1 ? $" [{index}]" : ""));
            lean.Line();
        }

        // A method handed a reference or an object may write caller memory, so its frame keeps a named footprint.
        bool Writes => spec.Framed || spec.Parameters.Any(parameter => parameter.Shape == ParameterShape.Reference) ||
            spec.Parameters.Any(parameter => parameter.Writable);
        const string Footprint = "List (Reference × Nat)";

        string StateBinders => string.Join(" ", (spec.Symbolic ? new[] { "(memory : Memory)" } : [])
            .Concat(Writes ? [$"(written : {Footprint})"] : [])
            .Concat(Homes.Length > 0 ? [$"({string.Join(" ", Homes)} : Reference)"] : []));

        string StateArguments(string memory) =>
            string.Join(" ", (spec.Symbolic ? new[] { memory } : []).Concat(Writes ? ["written"] : []).Concat(Homes));

        string StateType(string memory) => StateArguments(memory) is { Length: > 0 } arguments
            ? $"State {arguments}" : "State";

        string FrameArguments(Func<Component, string> view, string memory) =>
            string.Join(" ", (spec.Symbolic ? new[] { memory } : [])
                .Concat(components.Where(component => slots[component.Slot].Argument).Select(view)).Concat(Homes));

        List<string>[] headerParameters = [];

        /// <summary>Each slot's frame entry at the loop head, from the state values at `root`.</summary>
        string[] SlotTerms(string root) => slots.Select(slot => slot.Home is { } home
            ? $".bytes {(slot.Kind.Contains(' ') ? $"({slot.Kind})" : slot.Kind)} {home}"
            : slot.Components[0].Part == Part.Object
            ? $".object (some {Projection(root, components.IndexOf(slot.Components[0]), components.Count)})"
            : $"{slot.Kind} " +
                $"(some {Projection(root, components.IndexOf(slot.Components[0]), components.Count)}.view)")
            .ToArray();

        void StateAndHeader(Writer lean)
        {
            if (Writes) spec.Footprint(lean);
            var described = string.Join(", ", components.Select(component => component.Part != Part.Span
                ? $"`{component.Name}`"
                : $"the {(component.Span!.Writable ? "unwritten" : "unread")} suffix of `{component.Name}`"));
            lean.Doc($"The loop's locals at its head: {described}.");
            lean.Line($"abbrev State{(StateBinders.Length > 0 ? " " + StateBinders : "")} :=");
            var project = (Component component) =>
                Projection("values", components.IndexOf(component), components.Count);
            var slotTerms = SlotTerms("values");
            var remembered = slots.Select(slot => slot.Components[0].Part switch
            {
                Part.Word => $"some ({ScalarConstructor(slot.Components[0].Width)} {project(slot.Components[0])})",
                Part.Field => $"some (.aggregate (Extracted.layout{slot.Layout}.encode [" + string.Join(", ",
                    slot.Components.Select(field => $"{ScalarConstructor(field.Width)} {project(field)}")) + "]))",
                _ => "none"
            }).ToArray();
            var kinds = string.Join(", ", slots.Select(slot => slot.Kind));
            lean.Wrapped($"  FrameState {(Writes ? "written" : "[]")} {Memory}", [$"[{kinds}]", ValuesType], "");
            var slotsUse = slotTerms.Any(term => term.Contains("values")) ? "values" : "_";
            var knownUse = remembered.Any(term => term.Contains("values")) ? "values" : "_";
            var slotsLine = $"    (fun {slotsUse} => [{string.Join(", ", slotTerms)}])";
            var knownLine = $"fun {knownUse} => [{string.Join(", ", remembered)}]";
            if (slotsLine.Length + 1 + knownLine.Length <= 100) lean.Line(slotsLine + " " + knownLine);
            else
            {
                lean.Line(slotsLine);
                lean.Line("    " + knownLine);
            }
            lean.Line();
            headerParameters = new List<string>[loops.Count];
            for (active = 0; active < loops.Count; active++) LoopHeader(lean);
            active = 0;
        }

        /// <summary>The cutpoint, invariant and measure of the active loop.</summary>
        void LoopHeader(Writer lean)
        {
            var suffix = Suffix(active);
            var latchOp = body.Ops[loop.Latch];
            var opName = Regex.Match(latchOp, @"\A\.(\w+)").Groups[1].Value;
            if (!Body.Conditional(latchOp))
                throw Unsupported($"its loop at {Location(loop.Latch)} does not test a condition at its back edge");
            string Projected(Component component) =>
                Projection("state.values", components.IndexOf(component), components.Count);
            var state = Initial(component => component.Part switch
            {
                Part.Span => new SpanTerm(Projected(component) + ".view", "", "", false),
                Part.Object => new ObjectTerm(Projected(component)),
                _ => new Number(Projected(component), component.Width)
            });
            var operands = Guard(state);
            var stack = operands.AsEnumerable().Reverse().Select(operand => StackValue(operand, state)).ToArray();
            // A destructured array reaches the head only through its length.
            var candidates = spec.Parameters.Select(parameter => Indexed.Contains(parameter)
                ? (Name: parameter.Name + "Length", Lean: "Nat") : (parameter.Name, parameter.Lean)).ToArray();
            headerParameters[active] = candidates.Where(candidate => stack.Any(item =>
                Regex.IsMatch(item, $@"(?<![.\w]){candidate.Name}\b"))).Select(candidate => candidate.Name).ToList();
            var binders = (spec.Symbolic ? new[] { "(memory : Memory)" } : [])
                .Concat(Grouped(candidates.Where(candidate => headerParameters[active].Contains(candidate.Name))))
                .Concat(Writes ? [$"(written : {Footprint})"] : [])
                .Concat(Homes.Length > 0 ? [$"({string.Join(" ", Homes)} : Reference)"] : [])
                .Append($"(state : {StateType("memory")})");
            lean.Line($"-- The cutpoint is the loop's back-edge test at {Location(loop.Latch)}.");
            lean.Wrapped($"bind_cutpoint header{suffix}", binders, ":=");
            lean.Line($"  Extracted.method0 at loop{suffix}.latch matching (· matches .{opName} _)");
            var frame = FrameArguments(component =>
                Projection("state.values", components.IndexOf(component), components.Count) + ".view", "memory");
            var entryFrame = $"entry.frame{(frame.Length > 0 ? " " + frame : "")}";
            // An object or span local's slot changes with each store, so the head names every slot from the state.
            if (slots.Any(slot => slot.Components[0].Part == Part.Object ||
                slot.Components[0].Part == Part.Span && !slot.Argument))
            {
                lean.Line($"  with {{ {entryFrame} with");
                lean.Line($"      locals := [{string.Join(", ", SlotTerms("state.values"))}] }},");
                lean.Wrapped("   ", [$"[{string.Join(", ", stack)}],", "state.memory"], "");
            }
            else lean.Wrapped($"  with {entryFrame},", [$"[{string.Join(", ", stack)}],", "state.memory"], "");
            lean.Line();
            var implicitBinders = string.Join(" ", (spec.Symbolic ? new[] { "{memory : Memory}" } : [])
                .Concat(Writes ? [$"{{written : {Footprint}}}"] : [])
                .Concat(Homes.Length > 0 ? [$"{{{string.Join(" ", Homes)} : Reference}}"] : []));
            var explicitBinders = Grouped(spec.Binders).ToList();
            if (implicitBinders.Length > 0) explicitBinders.Add(implicitBinders);
            explicitBinders.Add($"(state : {StateType("memory")})");
            var ordinal = active + 1;
            lean.Quiet();
            lean.Line(loops.Count == 1 ? "/-- Replace with what holds at every loop head. -/"
                : $"/-- Replace with what holds at every head of loop {ordinal}, tested at {Location(loop.Latch)}. -/");
            lean.Wrapped($"def invariant{suffix}", explicitBinders, ": Prop := sorry");
            lean.Line();
            lean.Quiet();
            lean.Line(loops.Count == 1 ? "/-- Replace with a quantity each iteration decreases. -/"
                : $"/-- Replace with a quantity each iteration of loop {ordinal} decreases. -/");
            lean.Wrapped($"def measure{suffix}", explicitBinders, ": Nat := sorry");
            lean.Line();
        }

        /// <summary>The word an unsigned `width`-byte field holding `term` loads as.</summary>
        static string NarrowRead(string term, int width)
        {
            var operand = Regex.IsMatch(term, @"\A[\w.]+\z") ? term : $"({term})";
            return $"({operand}.setWidth {8 * width}).setWidth 32";
        }

        /// <summary>A value the outline cannot write as a term, named for the hole that meets it.</summary>
        static string Unnamed(Value value) => value switch
        {
            Unknown unknown => unknown.What,
            Element => "a span element before it is loaded",
            SpanLength => "a span length outside the loop test",
            LocalAddress or LocalValue => "a struct local as a whole",
            ReferenceArgument reference => $"the reference `{reference.Name}`",
            SpanArgument span => $"the span `{span.Span.Name}`",
            SpannedArray over => $"a span over the array `{over.Array.Name}`",
            _ => "a value the outline cannot name"
        };

        string StackValue(Value operand, PathState state) => operand switch
        {
            Number number => number.Stacked ?? $".scalar ({ScalarConstructor(number.Width)} {number.Term})",
            ObjectTerm reference => $".object {reference.Term}",
            SpanLength length =>
                $".scalar (.i32 (BitVec.ofNat 32 {((SpanTerm)state.State[length.Component]).View}.length))",
            _ => throw Unsupported($"the loop test at {Location(loop.Latch)} reads a value the outline cannot name")
        };

        PathState Initial(Func<Component, object> value) => new()
        {
            Pc = body.BlockStart(loop.Latch), GoalPc = loop.Latch, State = components.Select(value).ToArray()
        };

        /// <summary>The operands of the loop test, evaluated over the test's block from `state`.</summary>
        List<Value> Guard(PathState state)
        {
            while (state.Pc < loop.Latch)
                if (Step(state) != Event.Continue)
                    throw Unsupported(
                        $"the loop test at {Location(loop.Latch)} is not a straight block ({stopReason})");
            var arity = Regex.IsMatch(body.Ops[loop.Latch], @"\A\.br(non)?zero ") ? 1 : 2;
            if (state.Stack.Count != arity)
                throw Unsupported($"the loop test at {Location(loop.Latch)} uses values from before its block");
            return state.Stack;
        }

        void Proof(Writer lean)
        {
            // A caller object's allocation lies below the frame's watermark, which carrying its facts needs.
            foreach (var instance in spec.Objects) lean.Line($"  have {instance.Name}Old := {instance.Name}Live.old");
            foreach (var parameter in SpanParameters)
                if (parameter.Writable)
                {
                    lean.Line($"  have {parameter.Name}Checked : WritableSpan initial (footprint {spec.Arguments})");
                    lean.Line($"      {parameter.Name} {parameter.Width} {parameter.Name}.length :=");
                    lean.Line($"    ⟨{parameter.Name}Valid, {parameter.Mode}, {parameter.Name}Width, rfl, " +
                        $"{parameter.Name}Authority⟩");
                }
                else
                {
                    lean.Line($"  have {parameter.Name}Checked : CheckedSpan initial {parameter.Name} " +
                        $"{parameter.Width} false");
                    lean.Line($"      {parameter.ElementsName} := ⟨{parameter.Name}Valid, {parameter.Mode}, " +
                        $"{parameter.Name}Contents⟩");
                }
            foreach (var array in spanned)
            {
                var view = $"({array.Name}.span {(array.Writable ? "true" : "false")})";
                if (array.Writable)
                    lean.Wrapped($"  have {array.Name}Checked : WritableSpan initial (footprint {spec.Arguments})",
                        [view, $"{array.Width} {array.Name}.length :=", "WritableSpan.of_array",
                            $"{array.Name}Valid {array.Name}Type {array.Name}Authority"], "");
                else
                    lean.Wrapped($"  have {array.Name}Checked : CheckedSpan initial {view} {array.Width} false",
                        [$"{array.ElementsName} :=", "CheckedSpan.of_array", $"{array.Name}Valid",
                            $"{array.Name}Contents false"], "");
            }
            var entryArguments = (spec.Symbolic ? new[] { "initial" } : []).Concat(spec.Parameters.Select(p => p.Name))
                .Concat(spec.Symbolic ? ["wellFormed"] : [])
                .Concat(SpanParameters.SelectMany(parameter => new[]
                {
                    parameter.Name + "Valid",
                    parameter.Name + (parameter.Writable ? "Width" : "Contents.elementWidth"), parameter.Mode
                }))
                .Concat(WordArrays.Select(array => array.Name + "Valid"));
            var pattern = Homes.Concat(["entered", "enter"]);
            lean.Wrapped($"  obtain ⟨{string.Join(", ", pattern)}⟩ :=", ["entry.checked", .. entryArguments], "");
            lean.Line("  have setup := enter.setup");
            lean.Line("  have entryFrame := enter.frame");
            foreach (var array in Indexed) Destructure(lean, array);
            var formed = spec.Parameters.SelectMany(parameter => parameter.Shape switch
            {
                ParameterShape.Reference => new[] { parameter.Name + "Form" },
                ParameterShape.Span or ParameterShape.WordArray => [parameter.Name + "Valid"],
                ParameterShape.Object => [parameter.Name + "Live.formed"],
                _ => []
            });
            // An array argument is checked through `checkedValue`, which unfolds the word arguments beside it.
            var unfolded = !WordArrays.Any() ? []
                : spec.Parameters.Any(parameter => parameter.Shape == ParameterShape.Scalar)
                ? new[] { "checkedValue", "numericValue" } : ["checkedValue"];
            var checkedArguments = spec.Symbolic
                ? "(by simp [cil_checked" + string.Concat(unfolded.Concat(formed).Select(fact => ", " + fact)) + "])"
                : "rfl";
            lean.Wrapped("  refine invoke_loop_satisfies", ["Extracted.lookup0", checkedArguments, "setup",
                HeaderTerm(),
                $"(invariant {Arguments})", $"(measure {Arguments})", "(fun start => ?_)", "?_"], "");
            lean.Wrapped("  · have entryFrame := entryFrame", [Writes ? $"(footprint {Arguments})" : "[]"], "");
            var entry = new PathState
            {
                Pc = 0, GoalPc = 0, State = components.Select(component => component.Part switch
                {
                    Part.Span when slots[component.Slot].Argument => EntrySpan(component.Span!),
                    Part.Span => new Unknown($"the span local `{component.Name}` before it is assigned"),
                    Part.Object => new ObjectTerm(".null"),
                    _ => (object)new Number("0", component.Width, Literal: true)
                }).ToArray(),
                // Each step reading an array's length checks the array, valid in the entry's memory.
                Facts = [.. Indexed.Select(array => array.Name + "Valid")]
            };
            EntryPath(lean, entry);
            Iteration(lean, "  ");
        }

        /// <summary>The suffix a span argument, or the span over a whole array argument, starts as: all of it, with
        /// the checked fact the proof states before the loop.</summary>
        static SpanTerm EntrySpan(Parameter source)
        {
            var view = source.Shape == ParameterShape.WordArray
                ? $"({source.Name}.span {(source.Writable ? "true" : "false")})" : source.Name;
            return new(view, source.Writable ? source.Name + ".length" : source.ElementsName, source.Name + "Checked",
                false, Written: source.Writable);
        }

        /// <summary>Name an array argument's base, length and element type, with the facts its accesses need: a
        /// null array is the precondition's to exclude, since `ldlen` of it throws.</summary>
        void Destructure(Writer lean, Parameter array)
        {
            var name = array.Name;
            var storage = $"(ArrayView.storage {Destructured(array)})";
            lean.Line($"  rcases {name} with ⟨_ | {name}Base, {name}Length, {name}ElementType⟩");
            lean.Line($"  · -- a null `{name}` throws at its length, which Precondition rules out");
            lean.Line("    exfalso");
            lean.Line("    first");
            lean.Line("    | cil_loop_obligation [Precondition]");
            lean.Line($"    | fail \"Precondition must exclude null: `{name}.reference ≠ .null`\"");
            lean.Line($"  simp only at {name}Type");
            lean.Line($"  subst {name}Type");
            // A valid array is shorter than `2 ^ 31`, so its signed bound test reads as unsigned.
            lean.Wrapped($"  have {name}Short : {name}Length < 2 ^ 31 :=",
                ["SpanView.length_bounded", "_", "initial", name + "Valid"], "");
            if (array.Writable)
            {
                lean.Line($"  have {name}Below : {name}Base.allocation < initial.nextIdentity :=");
                lean.Line($"    SpanView.allocation_below (view := {storage}) {name}Valid wellFormed rfl");
                return;
            }
            lean.Line($"  have {name}Count : {name}Length = {array.ElementsName}.length := {name}Contents.length");
            lean.Wrapped($"  have {name}Checked : CheckedSpan initial",
                [storage, $"{array.Width} true {array.ElementsName} :="], "");
            lean.Line($"    ⟨{name}Valid, rfl, {name}Contents⟩");
        }

        /// <summary>An iteration of the active loop from its head, at `indent`.</summary>
        void Iteration(Writer lean, string indent)
        {
            lean.Line($"{indent}rintro ⟨{Pattern()}, current, frame⟩ holds recurse");
            lean.Comment($"{indent}-- ", $"{indent}-- ", "`holds` is the invariant at this loop head and `assumed` " +
                "the Precondition; each side below names the test it took, such as `guard`.");
            var iteration = Initial(component => component.Part switch
            {
                Part.Span => new SpanTerm(component.Name + "View", component.Name + "Remaining",
                    component.Name + "Span", true, Written: component.Span!.Writable),
                Part.Object => new ObjectTerm(component.Name),
                _ => new Number(component.Name, component.Width)
            });
            // An object stays live through the loop; the loop tactics carry the fact across each store.
            foreach (var instance in spec.Objects)
            {
                lean.Line($"{indent}have {instance.Name}Now := {instance.Name}Live.after_confined frame.confined");
                iteration.Facts.Add(instance.Name + "Now.formed");
            }
            Guard(iteration);
            Branch(lean, iteration, indent, "guard");
        }

        /// <summary>The active loop's cutpoint applied to the caller's memory, its parameters, footprint and homes.
        /// </summary>
        string HeaderTerm()
        {
            var arguments = (spec.Symbolic ? new[] { "initial" } : []).Concat(headerParameters[active])
                .Concat(Writes ? [$"(footprint {Arguments})"] : []).Concat(Homes).ToArray();
            return arguments.Length == 0 ? $"header{Suffix(active)}"
                : $"(header{Suffix(active)} {string.Join(" ", arguments)})";
        }

        /// <summary>Leave the active loop at the next loop's test: reach that loop's first head through
        /// `loop_terminates_then`, then walk an iteration of it, which returns or chains on in turn.</summary>
        void Chain(Writer lean, PathState state, string indent)
        {
            if (Values(state) is not { } values)
            {
                Hole(lean, indent, state, $"the next loop's first state holds {stopReason}");
                return;
            }
            var previous = active;
            active++;
            var suffix = Suffix(active);
            lean.Wrapped($"{indent}refine loop_terminates_then", [HeaderTerm(), $"(invariant{suffix} {Arguments})",
                $"(measure{suffix} {Arguments})", $"(fun start{suffix} => ?_)", "?_"], "");
            lean.Line($"{indent}· cil_loop_recurse start{suffix} {values}{Facts(state)}");
            lean.Noted(indent + "  ", "case invariant => sorry",
                $"invariant{suffix} at loop {active + 1}'s first head");
            Iteration(lean, indent);
            active = previous;
        }

        string Pattern()
        {
            var parts = components.Select(component => component.Part == Part.Span
                ? $"⟨{component.Name}View, {component.Name}Remaining, {component.Name}Span⟩"
                : component.Name).ToArray();
            return parts.Length == 1 ? parts[0] : "⟨" + string.Join(", ", parts) + "⟩";
        }

        void EntryPath(Writer lean, PathState state)
        {
            while (state.Pc != loop.Latch)
            {
                var pc = state.Pc;
                var happened = Step(state);
                if (happened == Event.Continue) continue;
                var what = happened == Event.Stop ? stopReason : "a branch or call";
                lean.Noted("    ", "sorry",
                    $"{NotOutlined}the entry path meets {what} at {Location(pc)}; step it to the loop by hand");
                return;
            }
            if (Values(state) is not { } values)
            {
                lean.Noted("    ", "sorry",
                    $"{NotOutlined}the first loop state holds {stopReason}; step the entry to the loop by hand");
                return;
            }
            foreach (var array in spanned.Where(array => state.Facts.Contains(array.Name + "Spanned")))
            {
                var mode = array.Writable ? "true" : "false";
                lean.Wrapped($"    have {array.Name}Spanned :=", [$"step_arraySpan_whole (writable := {mode})",
                    array.Name + "Type", $"(entryFrame.caller_array_valid wellFormed {array.Name}Valid)"], "");
            }
            lean.Line($"    cil_loop_recurse start {values}{Facts(state)}");
            lean.Noted("    ", "case invariant => sorry", "invariant at the first loop head");
        }

        string? Values(PathState state)
        {
            var parts = new List<string>();
            foreach (var value in state.State)
                switch (value)
                {
                    case Number { Narrow: false } or Number { Literal: true }:
                        parts.Add(((Number)value).Term);
                        break;
                    case SpanTerm span:
                        parts.Add($"⟨{Unwrapped(span.View)}, {span.Remaining}, {span.Checked}⟩");
                        break;
                    case ObjectTerm reference:
                        parts.Add(reference.Term);
                        break;
                    default:
                        stopReason = value is Unknown unknown ? unknown.What : "a narrow struct field";
                        return null;
                }
            return parts.Count == 1 ? parts[0] : "(" + string.Join(", ", parts.Select(Unwrapped)) + ")";
        }

        // `(a + b)` inside a tuple needs no parentheses of its own.
        static string Unwrapped(string term) => term.StartsWith('(') && term.EndsWith(')') && !term.Contains(", ")
            ? term[1..^1] : term;

        string Facts(PathState state) => state.Facts.Count == 0 ? "" : $" [{string.Join(", ", state.Facts)}]";

        void Hole(Writer lean, string indent, PathState state, string what) =>
            lean.Noted(indent, "sorry", $"{NotOutlined}{what}; step on by hand from {Location(state.GoalPc)}");

        void Walk(Writer lean, PathState state, string indent)
        {
            while (true)
            {
                if (state.Pc == loop.Latch)
                {
                    if (Values(state) is not { } values)
                    {
                        Hole(lean, indent, state, $"the next loop state holds {stopReason}");
                        return;
                    }
                    lean.Line($"{indent}cil_loop_recurse recurse {values}{Facts(state)}");
                    lean.Noted(indent, "case invariant => sorry", $"invariant again at the loop head");
                    lean.Noted(indent, "case measure => sorry", $"measure decreases over this iteration");
                    return;
                }
                if (active + 1 < loops.Count && state.Pc == loops[active + 1].Latch)
                {
                    Chain(lean, state, indent);
                    return;
                }
                var pc = state.Pc;
                current = lean;
                currentIndent = indent;
                var happened = Step(state);
                current = null;
                switch (happened)
                {
                    case Event.Continue:
                        continue;
                    case Event.Stop:
                        Hole(lean, indent, state, $"{stopReason} at {Location(pc)}");
                        return;
                    case Event.Return:
                        lean.Line($"{indent}cil_loop_finish{Facts(state)}");
                        spec.Postcondition(lean, indent, $"Postcondition at the return at {Location(pc)}");
                        return;
                    case Event.Call:
                        if (!Call(lean, state, indent, pc)) return;
                        continue;
                    case Event.Branch:
                        Branch(lean, state, indent, $"branch{++branches}");
                        return;
                }
            }
        }

        bool Call(Writer lean, PathState state, string indent, int pc)
        {
            var call = Regex.Match(body.Ops[pc], @"\A\.call(?:Instance)? (\d+) (\d+)\z");
            var callee = int.Parse(call.Groups[1].Value);
            var count = int.Parse(call.Groups[2].Value);
            var arguments = state.Stack.TakeLast(count).ToArray();
            state.Stack.RemoveRange(state.Stack.Count - count, count);
            var stores = Stores(callee) is not null;
            var spanStores = SpanStores(extraction, callee) is not null;
            // A span is lent only from the iteration's first memory, at which `frame` holds.
            SpanTerm? Lent(Value argument) => argument is LocalValue local && spanStores && !state.Moved &&
                state.State[components.IndexOf(slots[local.Slot].Components[0])] is SpanTerm
                    { Written: true, Head: not null } span ? span : null;
            bool Named(Value argument) => argument is Number { Narrow: false } or ReferenceArgument ||
                argument is AddedReference && stores || Lent(argument) is not null;
            string Passed(Value argument) =>
                argument is LocalValue local && slots[local.Slot].Components[0] is { Part: Part.Span } component
                    ? $"the span `{component.Name}`, which it lends only to a callee storing the first element of " +
                        "a nonempty written span, before any other store of the iteration"
                    : Unnamed(argument);
            if (state.Called || !arguments.All(Named))
            {
                Hole(lean, indent, state, state.Called
                    ? $"a second call at {Location(pc)}, whose input depends on the first call's state"
                    : $"the call at {Location(pc)} passes " + Passed(arguments.First(argument => !Named(argument))));
                return false;
            }
            // An element a storing callee writes is named with its side conditions, which close its precondition.
            var elementFacts = new List<string>();
            (current, currentIndent) = (lean, indent);
            var terms = arguments.Select(argument => argument switch
            {
                Number number => number.Term,
                ReferenceArgument reference => reference.Name,
                AddedReference added => ElementSlot(added, elementFacts, caller: true),
                LocalValue => Lent(argument)!.View,
                _ => throw new InvalidOperationException("unnamed argument")
            }).ToArray();
            current = null;
            state.Facts.AddRange(elementFacts);
            var lent = arguments.Where(argument => Lent(argument) is not null).Cast<LocalValue>()
                .Select(local => (slots[local.Slot].Components[0].Name, Span: Lent(local)!)).ToArray();
            // The lent span's bytes lie in the frame's footprint and below its watermark, the call's side conditions.
            foreach (var (spanName, span) in lent)
            {
                lean.Line($"{indent}have {spanName}Covered := {span.Checked}.covered");
                lean.Line($"{indent}have {spanName}Below := {span.Checked}.below wellFormed");
            }
            var input = terms.Length switch { 0 => "()", 1 => terms[0]!, _ => "(" + string.Join(", ", terms) + ")" };
            if (state.GoalPc != pc) lean.Line($"{indent}cil_loop_advance{Facts(state)}");
            // The frame's footprint is a definition the call's side condition unfolds to find the callee's.
            var unfolded = spec.Framed && !spec.Parameters.Any(parameter => parameter.Shape == ParameterShape.Reference)
                ? [.. state.Facts, "footprint"] : state.Facts;
            var facts = unfolded.Count == 0 ? "" : $" [{string.Join(", ", unfolded)}]";
            // The output keeps its name, so the next loop state may name it whatever the postcondition says.
            var keeping = extraction.Methods[callee].ReturnType.FullName != "System.Void" ? "keeping " : "";
            lean.Line($"{indent}cil_loop_call {keeping}{callees[callee]}_holds {input}{facts}");
            if (lent.Length == 1)
                lean.Line($"{indent}case precondition => exact ⟨{lent[0].Span.Head}, " +
                    $"{lent[0].Span.Checked}.lend wellFormed frame⟩");
            else if (elementFacts.Count == 0)
                lean.Noted(indent, "case precondition => sorry",
                    $"{extraction.Methods[callee].Name}'s precondition at this call");
            if (extraction.Methods[callee].ReturnType.FullName != "System.Void")
                state.Stack.Add(new Number("output", ElementWidth(extraction.Methods[callee].ReturnType)!.Value));
            state.Called = true;
            state.Pc = pc + 1;
            state.GoalPc = pc + 1;
            return true;
        }

        /// <summary>Split the goal on the test at `state.Pc`, its operands on the stack, and walk each side.</summary>
        void Branch(Writer lean, PathState state, string indent, string fact)
        {
            var pc = state.Pc;
            var op = body.Ops[pc];
            var opName = Regex.Match(op, @"\A\.(\w+)").Groups[1].Value;
            var target = Body.Target(op)!.Value;
            var unary = opName is "brzero" or "brnonzero";
            var operands = state.Stack.TakeLast(unary ? 1 : 2).ToArray();
            state.Stack.RemoveRange(state.Stack.Count - operands.Length, operands.Length);
            state.GoalPc = pc;
            PathState Side(int next, string? known)
            {
                var side = state.Copy();
                side.Pc = next;
                if (known is not null) side.Facts.Add(known);
                return side;
            }
            if (unary && operands[0] is SpanLength length && state.State[length.Component] is SpanTerm
                { Caseable: true } span)
            {
                var name = components[length.Component].Name;
                var empty = Side(opName == "brzero" ? target : pc + 1, null);
                var cons = Side(opName == "brzero" ? pc + 1 : target, null);
                cons.Obtained.Clear();
                lean.Line($"{indent}cases {span.Remaining} with");
                // A written span splits on its length; its elements are never read.
                if (span.Written)
                {
                    var rest = name + "Rest";
                    empty.State[length.Component] = span with { Remaining = "0", Caseable = false };
                    cons.State[length.Component] = span with { Remaining = $"({rest} + 1)", Caseable = false,
                        Head = rest, Tail = rest };
                    lean.Line($"{indent}| zero =>");
                    Walk(lean, empty, indent + "  ");
                    lean.Line($"{indent}| succ {rest} =>");
                    Walk(lean, cons, indent + "  ");
                    return;
                }
                var head = name + "Head";
                var tail = name + "Tail";
                empty.State[length.Component] = span with { Remaining = "[]", Caseable = false };
                cons.State[length.Component] = span with { Remaining = $"({head} :: {tail})", Caseable = false,
                    Head = head, Tail = tail };
                lean.Line($"{indent}| nil =>");
                Walk(lean, empty, indent + "  ");
                lean.Line($"{indent}| cons {head} {tail} =>");
                Walk(lean, cons, indent + "  ");
                return;
            }
            if (unary && operands[0] is Number { Literal: true } literal)
            {
                var truth = literal.Term != "0";
                state.Pc = (opName == "brnonzero") == truth ? target : pc + 1;
                Walk(lean, state, indent);
                return;
            }
            if (unary && operands[0] is ObjectTerm reference)
            {
                NullTest(lean, state, indent, reference.Term, opName == "brnonzero" ? target : pc + 1,
                    opName == "brnonzero" ? pc + 1 : target);
                return;
            }
            // Identity of two object references: the object locals and caller instances the walk names.
            var identities = operands.Select(operand => operand switch
            {
                ObjectTerm term => term.Term,
                ReferenceArgument argument when spec.Parameters.Any(parameter => parameter.Name == argument.Name &&
                    parameter.Shape == ParameterShape.Object) => $"(.address {argument.Name})",
                _ => null
            }).ToArray();
            if (opName is "beq" or "bne" && identities.All(term => term is not null))
            {
                var (identity, equalTaken) =
                    Body.Test(opName, [$"({identities[0]} : ManagedReference)", identities[1]!], 64);
                var same = Side(equalTaken ? target : pc + 1, fact);
                var different = Side(equalTaken ? pc + 1 : target, fact);
                lean.Line($"{indent}by_cases {fact} : {identity}");
                lean.Line($"{indent}· -- {Describe(same.Pc)}");
                Walk(lean, same, indent + "  ");
                lean.Line($"{indent}· -- {Describe(different.Pc)}");
                Walk(lean, different, indent + "  ");
                return;
            }
            if (operands.FirstOrDefault(operand => operand is not Number { Narrow: false }) is { } unnamed)
            {
                Hole(lean, indent, state, $"the test at {Location(pc)} reads {Unnamed(unnamed)}");
                return;
            }
            var terms = operands.Select(operand => ((Number)operand).Term).ToArray();
            var (condition, takenWhenTrue) = Body.Test(opName, terms, 8 * ((Number)operands[0]).Width);
            var holds = Side(takenWhenTrue ? target : pc + 1, fact);
            var fails = Side(takenWhenTrue ? pc + 1 : target, fact);
            lean.Line($"{indent}by_cases {fact} : {condition}");
            lean.Line($"{indent}· -- {Describe(holds.Pc)}");
            Walk(lean, holds, indent + "  ");
            lean.Line($"{indent}· -- {Describe(fails.Pc)}");
            Walk(lean, fails, indent + "  ");
        }

        /// <summary>Split the goal on whether the object local holding `term` is null and walk each side; the
        /// instance it may hold is live only by a fact the author proves.</summary>
        void NullTest(Writer lean, PathState state, string indent, string term, int present, int absent)
        {
            PathState Side(int next, string value)
            {
                var side = state.Copy();
                side.Pc = next;
                for (var index = 0; index < side.State.Length; index++)
                    if (side.State[index] is ObjectTerm held && held.Term == term)
                        side.State[index] = new ObjectTerm(value);
                return side;
            }
            if (term == ".null")
            {
                Walk(lean, Side(absent, term), indent);
                return;
            }
            // The liveness hole names the loop head's memory, which a call or a store replaces.
            if (!Regex.IsMatch(term, @"\A[A-Za-z][A-Za-z0-9_]*\z") || state.Called || state.Moved)
            {
                Hole(lean, indent, state,
                    $"the null test at {Location(state.Pc)} of an object the outline cannot name");
                return;
            }
            var instance = term + "Object";
            var live = Side(present, $"(.address {instance})");
            live.Facts.Add(instance + "Live.formed");
            lean.Line($"{indent}cases {term} with");
            lean.Line($"{indent}| null =>");
            Walk(lean, Side(absent, ".null"), indent + "  ");
            lean.Line($"{indent}| address {instance} =>");
            lean.Noted(indent + "  ", $"have {instance}Live : LiveObject current {instance} := sorry",
                $"`{term}` holds a live instance");
            Walk(lean, live, indent + "  ");
        }

        string Describe(int pc) => pc == loop.Head ? "another iteration"
            : pc < loop.Head || pc > loop.Latch ? $"leaves the loop at {Location(pc)}" : $"continues at {Location(pc)}";

        /// <summary>Evaluate the operation at `state.Pc`, advancing it unless the walk must act.</summary>
        Event Step(PathState state)
        {
            var op = body.Ops[state.Pc];
            var stack = state.Stack;
            Value Pop()
            {
                if (stack.Count == 0) return new Unknown("a value from before this path");
                var top = stack[^1];
                stack.RemoveAt(stack.Count - 1);
                return top;
            }
            Event Stop(string reason)
            {
                stopReason = reason;
                return Event.Stop;
            }
            Match match;
            if ((match = Regex.Match(op, @"\A\.local (\d+)\z")).Success)
            {
                var slot = slots[int.Parse(match.Groups[1].Value)];
                var first = components.IndexOf(slot.Components[0]);
                stack.Add(slot.Components[0].Part is Part.Word or Part.Object ? (Value)state.State[first]
                    : new LocalValue(slot.Index));
            }
            else if ((match = Regex.Match(op, @"\A\.setLocal (\d+)\z")).Success)
            {
                var slot = slots[int.Parse(match.Groups[1].Value)];
                var first = components.IndexOf(slot.Components[0]);
                var value = Pop();
                state.Moved = true;
                if (slot.Components[0].Part == Part.Word && value is Number or Unknown)
                    state.State[first] = value;
                else if (slot.Components[0].Part == Part.Span && value is Sliced sliced &&
                    state.State[sliced.Component] is SpanTerm { Tail: { } tail } span)
                {
                    var name = components[sliced.Component].Name;
                    state.State[first] = new SpanTerm(name + "Sliced", tail, name + "Next", false,
                        Written: span.Written);
                }
                else if (slot.Components[0].Part == Part.Object && value is ObjectTerm)
                    state.State[first] = value;
                else if (slot.Components[0].Span is { } source &&
                    (value is SpanArgument copied && copied.Span == source ||
                        value is SpannedArray spannedArray && spannedArray.Array == source))
                    state.State[first] = EntrySpan(source);
                else return Stop("a store of a value the outline cannot name");
            }
            else if ((match = Regex.Match(op, @"\A\.arg (\d+)\z")).Success)
            {
                var parameter = spec.Parameters[int.Parse(match.Groups[1].Value)];
                stack.Add(parameter.Shape switch
                {
                    ParameterShape.Scalar => new Number(parameter.Name, parameter.Width),
                    ParameterShape.Boolean => new Unknown($"the `bool` argument `{parameter.Name}`"),
                    ParameterShape.Narrow => new Unknown($"the narrow argument `{parameter.Name}`"),
                    ParameterShape.Reference or ParameterShape.Object => new ReferenceArgument(parameter.Name),
                    ParameterShape.WordArray => new WordArrayArgument(parameter),
                    _ => new SpanArgument(parameter)
                });
            }
            // The span a local takes over a whole array argument before the loop, on the entry path, where the
            // entry frame carries the array's validity past the frame's allocations.
            else if (op.StartsWith(".memory (.arraySpan ", StringComparison.Ordinal) && stack.Count > 0 &&
                stack[^1] is WordArrayArgument { Array: var whole } && spanned.Contains(whole))
            {
                stack.RemoveAt(stack.Count - 1);
                stack.Add(new SpannedArray(whole));
                state.Facts.Add(whole.Name + "Spanned");
            }
            else if ((match = Regex.Match(op, @"\A\.const(32|64) (.+)\z")).Success)
            {
                var literal = match.Groups[2].Value;
                var width = match.Groups[1].Value == "64" ? 8 : 4;
                stack.Add(new Number(literal, width, Literal: Regex.IsMatch(literal, @"\A\d+\z")));
            }
            else if ((match = Regex.Match(op, @"\A\.(add|sub|mul|band|bor|bxor)\z")).Success)
            {
                var right = Pop();
                var left = Pop();
                var symbol = match.Groups[1].Value switch
                {
                    "add" => "+", "sub" => "-", "mul" => "*", "band" => "&&&", "bor" => "|||", _ => "^^^"
                };
                if (left is Number { Narrow: false } a && right is Number { Narrow: false } b && a.Width == b.Width)
                    stack.Add(new Number($"({a.Term} {symbol} {b.Term})", a.Width));
                else stack.Add(new Unknown("arithmetic on a value the outline cannot name"));
            }
            else if (op == ".convI8" || op == ".convU8")
            {
                var value = Pop();
                stack.Add(value is Number { Literal: true, Width: 4 } literal ? literal with { Width = 8 }
                    : new Unknown("a widened value"));
            }
            else if ((match = Regex.Match(op, @"\A\.localAddr (\d+)\z")).Success)
                stack.Add(new LocalAddress(int.Parse(match.Groups[1].Value)));
            else if ((match = Regex.Match(op, @"\A\.initAggregate \d+\z")).Success)
            {
                if (Pop() is not LocalAddress address) return Stop("zeroing storage other than a struct local");
                state.Moved = true;
                foreach (var field in slots[address.Slot].Components)
                    state.State[components.IndexOf(field)] = new Number("0", field.Width, Literal: true);
            }
            else if ((match = Regex.Match(op, @"\A\.fieldAt (\d+) (\d+)\z")).Success)
            {
                var source = Pop();
                var slot = source switch
                {
                    LocalValue value => value.Slot, LocalAddress address => address.Slot, _ => -1
                };
                var field = slot < 0 ? null : slots[slot].Components.FirstOrDefault(component =>
                    component.Offset == int.Parse(match.Groups[1].Value));
                if (field is null) return Stop("a field read outside a struct local");
                var held = (Value)state.State[components.IndexOf(field)];
                // A narrow field loads its low bytes zero-extended, as `narrowLoad` reads the word it holds.
                stack.Add(field.Width < 4 && held is Number { Literal: false } word
                    ? new Number(NarrowRead(word.Term, field.Width), 4) : held);
            }
            else if ((match = Regex.Match(op, @"\A\.setFieldAt (\d+) (\d+)\z")).Success)
            {
                var value = Pop();
                var field = Pop() is LocalAddress address ? slots[address.Slot].Components.FirstOrDefault(component =>
                    component.Offset == int.Parse(match.Groups[1].Value)) : null;
                if (field is null || value is not (Number or Unknown))
                    return Stop("a field store outside a struct local");
                state.Moved = true;
                state.State[components.IndexOf(field)] = value is Number { Literal: false } number && field.Width < 4
                    ? number with { Narrow = true } : value;
            }
            else if (op == ".memory .spanLength")
            {
                if (Pop() is not LocalValue value || slots[value.Slot].Components[0].Part != Part.Span)
                    return Stop("the length of a span the outline does not follow");
                stack.Add(new SpanLength(components.IndexOf(slots[value.Slot].Components[0])));
            }
            else if (op == ".memory (.spanSlice false)")
            {
                var count = Pop();
                var source = Pop();
                if (count is not Number { Term: "1" } || source is not LocalValue value ||
                    state.State[components.IndexOf(slots[value.Slot].Components[0])] is not SpanTerm { Tail: { } } span)
                    return Stop("a slice other than `Slice(1)` of a span known to be nonempty");
                var component = components.IndexOf(slots[value.Slot].Components[0]);
                PendingTail(state, component, span);
                stack.Add(new Sliced(component));
            }
            else if ((match = Regex.Match(op, @"\A\.memory \(\.spanItem (\d+)\)\z")).Success)
            {
                var index = Pop();
                var source = Pop();
                if (index is not Number { Term: "0" } || source is not LocalValue value ||
                    state.State[components.IndexOf(slots[value.Slot].Components[0])] is not SpanTerm { Head: { } })
                    return Stop("an element other than the first of a span known to be nonempty");
                stack.Add(new Element(components.IndexOf(slots[value.Slot].Components[0])));
            }
            else if (op is ".loadScalar 4" or ".load64" or ".loadScalar 8" && stack.Count > 0 && stack[^1] is Element)
            {
                var element = (Element)Pop();
                var span = (SpanTerm)state.State[element.Component];
                if (state.Called) return Stop("a span read after a call");
                if (span.Written)
                    return Stop("a read of a span the loop writes, whose contents the frame does not carry");
                PendingHead(state, element.Component, span);
                stack.Add(new Number(span.Head!, components[element.Component].Width));
            }
            else if (op == ".memory .arrayLength")
            {
                if (Pop() is not WordArrayArgument array)
                    return Stop("the length of an array the outline does not follow");
                stack.Add(new ArrayLength(array.Array));
            }
            // `ldlen` pushes the length as a 64-bit word, which a test of an `int` index narrows; a test reads
            // the narrowed word simplified.
            else if (op == ".convI4" && stack.Count > 0 && stack[^1] is ArrayLength length)
            {
                stack.RemoveAt(stack.Count - 1);
                var count = length.Array.Name + "Length";
                stack.Add(new Number($"(BitVec.ofNat 32 {count})", 4,
                    Stacked: $".scalar (.i32 ((BitVec.ofNat 64 {count}).setWidth 32))"));
            }
            else if ((match = Regex.Match(op, @"\A\.memory \(\.arrayLoad (\d+) false\)\z")).Success &&
                stack.Count >= 2 && stack[^2] is WordArrayArgument read)
            {
                if (stack[^1] is not Number { Width: 4, Narrow: false } index || current is null ||
                    int.Parse(match.Groups[1].Value) != read.Array.Width)
                    return Stop("an array read the outline cannot name at an index and the element's width");
                if (read.Array.Writable)
                    return Stop("a read of the array the loop stores into, whose contents the frame does not carry");
                if (state.Moved || state.Called || !state.Obtained.Add(read.Array.Name + "Found"))
                    return Stop("an array read after a store, a call or another read of the iteration");
                stack.RemoveRange(stack.Count - 2, 2);
                stack.Add(new Number(ElementRead(read.Array, index.Term, state.Facts), read.Array.Width));
            }
            else if ((match = Regex.Match(op, @"\A\.memory \(\.arrayStore (\d+)\)\z")).Success &&
                stack.Count >= 3 && stack[^3] is WordArrayArgument stores)
            {
                var width = int.Parse(match.Groups[1].Value);
                if (stack[^2] is not Number { Width: 4, Narrow: false } index ||
                    stack[^1] is not Number { Narrow: false } stored || stored.Width != width || current is null)
                    return Stop("an array store the outline cannot name at an index and the element's width");
                if (state.Moved || state.Called)
                    return Stop("an array store after another store or a call of the iteration, whose memory the " +
                        "array's checks are not carried to");
                stack.RemoveRange(stack.Count - 3, 3);
                state.Facts.Add(ElementStore(stores.Array, index.Term, stored.Term));
                state.Moved = true;
            }
            else if (op == ".nop") { }
            else if (Body.Target(op) is { } target && !Body.Conditional(op))
            {
                state.Pc = target;
                return Event.Continue;
            }
            else if (Body.Conditional(op)) return Event.Branch;
            else if (op.StartsWith(".call ", StringComparison.Ordinal) ||
                op.StartsWith(".callInstance ", StringComparison.Ordinal)) return Event.Call;
            else if (op == ".ret" || op.StartsWith(".ret (some ", StringComparison.Ordinal)) return Event.Return;
            else if ((match = Regex.Match(op, @"\A\.memory \(\.add (\d+) true\)\z")).Success && current is not null &&
                !state.Called && stack.Count >= 2 &&
                stack[^1] is Number { Width: 4, Narrow: false } index && stack[^2] is ReferenceArgument reference &&
                spec.Parameters.Any(parameter => parameter.Name == reference.Name &&
                    parameter.Shape == ParameterShape.Reference))
            {
                stack.RemoveRange(stack.Count - 2, 2);
                stack.Add(new AddedReference(reference.Name, index.Term, int.Parse(match.Groups[1].Value)));
            }
            else if (op is ".store64" or ".storeScalar 4" or ".storeScalar 8" && stack.Count >= 2 &&
                stack[^2] is Element written && state.State[written.Component] is SpanTerm { Written: true })
            {
                var width = op == ".storeScalar 4" ? 4 : 8;
                if (state.Moved || state.Called)
                    return Stop("a span store after another store or a call of the iteration, whose memory the " +
                        "span's checks are not carried to");
                if (stack[^1] is not Number { Narrow: false } stored || stored.Width != width ||
                    components[written.Component].Width != width)
                    return Stop("a span store of a value the outline cannot name at the element's width");
                stack.RemoveRange(stack.Count - 2, 2);
                state.Facts.AddRange(SpanWrite(state, written.Component, stored.Term, StoreLemma(op)));
                state.Moved = true;
            }
            else if (op is ".store64" or ".storeScalar 4" or ".storeScalar 8" && stack.Count >= 2 &&
                stack[^2] is AddedReference added && !state.Moved)
            {
                var width = op == ".storeScalar 4" ? 4 : 8;
                if (stack[^1] is not Number { Narrow: false } stored || stored.Width != width || added.Width != width)
                    return Stop("a store through `Unsafe.Add` of a value the outline cannot name at the " +
                        "element's width");
                stack.RemoveRange(stack.Count - 2, 2);
                state.Facts.AddRange(ElementWrite(added, stored.Term, StoreLemma(op)));
                state.Moved = true;
            }
            else if (Regex.IsMatch(op, @"\A\.memory \(\.add \d+ (true|false)\)\z"))
                return Stop("an `Unsafe.Add` other than one of a reference argument by a 32-bit index, written " +
                    "through before any other store of an iteration, which needs `add memory base width offset = " +
                    ".ok reference` (such as from `Writable.add_int`) and write authority in `footprint`");
            else return Stop($"`{op}`, which the outline does not step");
            state.Pc++;
            return Event.Continue;
        }

        // Span facts are destructured where a path first reads them, at the walk's current indent.
        Writer? current;
        string currentIndent = "";

        void PendingHead(PathState state, int component, SpanTerm span)
        {
            var name = components[component].Name;
            var apart = "";
            if (Writes && current is not null && state.Obtained.Add(name + "Apart"))
            {
                current.Wrapped($"{currentIndent}have {name}Apart :",
                    [$"∀ entry ∈ footprint {Arguments},", $"SpanApart {span.View} entry :="], "");
                current.Noted(currentIndent + "    ", "sorry", $"`{name}` lies apart from the memory the loop writes");
                apart = $" {name}Apart";
            }
            else if (Writes) apart = $" {name}Apart";
            Pending(state, $"obtain ⟨{name}Item, -, {name}Found, {name}Element⟩ :=",
                $"({span.Checked}.within wellFormed frame{apart}).head (by decide)");
        }


        /// <summary>Store `value` into the first element of the written span `component`, at the iteration's
        /// first memory; returns the facts the loop tactics step the store with.</summary>
        string[] SpanWrite(PathState state, int component, string value, string lemma)
        {
            var name = components[component].Name;
            var span = (SpanTerm)state.State[component];
            current!.Line($"{currentIndent}obtain ⟨{name}Item, {name}After, {name}Address, {name}Found, {name}Wrote,");
            current.Line($"{currentIndent}    {name}Frame⟩ :=");
            current.Line($"{currentIndent}  frame.write_span_head wellFormed {span.Checked} {value}");
            // The written memory is named so the loop tactics carry the span's checks to it.
            return [name + "Found", name + "Wrote", $"{lemma} {name}Wrote"];
        }

        /// <summary>Write `value` to the element `added` names, at the iteration's first memory, leaving its
        /// authority, index bound and footprint as holes; returns the facts the loop tactics step it with.</summary>
        string[] ElementWrite(AddedReference added, string value, string lemma)
        {
            var name = added.Base;
            var facts = new List<string>();
            ElementSlot(added, facts);
            var lean = current!;
            var indent = currentIndent;
            lean.Line($"{indent}obtain ⟨{name}After, {name}Wrote, -, -, -⟩ := {name}Slot.write_one {value}");
            // The frame at the written memory is what the loop tactics carry the iteration's other facts in.
            lean.Line($"{indent}have {name}Frame := frame.write {name}Wrote");
            lean.Line($"{indent}  (by simpa [numberBytes_length] using {name}Within)");
            lean.Line($"{indent}  (by simpa [Reference.element_allocation] using wellFormed.form_bound {name}Form)");
            return [name + "Add", $"{lemma} {name}Wrote"];
        }

        /// <summary>An index term as `toNat` and `element` read it: a name, or a word ascribed its type.</summary>
        static string IndexTerm(string term) => Regex.IsMatch(term, @"\A[A-Za-z_][\w.]*\z") ? term : $"({term} : W32)";

        /// <summary>Load element `index` of a read-only array at the iteration's first memory, its bound left to
        /// the author's definitions; adds the facts that step `ldelem` to `facts` and returns the loaded term.
        /// </summary>
        string ElementRead(Parameter array, string index, List<string> facts)
        {
            var name = array.Name;
            var position = IndexTerm(index);
            var lean = current!;
            var indent = currentIndent;
            lean.Line($"{indent}have {name}Bound : {position}.toNat < {array.ElementsName}.length := by");
            ArrayObligation(lean, indent);
            var apart = "";
            if (Writes)
            {
                lean.Wrapped($"{indent}have {name}Apart :", [$"∀ entry ∈ footprint {Arguments},",
                    $"SpanApart (ArrayView.storage {Destructured(array)}) entry :="], "");
                lean.Noted(indent + "    ", "sorry", $"`{name}` lies apart from the memory the loop writes");
                apart = $" {name}Apart";
            }
            lean.Line($"{indent}obtain ⟨{name}Item, {name}Found, {name}Loaded⟩ :=");
            lean.Line($"{indent}  ({name}Checked.within wellFormed frame{apart}).contents.array_load");
            lean.Line($"{indent}    (frame.caller_array_valid wellFormed {name}Valid) (by decide) {name}Bound");
            lean.Line($"{indent}have {name}Step :=");
            lean.Line($"{indent}  step_arrayLoad_of_element (index := .i32 {index}) rfl {name}Found {name}Loaded");
            // The step pushes the element through `numericOfWidth`, which these unfold to the element itself.
            facts.AddRange(new[] { name + "Step", "numericOfWidth", "BitVec.ofNat_toNat" }
                .Where(fact => !facts.Contains(fact)));
            return $"{array.ElementsName}[{position}.toNat]";
        }

        /// <summary>Store `value` into element `index` of the written array at the iteration's first memory,
        /// its bound, authority and footprint left to the author's definitions; returns the fact that steps
        /// `stelem`.</summary>
        string ElementStore(Parameter array, string index, string value)
        {
            var name = array.Name;
            var width = array.Width;
            var position = IndexTerm(index);
            var element = $"{name}Base.element {width} {position}.toNat";
            var lean = current!;
            var indent = currentIndent;
            lean.Line($"{indent}have {name}Bound : {position}.toNat < {name}Length := by");
            ArrayObligation(lean, indent);
            lean.Line($"{indent}have {name}Slot : Writable current ({element}) {width} 0 1 := by");
            ArrayObligation(lean, indent);
            lean.Wrapped($"{indent}have {name}Within :",
                [$"∃ entry ∈ footprint {Arguments},", $"Within ({element}, {width}) entry := by"], "");
            ArrayObligation(lean, indent);
            lean.Line($"{indent}have {name}Element := arrayElement_of_access (width := {width})");
            lean.Line($"{indent}  (frame.caller_array_valid wellFormed {name}Valid) rfl rfl {name}Bound");
            lean.Line($"{indent}  (by simpa using {name}Slot 0 (by omega))");
            lean.Line($"{indent}obtain ⟨{name}After, {name}Wrote, -, -, -⟩ := {name}Slot.write_one {value}");
            // The frame at the written memory is what the loop tactics carry the iteration's other facts in.
            lean.Line($"{indent}have {name}Frame := frame.write {name}Wrote");
            lean.Line($"{indent}  (by simpa [numberBytes_length] using {name}Within)");
            lean.Line($"{indent}  (by simpa [Reference.element_allocation] using {name}Below)");
            var lemma = width == 8 ? "step_arrayStore_i64_of_write" : "step_arrayStore_of_write";
            lean.Line($"{indent}have {name}Step :=");
            lean.Line($"{indent}  {lemma} (index := .i32 {index}) rfl {name}Element {name}Wrote");
            return name + "Step";
        }

        /// <summary>Name the element `added` addresses with its write authority at the iteration's first memory,
        /// index bound, footprint entry and `add` fact; adds the facts a step through it needs to `facts`. With
        /// `caller`, authority and `add` are stated at the caller's memory, which the loop tactics carry past
        /// the iteration's local stores.</summary>
        string ElementSlot(AddedReference added, List<string> facts, bool caller = false)
        {
            var name = added.Base;
            var index = Regex.IsMatch(added.Index, @"\A[A-Za-z_][\w.]*\z") ? added.Index : $"({added.Index} : W32)";
            var element = $"{name}.element {added.Width} {index}.toNat";
            var lean = current!;
            var indent = currentIndent;
            // Each side condition follows from the author's definitions, so it is a hole only while they are.
            var closer = $"{indent}  cil_loop_obligation [invariant, Precondition, footprint]";
            var authority = caller ? name + "Reach" : name + "Slot";
            lean.Line($"{indent}have {authority} : Writable {(caller ? "initial" : "current")} ({element}) " +
                $"{added.Width} 0 1 := by");
            lean.Line(closer);
            lean.Line($"{indent}have {name}Small : {index}.toNat < 2 ^ 31 := by");
            lean.Line(closer);
            lean.Line($"{indent}have {name}Within : ∃ entry ∈ footprint {Arguments},");
            lean.Line($"{indent}    Within ({element}, {added.Width}) entry := by");
            lean.Line(closer);
            if (caller)
            {
                lean.Line($"{indent}have {name}Add := add_int_element wellFormed {name}Form {name}Small");
                lean.Line($"{indent}  (by simpa using {name}Reach 0 (by omega))");
                lean.Line($"{indent}have {name}Slot := {name}Reach.after_confined frame.confined wellFormed");
            }
            else
            {
                lean.Line($"{indent}have {name}Add := add_int_element frame.wellFormed");
                lean.Line($"{indent}  (frame.caller_form wellFormed {name}Form) {name}Small");
                lean.Line($"{indent}  (by simpa using {name}Slot 0 (by omega))");
            }
            facts.Add(name + "Add");
            return element;
        }

        void PendingTail(PathState state, int component, SpanTerm span)
        {
            var name = components[component].Name;
            Pending(state, $"obtain ⟨{name}Sliced, {name}Cut, {name}Next⟩ :=", $"{span.Checked}.tail");
        }

        void Pending(PathState state, string head, string fact)
        {
            if (current is null || !state.Obtained.Add(head)) return;
            current.Wrapped(currentIndent + head, [fact], "");
        }
    }

    static string LoopProof(Extraction extraction, Specification spec, Body body,
        IReadOnlyList<(int Head, int Latch)> loops, Names names, Writer lean) =>
        new LoopOutline(extraction, spec, body, loops, names).Emit(lean);
}
