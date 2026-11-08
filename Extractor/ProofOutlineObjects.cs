using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Class instances in an outline: the named fields an extraction emits, the premises and footprint they give an
// object argument, and the straight-line walk that steps field loads and one final field store.
internal static partial class ProofOutline
{
    /// <summary>A field an extraction names, as `Path.Name`; a reference field has no width.</summary>
    sealed record ViewField(string Path, string Name, int? Width, int Offset, bool Stored, int[] Loaders,
        int[] Storers)
    {
        internal string Lean => Path + "." + Name;
    }

    /// <summary>The fields an extraction's `Extracted.Classes` names, by the full name of their class, and whether
    /// any of its methods stores each.</summary>
    sealed class FieldViews
    {
        readonly Dictionary<string, ViewField[]> classes = new(StringComparer.Ordinal);

        internal FieldViews(Extraction extraction)
        {
            foreach (var view in extraction.Views)
                classes[view.FullName] = [.. view.Fields.Select(field => new ViewField(view.Path, field.Lean,
                    field.Width, field.Offset, field.Storers.Length > 0, field.Loaders, field.Storers))];
        }

        /// <summary>The named fields of an instance of `type`: its class's and its bases', nearest first.</summary>
        internal ViewField[] Of(TypeReference type) =>
            [.. new[] { type }.Concat(ObjectTypes.Bases(type))
                .SelectMany(owner => classes.GetValueOrDefault(owner.FullName) ?? [])];
    }

    /// <summary>The premise an object argument gives each named field: `Owned` when some method stores it.</summary>
    static string FieldPremise(ViewField field, string memory, string name) =>
        $"{field.Lean}.{(field.Stored ? "Owned" : "Readable")} {memory} {name}";

    /// <summary>The fact naming an object argument's field.</summary>
    static string FieldFact(Parameter parameter, ViewField field) =>
        parameter.Name + char.ToUpperInvariant(field.Name[0]) + field.Name[1..];

    /// <summary>The objects a straight-line body reaches, the field facts its statement assumes of each and the
    /// footprint it writes, as the walk of the body finds them.</summary>
    sealed class ObjectPlan
    {
        internal List<(string Name, string Statement)> Premises { get; } = [];
        internal List<string> Targets { get; } = [];
        internal List<string> Entries { get; } = [];
    }

    /// <summary>An object a body reaches: an argument, or the object a reference field of one holds, which the
    /// statement binds as a target.</summary>
    sealed record Reached(string Name, ViewField[] Fields, string? Held = null, string? Holder = null);

    enum AccessKind { Load, Store, Read, Own }

    /// <summary>A field access in program order, after `Stores` earlier writes; `Read` and `Own` are the facts
    /// a call's contract needs of the caller's object.</summary>
    sealed record Access(Reached Object, ViewField Field, AccessKind Kind, bool Signed, int Stores,
        string? Value = null, Reached? Target = null);

    /// <summary>A call through a callee's contract: the facts its precondition needs, and the field it writes
    /// as a store of the caller's object, if any.</summary>
    sealed record CallStep(Callee Callee, int Stores, Access[] Needs, Reached[] Live, Access? Writes, int Number);

    /// <summary>A callee the outline states a contract for from its own walk: the facts it needs of its
    /// objects, at most one field it writes, and its result in terms of its arguments and initial memory.</summary>
    sealed record Callee(int Index, string Name, Specification Spec, ObjectWalk Walk, ObjectPlan Plan)
    {
        internal Access? Store =>
            Walk.Steps.OfType<Access>().SingleOrDefault(access => access.Kind == AccessKind.Store);
    }

    /// <summary>A straight-line body as the facts that step it: field loads and stores of the objects it reaches,
    /// calls through their callees' contracts, locals and null tests of objects; null with the reason when it
    /// does more.</summary>
    sealed class ObjectWalk(Specification spec, string[] ops, FieldViews views, Func<int, Callee?> callees)
    {
        internal string? Stopped { get; private set; }
        internal string? Returned { get; private set; }
        internal List<Reached> Objects { get; } = [];
        internal List<object> Steps { get; } = [];

        abstract record Item;
        sealed record Word(string? Term, int Width) : Item;
        sealed record Instance(Reached Object) : Item;
        sealed record Null : Item;

        int stores;
        int calls;

        internal IEnumerable<Access> Accesses => Steps.SelectMany(step => step switch
        {
            Access access => [access],
            CallStep call => call.Needs,
            _ => Enumerable.Empty<Access>()
        });

        internal bool Run(Func<int, string> location)
        {
            foreach (var parameter in spec.Objects) Objects.Add(new Reached(parameter.Name, parameter.Fields));
            var stack = new List<Item>();
            var locals = new Dictionary<int, Item>();
            var visited = new HashSet<int>();
            for (var pc = 0; pc < ops.Length; pc++)
            {
                var op = ops[pc];
                Match match;
                Item? Pop()
                {
                    if (stack.Count == 0) return null;
                    var top = stack[^1];
                    stack.RemoveAt(stack.Count - 1);
                    return top;
                }
                bool Stop(string reason)
                {
                    Stopped = $"{reason} at {location(pc)}";
                    return false;
                }
                if (!visited.Add(pc)) return Stop("a backward jump");
                if ((match = Regex.Match(op, @"\A\.arg (\d+)\z")).Success)
                {
                    var parameter = spec.Parameters[int.Parse(match.Groups[1].Value)];
                    Item? item = parameter.Shape switch
                    {
                        ParameterShape.Object => new Instance(Objects.First(reached => reached.Name == parameter.Name)),
                        ParameterShape.Scalar => new Word(parameter.Name, parameter.Width),
                        _ => null
                    };
                    if (item is null) return Stop($"the argument `{parameter.Name}`, which needs a case split");
                    stack.Add(item);
                }
                else if ((match = Regex.Match(op, @"\A\.setLocal (\d+)\z")).Success)
                {
                    if (Pop() is not { } item) return Stop("a local store of an empty stack");
                    locals[int.Parse(match.Groups[1].Value)] = item;
                }
                else if ((match = Regex.Match(op, @"\A\.local (\d+)\z")).Success)
                {
                    if (!locals.TryGetValue(int.Parse(match.Groups[1].Value), out var item))
                        return Stop("a local the body reads before it stores it");
                    stack.Add(item);
                }
                else if (op == ".nullObject") stack.Add(new Null());
                else if (op == ".dup")
                {
                    if (stack.Count == 0) return Stop("a duplicate of an empty stack");
                    stack.Add(stack[^1]);
                }
                else if (op == ".pop") { if (Pop() is null) return Stop("a pop of an empty stack"); }
                else if ((match = Regex.Match(op, @"\A\.(brzero|brnonzero) (\d+)\z")).Success)
                {
                    // An argument object is never null, so its test always goes one way.
                    var zero = Pop() switch { Instance => false, Null => true, _ => (bool?)null };
                    if (zero is null) return Stop($"`{op}` on a word, which needs a case split");
                    if (zero == (match.Groups[1].Value == "brzero")) pc = int.Parse(match.Groups[2].Value) - 1;
                }
                else if ((match = Regex.Match(op, @"\A\.branch (\d+)\z")).Success)
                    pc = int.Parse(match.Groups[1].Value) - 1;
                else if ((match = Regex.Match(op,
                    @"\A\.const(32|64) (?:(\d+)|\(BitVec\.ofInt \d+ \((-?\d+)\)\))\z")).Success)
                    stack.Add(new Word(match.Groups[2].Success ? match.Groups[2].Value : $"({match.Groups[3].Value})",
                        match.Groups[1].Value == "64" ? 8 : 4));
                else if ((match = Regex.Match(op, @"\A\.(add|sub|mul|band|bor|bxor)\z")).Success)
                {
                    if (Pop() is not Word right || Pop() is not Word left || left.Width != right.Width)
                        return Stop("arithmetic on a value the outline cannot name");
                    var symbol = match.Groups[1].Value switch
                    {
                        "add" => "+", "sub" => "-", "mul" => "*", "band" => "&&&", "bor" => "|||", _ => "^^^"
                    };
                    stack.Add(new Word(left.Term is null || right.Term is null ? null
                        : $"({left.Term} {symbol} {right.Term})", left.Width));
                }
                else if (op is ".convU8" or ".convI8")
                {
                    if (Pop() is not Word { Width: 4 } word)
                        return Stop("a widening of a value the outline cannot name");
                    var widen = op == ".convU8" ? "setWidth" : "signExtend";
                    stack.Add(new Word(word.Term is null ? null : $"({word.Term}.{widen} 64)", 8));
                }
                // Values the steps compute but the outline does not name: they may be returned, not stored.
                else if (Regex.IsMatch(op, @"\A\.(shl|shr|shrUn|div|divUn|rem|remUn|eq|gt|gtu|lt|ltu)\z"))
                {
                    if (Pop() is not Word || Pop() is not Word left)
                        return Stop($"`{op}` on a value that is not a word");
                    stack.Add(new Word(null, op is ".eq" or ".gt" or ".gtu" or ".lt" or ".ltu" ? 4 : left.Width));
                }
                else if ((match = Regex.Match(op, @"\A\.(neg|not|conv[UI][124])\z")).Success)
                {
                    if (Pop() is not Word word) return Stop($"`{op}` on a value that is not a word");
                    stack.Add(new Word(null, op.StartsWith(".conv", StringComparison.Ordinal) ? 4 : word.Width));
                }
                else if (ClassViews.Decode(op) is { Store: false, Reference: false } load)
                {
                    if (Pop() is not Instance instance || Field(instance, load) is not { } field)
                        return Stop("a field load of an object the outline cannot name");
                    var signed = load.Signed;
                    Steps.Add(new Access(instance.Object, field, AccessKind.Load, signed, stores));
                    var term = $"({field.Lean}.of {Memory(stores)} {instance.Object.Name})";
                    stack.Add(field.Width switch
                    {
                        < 4 => new Word($"({term}.{(signed ? "signExtend" : "setWidth")} 32)", 4),
                        _ => new Word(term, field.Width!.Value)
                    });
                }
                else if (ClassViews.Decode(op) is { Store: true, Reference: false } store)
                {
                    var value = Pop();
                    if (Pop() is not Instance instance || Field(instance, store) is not { } field)
                        return Stop("a field store into an object the outline cannot name");
                    if (value is not Word word || word.Width != field.Width)
                        return Stop($"a store into `{field.Lean}` of a value of another width, which the field " +
                            "truncates");
                    if (word.Term is null)
                        return Stop($"a store into `{field.Lean}` of a value the outline does not name");
                    if (instance.Object.Holder is not null)
                        return Stop($"a store into `{field.Lean}` of an object a field holds, which the footprint " +
                            "cannot name");
                    Steps.Add(new Access(instance.Object, field, AccessKind.Store, false, stores++, word.Term));
                }
                else if (ClassViews.Decode(op) is { Store: false, Reference: true } referenceLoad)
                {
                    if (Pop() is not Instance instance || Field(instance, referenceLoad) is not { } field)
                        return Stop("a reference field load of an object the outline cannot name");
                    if (stores > 0)
                        return Stop($"a load of `{field.Lean}` after a store, whose target the statement names " +
                            "in the caller's memory");
                    var reached = Accesses.FirstOrDefault(access => access.Kind == AccessKind.Load &&
                        access.Target is not null && access.Object == instance.Object && access.Field == field)?.Target;
                    if (reached is null)
                    {
                        if (spec.Method.Body.Instructions[pc].Operand is not FieldReference { FieldType: var type } ||
                            !ObjectTypes.Is(type))
                            return Stop($"a load of `{field.Lean}`, whose class the outline cannot name");
                        var name = instance.Object.Name + Capitalized(field.Name);
                        reached = new Reached(name + "Target", views.Of(type), name + "Held", instance.Object.Name);
                        Objects.Add(reached);
                    }
                    Steps.Add(new Access(instance.Object, field, AccessKind.Load, false, stores, Target: reached));
                    stack.Add(new Instance(reached));
                }
                else if (ClassViews.Decode(op) is { Store: true, Reference: true } referenceStore)
                {
                    var value = Pop();
                    if (Pop() is not Instance instance || Field(instance, referenceStore) is not { } field)
                        return Stop("a reference field store into an object the outline cannot name");
                    if (value is not Instance target)
                        return Stop($"a store into `{field.Lean}` of null, which `owned.store` does not take");
                    if (instance.Object.Holder is not null)
                        return Stop($"a store into `{field.Lean}` of an object a field holds, which the footprint " +
                            "cannot name");
                    Steps.Add(new Access(instance.Object, field, AccessKind.Store, false, stores++,
                        Target: target.Object));
                }
                else if ((match = Regex.Match(op, @"\A\.call(?:Instance)? (\d+) (\d+)\z")).Success)
                {
                    var index = int.Parse(match.Groups[1].Value);
                    if (callees(index) is not { } callee)
                        return Stop("a call whose callee the outline cannot state as a contract from its body, " +
                            "which `cil_contract_steps` composes through a contract you write");
                    var arguments = new Item?[callee.Spec.Parameters.Length];
                    for (var position = arguments.Length - 1; position >= 0; position--) arguments[position] = Pop();
                    if (arguments.Any(argument => argument is Word { Term: null }))
                        return Stop($"a call to `{callee.Spec.Method.Name}` with a value the outline does not name");
                    if (Call(callee, arguments) is { } reason) return Stop(reason);
                    if (callee.Walk.Returned is { } returned)
                        stack.Add(new Word(Substitute(returned, callee, arguments, Memory(stores)),
                            callee.Spec.Result is { Constructor: ".i64" } ? 8 : 4));
                    else if (callee.Spec.Result is not null)
                        return Stop($"a call to `{callee.Spec.Method.Name}`, whose result the outline cannot name");
                }
                else if (op == ".nop") { }
                else if (op == ".ret" || op.StartsWith(".ret (some ", StringComparison.Ordinal))
                {
                    if (spec.Result is not null)
                    {
                        var result = Pop();
                        Returned = result switch
                        {
                            Word word when !spec.Result.Boolean && !spec.Result.Object => word.Term,
                            Instance instance when spec.Result.Object => $"(.address {instance.Object.Name})",
                            Null when spec.Result.Object => ".null",
                            _ => null
                        };
                        // A computed word the outline does not name still leaves the result to the postcondition.
                        if (Returned is null && result is not Word { Term: null })
                            return Stop("a result the outline cannot name");
                    }
                    return true;
                }
                else return Stop($"`{op}`, which the outline does not step");
            }
            Stopped = "the end of the body without a return";
            return false;
        }

        /// <summary>Records a call: what its precondition needs of the objects passed, and its store as a store
        /// of the caller's object; the reason when an argument is not one the outline names.</summary>
        string? Call(Callee callee, Item?[] arguments)
        {
            var needs = new List<Access>();
            var live = new List<Reached>();
            Access? writes = null;
            for (var position = 0; position < arguments.Length; position++)
            {
                var parameter = callee.Spec.Parameters[position];
                if (parameter.Shape != ParameterShape.Object) continue;
                if (arguments[position] is not Instance instance)
                    return $"a call to `{callee.Spec.Method.Name}` with an object the outline cannot name";
                live.Add(instance.Object);
                foreach (var access in callee.Walk.Accesses.Where(access =>
                    access.Object.Name == parameter.Name && access.Kind is AccessKind.Load or AccessKind.Store))
                {
                    var field = instance.Object.Fields.FirstOrDefault(field => field.Lean == access.Field.Lean);
                    if (field is null)
                        return $"a call to `{callee.Spec.Method.Name}` on a field the caller cannot name";
                    var owned = callee.Walk.Accesses.Any(other => other.Object == access.Object &&
                        other.Field == access.Field && other.Kind == AccessKind.Store);
                    if (needs.Any(need => need.Object == instance.Object && need.Field == field)) continue;
                    needs.Add(new Access(instance.Object, field, owned ? AccessKind.Own : AccessKind.Read, false,
                        stores));
                }
            }
            if (callee.Store is { } store)
            {
                var position = Array.FindIndex(callee.Spec.Parameters,
                    parameter => parameter.Name == store.Object.Name);
                var owner = ((Instance)arguments[position]!).Object;
                if (owner.Holder is not null)
                    return $"a call to `{callee.Spec.Method.Name}` that writes an object a field holds";
                writes = new Access(owner, owner.Fields.First(field => field.Lean == store.Field.Lean),
                    AccessKind.Store, false, stores,
                    store.Value is null ? null : Substitute(store.Value, callee, arguments, Memory(stores)));
            }
            Steps.Add(new CallStep(callee, stores, [.. needs], [.. live.Distinct()], writes, ++calls));
            if (writes is not null) stores++;
            return null;
        }

        /// <summary>A callee's term over its parameters and initial memory, in the caller's names and memory.</summary>
        static string Substitute(string term, Callee callee, Item?[] arguments, string memory)
        {
            var names = callee.Spec.Parameters.Select((parameter, position) => (parameter.Name,
                Value: arguments[position] switch
                {
                    Word { Term: { } named } => named,
                    Instance instance => instance.Object.Name,
                    _ => parameter.Name
                })).Append(("initial", memory)).ToDictionary(pair => pair.Item1, pair => pair.Item2);
            return Regex.Replace(term, @"(?<![\w.])[A-Za-z_][\w]*(?![\w])",
                found => names.TryGetValue(found.Value, out var value) ? value : found.Value);
        }

        internal static string Memory(int stores) => stores == 0 ? "initial" : $"stored{stores}";

        static ViewField? Field(Instance instance, ClassViews.FieldOperation operation) => instance.Object.Fields
            .FirstOrDefault(field => field.Offset == operation.Offset && field.Width == operation.Width);

        /// <summary>The statement's facts about the reached objects: each is live, a target is what its field
        /// holds, and each field the body touches is `Owned` when it or a callee stores it and `Readable`
        /// otherwise.</summary>
        internal ObjectPlan Plan()
        {
            var plan = new ObjectPlan();
            var all = Accesses.Concat(Steps.OfType<CallStep>().Select(call => call.Writes).OfType<Access>()).ToArray();
            foreach (var reached in Objects)
            {
                if (reached.Holder is not null)
                {
                    plan.Targets.Add(reached.Name);
                    var holder = all.First(access => access.Target == reached && access.Kind == AccessKind.Load);
                    plan.Premises.Add((reached.Held!,
                        $"{holder.Field.Lean}.of initial {holder.Object.Name} = .address {reached.Name}"));
                }
                plan.Premises.Add((reached.Name + "Live", $"LiveObject initial {reached.Name}"));
                foreach (var field in reached.Fields)
                {
                    var touched = all.Where(access => access.Object == reached && access.Field == field).ToArray();
                    if (touched.Length == 0) continue;
                    var owned = touched.Any(access => access.Kind is AccessKind.Store or AccessKind.Own);
                    plan.Premises.Add((Fact(reached, field),
                        $"{field.Lean}.{(owned ? "Owned" : "Readable")} initial {reached.Name}"));
                    if (owned) plan.Entries.Add($"{field.Lean}.entry {reached.Name}");
                }
            }
            return plan;
        }

        internal static string Fact(Reached reached, ViewField field) => reached.Name + Capitalized(field.Name);
    }

    static string Capitalized(string name) => char.ToUpperInvariant(name[0]) + name[1..];

    /// <summary>The contract of a callee whose body the walk steps with no call of its own, no reference field
    /// load and at most one store: `pre` its facts, `post` its store and its result, and its proof.</summary>
    static Callee? Summarize(Extraction extraction, int index, string name, FieldViews views)
    {
        var method = extraction.Methods[index];
        try
        {
            var names = new Names();
            var receiver = method.HasThis ? new[] { Receiver(method, names, views) } : [];
            var parameters = receiver.Concat(method.Parameters.Select(parameter =>
                Describe(method, parameter, names, views))).ToArray();
            if (parameters.Any(parameter => parameter.Shape is not (ParameterShape.Object or ParameterShape.Scalar)))
                return null;
            var spec = new Specification(method, parameters, DescribeResult(method), true, true);
            var walk = new ObjectWalk(spec, extraction.Emitted[index].Ops, views, _ => null);
            if (!walk.Run(_ => "") || walk.Steps.OfType<CallStep>().Any() ||
                walk.Objects.Any(reached => reached.Holder is not null) ||
                walk.Accesses.Count(access => access.Kind == AccessKind.Store) > 1 ||
                (walk.Returned ?? "").Contains("stored", StringComparison.Ordinal) ||
                (spec.Result is not null && walk.Returned is null) ||
                spec.Result is { Boolean: true } or { Object: true })
                return null;
            return new Callee(index, name, spec, walk, walk.Plan());
        }
        catch (NotSupportedException)
        {
            return null;
        }
    }

    /// <summary>A tactic's fact list as parts the writer may wrap after any comma.</summary>
    static IEnumerable<string> FactList(List<string> facts) =>
        facts.Select((fact, index) => (index == 0 ? "[" : "") + fact + (index + 1 < facts.Count ? "," : "]"));

    /// <summary>Writes a callee's contract and the proof that its body meets it.</summary>
    static void CalleeContract(Writer lean, Callee callee, string method)
    {
        var spec = callee.Spec;
        var inputs = spec.Parameters;
        string Pattern(string body) => inputs.Length == 1 ? Used(inputs[0].Name, body)
            : "(" + string.Join(", ", inputs.Select(input => Used(input.Name, body))) + ")";
        string Used(string name, string body) => Regex.IsMatch(body, $@"(?<![\w.]){name}(?!\w)") ? name : "_";
        var inputType = inputs.Length == 1 ? inputs[0].Lean
            : "(" + string.Join(" × ", inputs.Select(input => input.Lean)) + ")";
        var outputType = spec.Result?.Lean ?? "Unit";
        var arguments = "[" + string.Join(", ", inputs.Select(input => input.Shape == ParameterShape.Object
            ? $".object (.address {input.Name})" : $".scalar ({ScalarConstructor(input.Width)} {input.Name})")) + "]";
        var pre = string.Join(" ∧ ", callee.Plan.Premises.Select(premise =>
            Regex.Replace(premise.Statement, @"\binitial\b", "memory")));
        var footprint = "[" + string.Join(", ", callee.Plan.Entries) + "]";
        var store = callee.Store;
        var effects = new List<string>();
        if (store is null) effects.Add("final = initial");
        else effects.Add(store.Field.Width is null
            ? $"{store.Field.Lean}.Holds final {store.Object.Name} (.address {store.Target!.Name})"
            : $"{store.Field.Lean}.Holds final {store.Object.Name} {store.Value}");
        if (callee.Walk.Returned is { } returned) effects.Add($"result = {returned}");
        var post = string.Join(" ∧ ", effects);
        lean.Doc($"`{spec.Method.Name}` as the outline reads its body: it needs the facts of `pre`, writes " +
            "only `footprint` and leaves `post`.");
        lean.Line($"def {callee.Name}Contract : MethodContract {inputType} {outputType} where");
        lean.Line($"  args := fun {Pattern(arguments)} => {arguments}");
        lean.Line(spec.Result is { } result ? $"  results result := [{result.Encode("result")}]" : "  results _ := []");
        lean.Wrapped($"  pre := fun {Pattern(pre)} memory =>", [pre.Length == 0 ? "True" : pre], "");
        lean.Wrapped($"  footprint := fun {Pattern(footprint)} =>", [footprint], "");
        lean.Wrapped($"  post := fun {Pattern(post)} initial final {(spec.Result is null ? "_" : "result")} =>",
            [post], "");
        lean.Line();
        lean.Doc($"`{spec.Method.Name}` meets its contract; callers use only the contract.");
        lean.Line($"theorem {callee.Name}_holds : {callee.Name}Contract.Holds Extracted.program {method} := by");
        var names = inputs.Select(input => input.Name).ToArray();
        var premises = callee.Plan.Premises.Select(premise => premise.Name).ToArray();
        static string Tuple(string[] parts) => parts.Length == 1 ? parts[0] : "⟨" + string.Join(", ", parts) + "⟩";
        lean.Line($"  rintro {Tuple(names)} initial permitted");
        lean.Line($"  dsimp only [{callee.Name}Contract] at *");
        if (premises.Length > 0)
            lean.Line($"  obtain {Tuple(premises)} := permitted");
        var proof = store is null
            ? callee.Walk.Returned is null ? "rfl" : "⟨rfl, rfl⟩"
            : callee.Walk.Returned is null ? "held1" : "⟨held1, rfl⟩";
        ObjectBody(lean, spec, callee.Walk, "simp", $"{(spec.Result is null ? "()" : "_")}, rfl, {proof}");
        lean.Line();
        lean.Line($"#print axioms {callee.Name}_holds");
        lean.Line();
    }

    /// <summary>The proof of a body over objects: each store through `Owned.store`, each call through its
    /// callee's contract, the facts of later accesses carried across the writes before them, and the run
    /// stepped with every access's facts. An entry leaves its postcondition as the hole; a callee's proof
    /// closes its contract's `Returns` with `returns`.</summary>
    static void ObjectBody(Writer lean, Specification spec, ObjectWalk walk, string widen,
        string? returns = null)
    {
        // The name of each fact in the memory after a number of writes, introduced when an access needs it.
        var known = new Dictionary<(string Key, int Stores), string>();
        var stored = new List<Access>();
        foreach (var reached in walk.Objects)
        {
            known[(reached.Name + "Live", 0)] = reached.Name + "Live";
            foreach (var field in reached.Fields) known[(ObjectWalk.Fact(reached, field), 0)] =
                ObjectWalk.Fact(reached, field);
        }
        string Live(Reached reached, int stores) => Carry(reached.Name + "Live", stores, (previous, level) =>
            $"{previous}.after_confined framed{level}");
        string FieldFact(Reached reached, ViewField field, int stores) =>
            Carry(ObjectWalk.Fact(reached, field), stores, (previous, level) =>
            {
                var store = stored[level - 1];
                if (store.Field != field)
                    return $"{previous}.after_confined framed{level} (apart_of_entries rfl)";
                if (store.Object == reached) return $"held{level}.1";
                // The two objects may be one, so `across` splits on whether the store reached this field.
                return $"({previous}.across {Live(store.Object, level - 1)} framed{level} held{level}).1";
            });
        string Carry(string key, int stores, Func<string, int, string> across)
        {
            if (known.TryGetValue((key, stores), out var name)) return name;
            var previous = Carry(key, stores - 1, across);
            var carried = across(previous, stores);
            name = key + stores;
            lean.Line($"  have {name} := {carried}");
            known[(key, stores)] = name;
            return name;
        }
        var facts = walk.Objects.Where(reached => reached.Holder is null)
            .Select(reached => reached.Name + "Live.formed").ToList();
        void Add(string fact)
        {
            if (!facts.Contains(fact)) facts.Add(fact);
        }
        foreach (var step in walk.Steps)
        {
            if (step is CallStep call)
            {
                foreach (var reached in call.Live)
                {
                    Add(Live(reached, call.Stores));
                    Add(Live(reached, call.Stores) + ".formed");
                }
                foreach (var need in call.Needs) Add(FieldFact(need.Object, need.Field, call.Stores));
                Add($"{call.Callee.Name}_holds");
                Add($"{call.Callee.Name}Contract");
                Add("leaveFrame");
                lean.Wrapped("  cil_contract_steps", FactList(facts), "");
                facts.Clear();
                var number = call.Number;
                if (call.Writes is { } writes)
                {
                    var index = writes.Stores + 1;
                    lean.Line($"  rename_i stored{index} framed{index} output{number} held{index} _");
                    lean.Line($"  dsimp only [{call.Callee.Name}Contract] at framed{index} held{index}");
                    stored.Add(writes);
                }
                else
                {
                    lean.Line($"  rename_i called{number} _ output{number} post{number} _");
                    lean.Line($"  dsimp only [{call.Callee.Name}Contract] at post{number}");
                    // The memory after the call is the caller's: keep the name the specification uses.
                    if (call.Callee.Walk.Returned is not null)
                        lean.Line($"  obtain ⟨post{number}, rfl⟩ := post{number}");
                    lean.Line($"  subst called{number}");
                }
                continue;
            }
            var access = (Access)step;
            var fact = FieldFact(access.Object, access.Field, access.Stores);
            if (access.Kind == AccessKind.Load)
            {
                Add(access.Field.Width is null ? $"{fact}.facts {access.Target!.Held} {access.Target.Name}Live"
                    : access.Signed ? fact + ".signedFacts" : fact + ".facts");
                continue;
            }
            var stores = access.Stores + 1;
            if (access.Field.Width is null)
            {
                var target = Live(access.Target!, access.Stores);
                lean.Line($"  obtain ⟨written{stores}, framed{stores}, held{stores}⟩ := {fact}.store {target}");
                lean.Wrapped("  generalize", [$"setSlot {ObjectWalk.Memory(access.Stores)} " +
                    $"({access.Field.Lean}.address {access.Object.Name}) (.address {access.Target!.Name}) = " +
                    $"stored{stores}"], $"at written{stores} framed{stores} held{stores}");
                // The store checks the stored reference is formed in the memory it writes.
                Add(target + ".formed");
            }
            else lean.Wrapped($"  obtain ⟨stored{stores}, written{stores}, framed{stores}, held{stores}⟩ :=",
                [$"{fact}.store {access.Value}"], "");
            Add(fact + ".located");
            Add(Live(access.Object, access.Stores) + ".formed");
            Add($"written{stores}");
            stored.Add(access);
        }
        var widened = Enumerable.Range(1, stored.Count).Select(index => $"(framed{index}.widen (by {widen}))")
            .ToArray();
        var confined = widened.Length == 0 ? "Confined.refl _ _"
            : widened.Skip(1).Aggregate(widened[0], (chain, next) => $"({chain}.trans {next})");
        // The return leaves the method's frame, which owns no caller memory.
        // After a call the steps may already have reached the return.
        Add("leaveFrame");
        lean.Wrapped(walk.Steps.LastOrDefault() is CallStep
            ? "  try cil_contract_steps" : "  cil_contract_steps", FactList(facts), "");
        if (returns is not null)
        {
            lean.Wrapped("  exact", [$"⟨{confined},", returns + "⟩"], "");
            return;
        }
        lean.Wrapped(spec.Result is null ? "  refine ⟨rfl," : "  refine ⟨_, rfl,", [confined + ","], "?_⟩");
        var held = string.Join(", ", Enumerable.Range(1, stored.Count).Select(index => $"`held{index}`"));
        lean.Noted("  ", "sorry", "Postcondition of the returned value" +
            (stored.Count == 0 ? "" : $", with {held} the stored fields"));
    }
}
