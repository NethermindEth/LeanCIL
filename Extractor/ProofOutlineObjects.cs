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
    /// <remarks>A reference store of a value that is not an object the body reaches names it by `Value` and the
    /// fact that it forms by `Formed`.</remarks>
    sealed record Access(Reached Object, ViewField Field, AccessKind Kind, bool Signed, int Stores,
        string? Value = null, Reached? Target = null, string? Formed = null)
    {
        /// <summary>A load of a reference field whose class is outside the model: its value is named, never
        /// read through.</summary>
        internal bool Opaque => Kind == AccessKind.Load && Field.Width is null && Target is null;
    }

    enum ElementKind { Length, Load, Store }

    /// <summary>An access of an array argument: its length, or a load or store of the element at `Index`, a `Nat`
    /// term, whose fact is `Slot`. A store writes `Value`: an object the body reaches as `Target`, null, or a
    /// reference outside the model whose formation `Formed` states.</summary>
    sealed record ElementAccess(string Array, ElementKind Kind, string? Index = null, string? Value = null,
        Reached? Target = null, string? Formed = null, string? Slot = null)
    {
        /// <summary>The premise that the stored object passes the covariance check of the array's element class.
        /// </summary>
        internal string? Storable => Kind == ElementKind.Store && Value != ".null" ? Slot + "Storable" : null;
    }

    /// <summary>A call through a callee's contract: the facts its precondition needs, the field it writes as a
    /// store of the caller's object, if any, and for each object the callee loads from a reference field, the
    /// caller's object that field holds and the fact that says so.</summary>
    sealed record CallStep(Callee Callee, int Stores, Access[] Needs, Reached[] Live, Access? Writes, int Number,
        (Reached Target, string Held)[] Found);

    /// <summary>A test of named words that splits the body: `Fact` names `Condition` on the side that holds it
    /// and its negation on the other, and each side is walked from where it continues to its own return.</summary>
    sealed record Split(string Fact, string Condition, (string Where, ObjectWalk Walk) Holds,
        (string Where, ObjectWalk Walk) Fails);

    /// <summary>A callee the outline states a contract for from its own walk: the facts it needs of its
    /// objects, at most one field it writes, and its result in terms of its arguments, the objects it loads
    /// from reference fields and its initial memory.</summary>
    sealed record Callee(int Index, string Name, Specification Spec, ObjectWalk Walk, ObjectPlan Plan)
    {
        internal Access? Store =>
            Walk.Steps.OfType<Access>().SingleOrDefault(access => access.Kind == AccessKind.Store);

        internal Reached[] Targets => [.. Walk.Objects.Where(reached => reached.Holder is not null)];
    }

    /// <summary>A body without loops as the facts that step it: field loads and stores of the objects it reaches,
    /// calls through their callees' contracts, locals, null tests of objects and splits on tests of named words,
    /// and references to classes outside the model that it loads, compares, tests and stores but never reads
    /// through; null with the reason when it does more.</summary>
    /// <remarks>A `linear` walk reads every op once in order, ignoring where branches go, to find which fields of
    /// which objects a body with loops touches; its steps are not a proof.</remarks>
    sealed class ObjectWalk(Specification spec, string[] ops, FieldViews views, Func<int, Callee?> callees,
        bool linear = false)
    {
        internal string? Stopped { get; private set; }
        internal string? Returned { get; private set; }
        internal List<Reached> Objects { get; private init; } = [];
        internal List<object> Steps { get; } = [];

        abstract record Item;
        sealed record Word(string? Term, int Width) : Item;
        sealed record Instance(Reached Object) : Item;
        sealed record Null : Item;
        /// <summary>A reference to an object outside the model, as the field it was loaded from names it before any
        /// write in a parenthesized `Term`, with the fact that it forms then.</summary>
        sealed record Opaque(string Term, string Formed) : Item;
        /// <summary>An array argument of class references.</summary>
        sealed record ArrayArgument(string Name) : Item;

        /// <summary>The fact naming each element of an array argument the body loads or stores, by array and
        /// index, shared by every path.</summary>
        Dictionary<(string Array, string Index), string> Slots { get; init; } = [];

        /// <summary>The value stored into each element fact, shared by every path.</summary>
        Dictionary<string, string> Stored { get; init; } = [];

        /// <summary>An element store came first, after which the walk takes no further access or call, since
        /// the facts of other fields and elements are not carried across it.</summary>
        bool elementStored;
        int stores;
        int calls;
        int splits;
        object[] previous = [];

        /// <summary>The steps on this path, from the start of the body.</summary>
        IEnumerable<object> PathSteps => previous.Concat(Steps);

        /// <summary>The steps on every path through the body, each side of a split after the steps before it.
        /// </summary>
        internal IEnumerable<object> Flattened => Steps.SelectMany(step => step is Split split
            ? split.Holds.Walk.Flattened.Concat(split.Fails.Walk.Flattened) : new[] { step });

        internal IEnumerable<Access> Accesses => Flattened.SelectMany(step => step switch
        {
            Access access => [access],
            CallStep call => call.Needs,
            _ => Enumerable.Empty<Access>()
        });

        internal bool Run(Func<int, string> location)
        {
            foreach (var parameter in spec.Objects) Objects.Add(new Reached(parameter.Name, parameter.Fields));
            return Walk(0, [], new(), [], location);
        }

        /// <summary>Walks from `start` with the stack, locals and visited pcs of the path that reaches it.</summary>
        bool Walk(int start, List<Item> stack, Dictionary<int, Item> locals, HashSet<int> visited,
            Func<int, string> location)
        {
            for (var pc = start; pc < ops.Length; pc++)
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
                // Walks each side of a test from where it continues, with what the path holds so far.
                bool Branch(string condition, bool takenWhenTrue, int target)
                {
                    var (holds, fails) = takenWhenTrue ? (target, pc + 1) : (pc + 1, target);
                    var walks = new[] { holds, fails }.Select(next => (Next: next, Walk: new ObjectWalk(spec, ops,
                        views, callees, linear) { Objects = Objects, Slots = Slots, Stored = Stored, stores = stores,
                        calls = calls, splits = splits + 1, elementStored = elementStored,
                        previous = [.. PathSteps] })).ToArray();
                    Steps.Add(new Split($"branch{splits + 1}", condition, (location(holds), walks[0].Walk),
                        (location(fails), walks[1].Walk)));
                    foreach (var side in walks)
                        if (!side.Walk.Walk(side.Next, [.. stack], new(locals), [.. visited], location))
                        {
                            Stopped = side.Walk.Stopped;
                            return false;
                        }
                    return true;
                }
                if (!visited.Add(pc)) return Stop("a backward jump");
                if (elementStored && (ClassViews.Decode(op) is not null || op.StartsWith(".memory .referenceArray",
                    StringComparison.Ordinal) || op.StartsWith(".call", StringComparison.Ordinal)))
                    return Stop($"`{op}` after an element store, whose facts the outline does not carry across it");
                if ((match = Regex.Match(op, @"\A\.arg (\d+)\z")).Success)
                {
                    var parameter = spec.Parameters[int.Parse(match.Groups[1].Value)];
                    Item? item = parameter.Shape switch
                    {
                        ParameterShape.Object => new Instance(Objects.First(reached => reached.Name == parameter.Name)),
                        ParameterShape.Scalar => new Word(parameter.Name, parameter.Width),
                        ParameterShape.Array => new ArrayArgument(parameter.Name),
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
                else if (op == ".memory .nullObject") stack.Add(new Null());
                else if (op == ".dup")
                {
                    if (stack.Count == 0) return Stop("a duplicate of an empty stack");
                    stack.Add(stack[^1]);
                }
                else if (op == ".pop") { if (Pop() is null) return Stop("a pop of an empty stack"); }
                else if (linear && Regex.Match(op, @"\A\.(\w+) \d+\z") is { Success: true } jump &&
                    Body.Target(op) is not null)
                {
                    var operands = jump.Groups[1].Value switch { "branch" => 0, "brzero" or "brnonzero" => 1, _ => 2 };
                    for (var operand = 0; operand < operands; operand++)
                        if (Pop() is null) return Stop($"`{op}` on an empty stack");
                }
                else if ((match = Regex.Match(op, @"\A\.(brzero|brnonzero) (\d+)\z")).Success &&
                    stack.Count > 0 && stack[^1] is Opaque)
                {
                    var tested = (Opaque)Pop()!;
                    if (stores > 0) return Stop(Unformed(tested));
                    // `brfalse` takes its target when the reference is null.
                    return Branch($"{tested.Term[1..^1]} = .null", match.Groups[1].Value == "brzero",
                        int.Parse(match.Groups[2].Value));
                }
                else if ((match = Regex.Match(op, @"\A\.(beq|bne) (\d+)\z")).Success && stack.Count > 1 &&
                    (stack[^1] is Opaque || stack[^2] is Opaque))
                {
                    var right = Pop();
                    var left = Pop();
                    if (Compared(left, right) is not { } condition) return Stop(Uncompared(op));
                    return Branch(condition, match.Groups[1].Value == "beq", int.Parse(match.Groups[2].Value));
                }
                else if (op is ".eq" or ".gtu" && stack.Count > 1 && (stack[^1] is Opaque || stack[^2] is Opaque))
                {
                    var right = Pop();
                    var left = Pop();
                    // `cgt.un` on references is defined only against null.
                    if (Compared(left, right) is null || op == ".gtu" && right is not Null)
                        return Stop(Uncompared(op));
                    stack.Add(new Word(null, 4));
                }
                else if ((match = Regex.Match(op, @"\A\.(brzero|brnonzero) (\d+)\z")).Success &&
                    stack.Count > 0 && stack[^1] is not Word)
                {
                    // An argument object is never null, so its test always goes one way.
                    var zero = Pop() is Null;
                    if (zero == (match.Groups[1].Value == "brzero")) pc = int.Parse(match.Groups[2].Value) - 1;
                }
                else if (Body.Conditional(op))
                {
                    var name = Regex.Match(op, @"\A\.(\w+)").Groups[1].Value;
                    var operands = new Word?[name is "brzero" or "brnonzero" ? 1 : 2];
                    for (var position = operands.Length - 1; position >= 0; position--)
                        operands[position] = Pop() as Word;
                    if (operands.Any(operand => operand?.Term is null) ||
                        operands.Any(operand => operand!.Width != operands[0]!.Width))
                        return Stop($"`{op}` on a value the outline does not name");
                    var (condition, takenWhenTrue) = Body.Test(name, [.. operands.Select(operand => operand!.Term!)]);
                    return Branch(condition, takenWhenTrue, Body.Target(op)!.Value);
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
                    if (word.Term is null && !linear)
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
                    var held = spec.Method.Body.Instructions[pc].Operand is FieldReference { FieldType: var type }
                        ? type : null;
                    if (held is not null && ObjectTypes.Opaque(held))
                    {
                        if (stores > 0)
                            return Stop($"a load of `{field.Lean}` after a store, whose reference the statement " +
                                "forms only in the caller's memory");
                        Steps.Add(new Access(instance.Object, field, AccessKind.Load, false, stores));
                        stack.Add(new Opaque($"({field.Lean}.of initial {instance.Object.Name})",
                            Fact(instance.Object, field) + "Forms.formed"));
                        continue;
                    }
                    if (stores > 0)
                        return Stop($"a load of `{field.Lean}` after a store, whose target the statement names " +
                            "in the caller's memory");
                    // Loads of one field on any path reach one target, since no store comes before them.
                    var name = instance.Object.Name + Capitalized(field.Name);
                    var reached = Objects.FirstOrDefault(other => other.Name == name + "Target");
                    if (reached is null)
                    {
                        if (held is null || !ObjectTypes.Is(held))
                            return Stop($"a load of `{field.Lean}`, whose class the outline cannot name");
                        reached = new Reached(name + "Target", views.Of(held), name + "Held", instance.Object.Name);
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
                    if (instance.Object.Holder is not null)
                        return Stop($"a store into `{field.Lean}` of an object a field holds, which the footprint " +
                            "cannot name");
                    if (value is Opaque { } late && stores > 0) return Stop(Unformed(late));
                    Access? stored = value switch
                    {
                        Instance target => new(instance.Object, field, AccessKind.Store, false, stores,
                            Target: target.Object),
                        Null => new(instance.Object, field, AccessKind.Store, false, stores, ".null", Formed: "rfl"),
                        Opaque opaque => new(instance.Object, field, AccessKind.Store, false, stores, opaque.Term,
                            Formed: opaque.Formed),
                        _ => null
                    };
                    if (stored is null)
                        return Stop($"a store into `{field.Lean}` of a value the outline cannot name");
                    Steps.Add(stored);
                    stores++;
                }
                else if ((match = Regex.Match(op, @"\A\.call(?:Instance)? (\d+) (\d+)\z")).Success)
                {
                    var index = int.Parse(match.Groups[1].Value);
                    if (callees(index) is not { } callee)
                        return Stop("a call whose callee the outline cannot state as a contract from its body, " +
                            "which `cil_contract_steps` composes through a contract you write");
                    var arguments = new Item?[callee.Spec.Parameters.Length];
                    for (var position = arguments.Length - 1; position >= 0; position--) arguments[position] = Pop();
                    if (arguments.Any(argument => argument is Word { Term: null }) && !linear)
                        return Stop($"a call to `{callee.Spec.Method.Name}` with a value the outline does not name");
                    if (Call(callee, arguments) is { } reason) return Stop(reason);
                    if (callee.Walk.Returned is { } returned)
                        stack.Add(new Word(Substitute(returned, callee, arguments, Memory(stores),
                            ((CallStep)Steps[^1]).Found), callee.Spec.Result is { Constructor: ".i64" } ? 8 : 4));
                    else if (callee.Spec.Result is not null && !linear)
                        return Stop($"a call to `{callee.Spec.Method.Name}`, whose result the outline cannot name");
                    else if (callee.Spec.Result is not null)
                        stack.Add(new Word(null, callee.Spec.Result is { Constructor: ".i64" } ? 8 : 4));
                }
                else if (op == ".memory .referenceArrayLength")
                {
                    if (Pop() is not ArrayArgument array) return Stop("`ldlen` of an array the outline cannot name");
                    if (stores > 0) return Stop(Unwritten(op));
                    Steps.Add(new ElementAccess(array.Name, ElementKind.Length));
                    stack.Add(new Word($"(BitVec.ofNat 64 {array.Name}Length)", 8));
                }
                else if (op == ".memory .referenceArrayLoad")
                {
                    if (Pop() is not Word index || Pop() is not ArrayArgument array || Index(index) is not { } at)
                        return Stop("`ldelem.ref` of an array or index the outline cannot name");
                    if (stores > 0) return Stop(Unwritten(op));
                    var slot = Slot(array.Name, at);
                    Steps.Add(new ElementAccess(array.Name, ElementKind.Load, at, Slot: slot));
                    stack.Add(new Opaque($"(ReferenceArray.of initial {array.Name} {at})", slot + "Forms.formed"));
                }
                else if (op == ".memory .referenceArrayStore")
                {
                    var value = Pop();
                    if (Pop() is not Word index || Pop() is not ArrayArgument array || Index(index) is not { } at)
                        return Stop("`stelem.ref` into an array or at an index the outline cannot name");
                    if (stores > 0) return Stop(Unwritten(op));
                    var slot = Slot(array.Name, at);
                    ElementAccess? stored = value switch
                    {
                        Instance target => new(array.Name, ElementKind.Store, at, $"(.address {target.Object.Name})",
                            target.Object, Slot: slot),
                        Null => new(array.Name, ElementKind.Store, at, ".null", Slot: slot),
                        Opaque opaque => new(array.Name, ElementKind.Store, at, opaque.Term, Formed: opaque.Formed,
                            Slot: slot),
                        _ => null
                    };
                    if (stored is null) return Stop("`stelem.ref` of a value the outline cannot name");
                    // One premise names what each element's store must pass, so every path stores the same value.
                    if (Stored.TryGetValue(slot, out var other) && other != stored.Value)
                        return Stop($"a second value stored into `{slot}`, which the statement names one store of");
                    Stored[slot] = stored.Value!;
                    Steps.Add(stored);
                    stores++;
                    elementStored = true;
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
                            Opaque opaque when spec.Result.Object => opaque.Term,
                            Null when spec.Result.Object => ".null",
                            _ => null
                        };
                        // A computed word the outline does not name still leaves the result to the postcondition.
                        if (Returned is null && result is not Word { Term: null })
                            return Stop("a result the outline cannot name");
                    }
                    if (!linear) return true;
                }
                else return Stop($"`{op}`, which the outline does not step");
            }
            if (linear) return true;
            Stopped = "the end of the body without a return";
            return false;
        }

        /// <summary>Records a call: what its precondition needs of the objects passed and of those their
        /// reference fields hold, and its store as a store of the caller's object; the reason when an argument
        /// or a held object is not one the outline names.</summary>
        string? Call(Callee callee, Item?[] arguments)
        {
            var name = callee.Spec.Method.Name;
            var needs = new List<Access>();
            var live = new List<Reached>();
            var found = new List<(Reached, string)>();
            var objects = new Dictionary<Reached, Reached>();
            Access? writes = null;
            string? Need(Reached reached, Reached passed)
            {
                foreach (var access in callee.Walk.Accesses.Where(access =>
                    access.Object == reached && access.Kind is AccessKind.Load or AccessKind.Store))
                {
                    var field = passed.Fields.FirstOrDefault(field => field.Lean == access.Field.Lean);
                    if (field is null) return $"a call to `{name}` on a field the caller cannot name";
                    var owned = callee.Walk.Accesses.Any(other => other.Object == access.Object &&
                        other.Field == access.Field && other.Kind == AccessKind.Store);
                    if (needs.Any(need => need.Object == passed && need.Field == field)) continue;
                    needs.Add(new Access(passed, field, owned ? AccessKind.Own : AccessKind.Read, false, stores));
                }
                live.Add(passed);
                objects[reached] = passed;
                return null;
            }
            for (var position = 0; position < arguments.Length; position++)
            {
                var parameter = callee.Spec.Parameters[position];
                if (parameter.Shape != ParameterShape.Object) continue;
                if (arguments[position] is not Instance instance)
                    return $"a call to `{name}` with an object the outline cannot name";
                if (Need(callee.Walk.Objects.First(reached => reached.Name == parameter.Name), instance.Object)
                    is { } reason) return reason;
            }
            foreach (var target in callee.Targets)
            {
                var load = callee.Walk.Accesses.First(access => access.Target == target);
                var holder = objects[load.Object];
                var field = holder.Fields.FirstOrDefault(field => field.Lean == load.Field.Lean);
                if (field is null || Holding(holder, field, target.Fields) is not { } holding)
                    return $"a call to `{name}` that loads `{load.Field.Lean}`, whose object the caller names " +
                        "only before any write or right after storing it";
                if (holding.Bound)
                    needs.Add(new Access(holder, field, AccessKind.Load, false, stores, Target: holding.Target));
                if (Need(target, holding.Target) is { } reason) return reason;
                found.Add((holding.Target, holding.Held));
            }
            if (callee.Store is { } store)
            {
                var owner = objects[store.Object];
                if (owner.Holder is not null) return $"a call to `{name}` that writes an object a field holds";
                writes = new Access(owner, owner.Fields.First(field => field.Lean == store.Field.Lean),
                    AccessKind.Store, false, stores,
                    store.Value is null ? null : Substitute(store.Value, callee, arguments, Memory(stores), []),
                    store.Target is null ? null : objects[store.Target]);
            }
            Steps.Add(new CallStep(callee, stores, [.. needs], [.. live.Distinct()], writes, ++calls, [.. found]));
            if (writes is not null) stores++;
            return null;
        }

        /// <summary>The object `holder`'s reference `field` holds in the current memory and the fact that says
        /// so: the last write's when it stored that field, or before any write a target the statement binds.
        /// </summary>
        (Reached Target, string Held, bool Bound)? Holding(Reached holder, ViewField field, ViewField[] fields)
        {
            if (stores > 0)
            {
                var last = PathSteps.Select(step => step switch
                {
                    Access { Kind: AccessKind.Store } access => access,
                    CallStep call => call.Writes,
                    _ => null
                }).OfType<Access>().LastOrDefault();
                return last is { Target: { } stored } && last.Object == holder && last.Field == field
                    ? (stored, $"held{stores}.2", false) : null;
            }
            var name = holder.Name + Capitalized(field.Name);
            var reached = Objects.FirstOrDefault(other => other.Name == name + "Target");
            if (reached is null)
                Objects.Add(reached = new Reached(name + "Target", fields, name + "Held", holder.Name));
            return (reached, reached.Held!, true);
        }

        /// <summary>A callee's term over its parameters, the objects it loads and its initial memory, in the
        /// caller's names and memory.</summary>
        static string Substitute(string term, Callee callee, Item?[] arguments, string memory,
            (Reached Target, string Held)[] found)
        {
            var names = callee.Spec.Parameters.Select((parameter, position) => (parameter.Name,
                Value: arguments[position] switch
                {
                    Word { Term: { } named } => named,
                    Instance instance => instance.Object.Name,
                    _ => parameter.Name
                })).Concat(callee.Targets.Zip(found, (target, passed) => (target.Name, passed.Target.Name)))
                .Append(("initial", memory)).ToDictionary(pair => pair.Item1, pair => pair.Item2);
            return Regex.Replace(term, @"(?<![\w.])[A-Za-z_][\w]*(?![\w])",
                match => names.TryGetValue(match.Value, out var value) ? value : match.Value);
        }

        internal static string Memory(int stores) => stores == 0 ? "initial" : $"stored{stores}";

        static string Unformed(Opaque opaque) =>
            $"a use of `{opaque.Term}` after a store, whose reference the statement forms only in the caller's memory";

        static string Unwritten(string op) =>
            $"`{op}` after a store, whose array facts the statement states only of the caller's memory";

        /// <summary>The element number a named int32 index selects, as the CLR reads it: unsigned.</summary>
        static string? Index(Word index) => index switch
        {
            { Width: not 4 } or { Term: null } => null,
            { Term: var term } when Regex.IsMatch(term, @"\A\d+\z") => term,
            { Term: var term } when term.StartsWith("(-", StringComparison.Ordinal) => null,
            { Term: var term } => term + ".toNat"
        };

        /// <summary>The fact naming element `index` of `array`, numbered in the order the body reaches them.
        /// </summary>
        string Slot(string array, string index)
        {
            if (Slots.TryGetValue((array, index), out var name)) return name;
            name = $"{array}Slot{Slots.Keys.Count(key => key.Array == array) + 1}";
            Slots[(array, index)] = name;
            return name;
        }

        static string Uncompared(string op) => $"`{op}` of a reference with a value the outline cannot name";

        /// <summary>The equation a reference test decides, or null when an operand is not a reference the outline
        /// names or a store has come first, since the statement forms each reference in the caller's memory.
        /// </summary>
        string? Compared(Item? left, Item? right)
        {
            if (stores > 0) return null;
            static string? Term(Item? item) => item switch
            {
                Opaque opaque => opaque.Term[1..^1],
                Null => ".null",
                Instance instance => $"(.address {instance.Object.Name})",
                _ => null
            };
            // The opaque operand comes first, so the equation elaborates at `ManagedReference`.
            return (Term(left), Term(right)) is ({ } first, { } second)
                ? left is Opaque ? $"{first} = {second}" : $"{second} = {first}" : null;
        }

        static ViewField? Field(Instance instance, ClassViews.FieldOperation operation) => instance.Object.Fields
            .FirstOrDefault(field => field.Offset == operation.Offset && field.Width == operation.Width);

        /// <summary>The statement's facts about the reached objects: each is live, a target is what its field
        /// holds, and each field the body touches is `Owned` when it or a callee stores it and `Readable`
        /// otherwise.</summary>
        IEnumerable<Access> Touches =>
            Accesses.Concat(Flattened.OfType<CallStep>().Select(call => call.Writes).OfType<Access>());

        /// <summary>Whether the statement asks `Owned` of the field: the body or a callee stores it.</summary>
        internal bool Owns(Reached reached, ViewField field) => Touches.Any(access => access.Object == reached &&
            access.Field == field && access.Kind is AccessKind.Store or AccessKind.Own);

        internal ObjectPlan Plan()
        {
            var plan = new ObjectPlan();
            var all = Touches.ToArray();
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
                    if (touched.Any(access => access.Opaque))
                        plan.Premises.Add((Fact(reached, field) + "Forms",
                            $"{field.Lean}.Forms initial {reached.Name}"));
                }
            }
            var elements = Flattened.OfType<ElementAccess>().ToArray();
            foreach (var array in spec.Arrays)
            {
                var shape = $"{array.Name} {array.ElementName} {array.LengthName}";
                var touched = elements.Where(access => access.Array == array.Name && access.Slot is not null)
                    .GroupBy(access => access.Slot!).ToArray();
                if (touched.Length == 0)
                    plan.Premises.Add((array.Name + "Live", $"ReferenceArray.Live initial {shape}"));
                foreach (var slot in touched)
                {
                    var index = slot.First().Index;
                    var owned = slot.Any(access => access.Kind == ElementKind.Store);
                    plan.Premises.Add((slot.Key,
                        $"ReferenceArray.{(owned ? "Owned" : "Readable")} initial {shape} {index}"));
                    if (slot.Any(access => access.Kind == ElementKind.Load))
                        plan.Premises.Add((slot.Key + "Forms", $"ReferenceArray.Forms initial {array.Name} {index}"));
                    if (slot.FirstOrDefault(access => access.Storable is not null) is { } store)
                        plan.Premises.Add((store.Storable!,
                            $"storableIn initial {array.ElementName} {store.Value} = .ok ()"));
                    if (owned) plan.Entries.Add($"ReferenceArray.entry {array.Name} {index}");
                }
            }
            return plan;
        }

        internal static string Fact(Reached reached, ViewField field) => reached.Name + Capitalized(field.Name);

        /// <summary>The fact an array argument's location and formation are read from: its first element
        /// fact, or its `Live` premise when the body touches no element.</summary>
        internal string ArrayFact(string array) => Flattened.OfType<ElementAccess>()
            .FirstOrDefault(access => access.Array == array && access.Slot is not null)?.Slot ?? array + "Live";
    }

    static string Capitalized(string name) => char.ToUpperInvariant(name[0]) + name[1..];

    /// <summary>The contract of a callee whose body the walk steps with no call of its own and at most one store,
    /// or reference field loads and no store: `pre` its facts, `post` its store and its result, and its proof.
    /// </summary>
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
            // A contract states reference stores only of objects the callee reaches, and its caller cannot give
            // it the premise that a reference outside the model forms.
            if (!walk.Run(_ => "") || walk.Steps.Any(step => step is CallStep or Split) ||
                walk.Accesses.Any(access => access.Opaque || access.Kind == AccessKind.Store &&
                    access.Field.Width is null && access.Target is null) ||
                walk.Accesses.Count(access => access.Kind == AccessKind.Store) >
                    (walk.Objects.Any(reached => reached.Holder is not null) ? 0 : 1) ||
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

    /// <summary>Gives a body with a loop the premises of the fields it and its callees touch of each object
    /// argument, `Owned` only where one of them stores, when a linear walk reads the whole body; otherwise the
    /// statement keeps a fact of every named field.</summary>
    static void LoopPlan(Extraction extraction, Specification spec, Body body)
    {
        if (!spec.Parameters.Any(parameter => parameter.Shape == ParameterShape.Object)) return;
        var views = new FieldViews(extraction);
        var names = new Names();
        var summaries = new Dictionary<int, Callee?>();
        Callee? Summary(int index) => summaries.TryGetValue(index, out var known) ? known
            : summaries[index] = Summarize(extraction, index, names.Claim("callee" + index, "callee" + index), views);
        var walk = new ObjectWalk(spec, body.Ops, views, Summary, linear: true);
        if (walk.Run(pc => Location(spec.Method, pc)) && walk.Objects.All(reached => reached.Holder is null))
            spec.Plan = walk.Plan();
    }

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
        // An object a reference field holds is not an argument: `pre` asks that one exists, and `post` speaks of
        // whichever the field holds, so a caller names it by the fact that its own field holds it.
        var targets = callee.Targets;
        var premises = callee.Plan.Premises;
        var bound = premises.FindIndex(premise => targets.Any(target => target.Held == premise.Name));
        string Conjunction(IEnumerable<(string Name, string Statement)> parts) => string.Join(" ∧ ",
            parts.Select(premise => Regex.Replace(premise.Statement, @"\binitial\b", "memory")));
        var binders = string.Join(" ", targets.Select(target => target.Name));
        var pre = bound < 0 ? Conjunction(premises)
            : $"{Conjunction(premises.Take(bound))} ∧ ∃ {binders}, {Conjunction(premises.Skip(bound))}";
        var footprint = "[" + string.Join(", ", callee.Plan.Entries) + "]";
        var store = callee.Store;
        var effects = new List<string>();
        if (store is null) effects.Add("final = initial");
        else effects.Add(store.Field.Width is null
            ? $"{store.Field.Lean}.Holds final {store.Object.Name} (.address {store.Target!.Name})"
            : $"{store.Field.Lean}.Holds final {store.Object.Name} {store.Value}");
        var held = targets.Select(target => premises.First(premise => premise.Name == target.Held).Statement)
            .ToArray();
        if (callee.Walk.Returned is { } returned)
            effects.Add(string.Concat(targets.Select((target, position) => $"∀ {target.Name}, {held[position]} → "))
                + $"result = {returned}");
        var post = string.Join(" ∧ ", effects);
        lean.Doc($"`{spec.Method.Name}` as the outline reads its body: it needs the facts of `pre`, writes " +
            "only `footprint` and leaves `post`.");
        lean.Line($"def {callee.Name}Contract : MethodContract {inputType} {outputType} where");
        lean.Line($"  args := fun {Pattern(arguments)} => {arguments}");
        lean.Line(spec.Result is { } result ? $"  results result := [{result.Encode("result")}]" : "  results _ := []");
        // A term that fits on its own continuation line stays whole; a longer one breaks at its spaces.
        static string[] Parts(string term) => term.Length + 6 <= 100 ? [term] : term.Split(' ');
        lean.Wrapped($"  pre := fun {Pattern(pre)} memory =>", Parts(pre.Length == 0 ? "True" : pre), "");
        lean.Wrapped($"  footprint := fun {Pattern(footprint)} =>", [footprint], "");
        lean.Wrapped($"  post := fun {Pattern(post)} {Used("initial", post)} final " +
            $"{(spec.Result is null ? "_" : "result")} =>", Parts(post), "");
        lean.Line();
        lean.Doc($"`{spec.Method.Name}` meets its contract; callers use only the contract.");
        lean.Line($"theorem {callee.Name}_holds : {callee.Name}Contract.Holds Extracted.program {method} := by");
        var names = inputs.Select(input => input.Name).ToArray();
        var obtained = premises.Select(premise => premise.Name).ToList();
        if (bound >= 0) obtained.InsertRange(bound, targets.Select(target => target.Name));
        static string Tuple(IList<string> parts) =>
            parts.Count == 1 ? parts[0] : "⟨" + string.Join(", ", parts) + "⟩";
        lean.Line($"  rintro {Tuple(names)} initial permitted");
        lean.Line($"  dsimp only [{callee.Name}Contract] at *");
        if (obtained.Count == 1) lean.Line($"  obtain {obtained[0]} := permitted");
        else if (obtained.Count > 1)
            lean.Wrapped("  obtain", obtained.Select((part, index) => (index == 0 ? "⟨" : "") + part +
                (index + 1 < obtained.Count ? "," : "⟩ :=")), "permitted");
        var resulting = targets.Length > 0 ? "?_" : "rfl";
        var proof = store is null
            ? callee.Walk.Returned is null ? "rfl" : $"⟨rfl, {resulting}⟩"
            : callee.Walk.Returned is null ? "held1" : $"⟨held1, {resulting}⟩";
        ObjectBody(lean, spec, callee.Walk, "simp", $"{(spec.Result is null ? "()" : "_")}, rfl, {proof}");
        if (callee.Walk.Returned is not null && targets.Length > 0)
        {
            // The field holds one object, so each one `post` names is the one the proof obtained.
            lean.Line("  intro " + string.Join(" ", targets.Select((_, position) => $"_ found{position + 1}")));
            for (var position = 0; position < targets.Length; position++)
                lean.Line($"  cases {targets[position].Held}.symm.trans found{position + 1}");
            lean.Line("  rfl");
        }
        lean.Line();
        lean.Line($"#print axioms {callee.Name}_holds");
        lean.Line();
    }

    /// <summary>The proof of a body over objects: each store through `Owned.store`, each call through its
    /// callee's contract, the facts of later accesses carried across the writes before them, each split by
    /// cases on its test, and each path's run stepped with every access's facts. An entry leaves each path's
    /// postcondition as a hole; a callee's proof closes its contract's `Returns` with `returns`.</summary>
    static void ObjectBody(Writer lean, Specification spec, ObjectWalk walk, string widen,
        string? returns = null)
    {
        var known = new Dictionary<(string Key, int Stores), string>();
        foreach (var reached in walk.Objects)
        {
            known[(reached.Name + "Live", 0)] = reached.Name + "Live";
            foreach (var field in reached.Fields) known[(ObjectWalk.Fact(reached, field), 0)] =
                ObjectWalk.Fact(reached, field);
        }
        var facts = walk.Objects.Where(reached => reached.Holder is null)
            .Select(reached => reached.Name + "Live.formed")
            .Concat(spec.Arrays.Select(array => walk.ArrayFact(array.Name) + ".formed")).ToList();
        new ObjectPath(lean, spec, walk.Owns, walk.ArrayFact, widen, returns, "  ", known, [], facts, [])
            .Write(walk);
    }

    /// <summary>One path of an object body's proof from where its walk starts, `indent` deep: `known` names
    /// each fact in the memory after a number of writes, `stored` holds the writes so far, `facts` those not
    /// yet given to a step and `branches` the sides of the splits taken.</summary>
    sealed class ObjectPath(Writer lean, Specification spec, Func<Reached, ViewField, bool> owns,
        Func<string, string> arrayFact, string widen, string? returns, string indent,
        Dictionary<(string Key, int Stores), string> known, List<object> stored, List<string> facts,
        List<string> branches)
    {
        string Live(Reached reached, int stores) => Carry(reached.Name + "Live", stores, (previous, level) =>
            $"{previous}.after_confined framed{level}");

        string FieldFact(Reached reached, ViewField field, int stores) =>
            Carry(ObjectWalk.Fact(reached, field), stores, (previous, level) =>
            {
                // The walk takes no field access after an element store, so each earlier write is a field's.
                var store = (Access)stored[level - 1];
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
            lean.Line($"{indent}have {name} := {carried}");
            known[(key, stores)] = name;
            return name;
        }

        void Add(string fact)
        {
            if (!facts.Contains(fact)) facts.Add(fact);
        }

        internal void Write(ObjectWalk walk)
        {
            foreach (var step in walk.Steps)
            {
                if (step is Split split)
                {
                    // Each side keeps the facts introduced before the split and adds its own after it.
                    lean.Line($"{indent}by_cases {split.Fact} : {split.Condition}");
                    foreach (var (where, side, outcome) in new[] { (split.Holds.Where, split.Holds.Walk, "holds"),
                        (split.Fails.Where, split.Fails.Walk, "fails") })
                    {
                        lean.Line($"{indent}· -- `{split.Fact}` {outcome}: continues at {where}");
                        new ObjectPath(lean, spec, owns, arrayFact, widen, returns, indent + "  ", new(known),
                            [.. stored], [.. facts, split.Fact], [.. branches, $"`{split.Fact}` {outcome}"])
                            .Write(side);
                    }
                    return;
                }
                if (step is CallStep call)
                {
                    Call(call);
                    continue;
                }
                if (step is ElementAccess element)
                {
                    Element(element);
                    continue;
                }
                Access((Access)step);
            }
            Return(walk);
        }

        /// <summary>An array argument's length or element access, before any other write.</summary>
        void Element(ElementAccess access)
        {
            var slot = access.Slot;
            if (access.Kind == ElementKind.Length)
            {
                Add(arrayFact(access.Array) + ".located");
                return;
            }
            if (access.Kind == ElementKind.Load)
            {
                // The load pushes the element as it is, so later tests and stores need it to form.
                Add($"({slot}.facts_forms {slot}Forms).1");
                Add($"({slot}.facts_forms {slot}Forms).2");
                Add(slot + "Forms.formed");
                return;
            }
            var number = stored.Count + 1;
            var obtained = access switch
            {
                { Target: { } target } => $"{slot}.store {Live(target, 0)} {access.Storable}",
                { Value: ".null" } => $"{slot}.store_null",
                _ => $"{slot}.store_formed {access.Formed} {access.Storable}"
            };
            lean.Wrapped($"{indent}obtain ⟨located{number}, checked{number}, written{number}, framed{number}, " +
                $"held{number}⟩ :=", [obtained], "");
            lean.Wrapped($"{indent}generalize",
                ["setSlot initial", $"(ReferenceArray.slot {access.Array} {access.Index})", access.Value!,
                    $"= stored{number}"], $"at written{number} framed{number} held{number}");
            if (access.Target is { } reached) Add(Live(reached, 0) + ".formed");
            else if (access.Formed is { } formed) Add(formed);
            Add($"located{number}");
            Add($"checked{number}");
            Add($"written{number}");
            stored.Add(access);
        }

        void Call(CallStep call)
        {
            foreach (var reached in call.Live)
            {
                Add(Live(reached, call.Stores));
                Add(Live(reached, call.Stores) + ".formed");
            }
            foreach (var need in call.Needs)
            {
                // A callee that only reads a field asks `Readable` of it, even where the caller owns it.
                var fact = FieldFact(need.Object, need.Field, call.Stores);
                Add(need.Kind == AccessKind.Read && owns(need.Object, need.Field) ? fact + ".toReadable" : fact);
            }
            foreach (var (_, held) in call.Found) Add(held);
            Add($"{call.Callee.Name}_holds");
            Add($"{call.Callee.Name}Contract");
            Add("leaveFrame");
            lean.Wrapped($"{indent}cil_contract_steps", FactList(facts), "");
            facts.Clear();
            var number = call.Number;
            if (call.Writes is { } writes)
            {
                var index = writes.Stores + 1;
                lean.Line($"{indent}rename_i stored{index} framed{index} output{number} held{index} _");
                lean.Line($"{indent}dsimp only [{call.Callee.Name}Contract] at framed{index} held{index}");
                stored.Add(writes);
                return;
            }
            lean.Line($"{indent}rename_i called{number} _ output{number} post{number} _");
            lean.Line($"{indent}dsimp only [{call.Callee.Name}Contract] at post{number}");
            // The memory after the call is the caller's: keep the name the specification uses.
            if (call.Callee.Walk.Returned is not null && call.Found.Length > 0)
            {
                // The result is stated of whatever objects the fields hold: those the caller's facts name.
                lean.Line($"{indent}obtain ⟨post{number}, returned{number}⟩ := post{number}");
                lean.Wrapped($"{indent}have returned{number} := returned{number}",
                    call.Found.SelectMany(found => new[] { found.Target.Name, found.Held }), "");
                lean.Line($"{indent}subst returned{number}");
            }
            else if (call.Callee.Walk.Returned is not null)
                lean.Line($"{indent}obtain ⟨post{number}, rfl⟩ := post{number}");
            lean.Line($"{indent}subst called{number}");
        }

        void Access(Access access)
        {
            var fact = FieldFact(access.Object, access.Field, access.Stores);
            if (access.Opaque)
            {
                // The load pushes the reference as it is, so later tests and stores need it to form.
                var forms = fact + "Forms";
                Add(fact + ".located");
                Add($"{fact}.load_forms {forms}");
                Add(forms + ".formed");
                return;
            }
            if (access.Kind == AccessKind.Load)
            {
                Add(access.Field.Width is null ? $"{fact}.facts {access.Target!.Held} {access.Target.Name}Live"
                    : access.Signed ? fact + ".signedFacts" : fact + ".facts");
                return;
            }
            var stores = access.Stores + 1;
            if (access.Field.Width is null)
            {
                var target = access.Target is { } reached ? Live(reached, access.Stores) : null;
                var value = access.Target is { } named ? $"(.address {named.Name})" : access.Value!;
                lean.Line($"{indent}obtain ⟨written{stores}, framed{stores}, held{stores}⟩ := " + (target is null
                    ? $"{fact}.store_formed {(access.Formed == "rfl" ? $"(value := {value}) rfl" : access.Formed)}"
                    : $"{fact}.store {target}"));
                lean.Wrapped($"{indent}generalize", [$"setSlot {ObjectWalk.Memory(access.Stores)}",
                    $"({access.Field.Lean}.address {access.Object.Name})", value, $"= stored{stores}"],
                    $"at written{stores} framed{stores} held{stores}");
                // The store checks the stored reference is formed in the memory it writes.
                if (target is not null) Add(target + ".formed");
                else if (access.Formed != "rfl") Add(access.Formed!);
            }
            else lean.Wrapped($"{indent}obtain ⟨stored{stores}, written{stores}, framed{stores}, held{stores}⟩ :=",
                [$"{fact}.store {access.Value}"], "");
            Add(fact + ".located");
            Add(Live(access.Object, access.Stores) + ".formed");
            Add($"written{stores}");
            stored.Add(access);
        }

        void Return(ObjectWalk walk)
        {
            var widened = Enumerable.Range(1, stored.Count).Select(index => $"(framed{index}.widen (by {widen}))")
                .ToArray();
            var confined = widened.Length == 0 ? "Confined.refl _ _"
                : widened.Skip(1).Aggregate(widened[0], (chain, next) => $"({chain}.trans {next})");
            // A returned object must still form in the memory the last store left.
            if (walk.Objects.FirstOrDefault(reached => $"(.address {reached.Name})" == walk.Returned) is { } result)
                Add(Live(result, stored.Count) + ".formed");
            // The return leaves the method's frame, which owns no caller memory.
            // After a call the steps may already have reached the return.
            Add("leaveFrame");
            lean.Wrapped(walk.Steps.LastOrDefault() is CallStep
                ? $"{indent}try cil_contract_steps" : $"{indent}cil_contract_steps", FactList(facts), "");
            if (returns is not null)
            {
                lean.Wrapped(returns.Contains("?_", StringComparison.Ordinal) ? $"{indent}refine" : $"{indent}exact",
                    [$"⟨{confined},", returns + "⟩"], "");
                return;
            }
            var boolean = spec.Result is { Boolean: true };
            lean.Wrapped(spec.Result is null ? $"{indent}refine ⟨rfl,"
                : boolean ? $"{indent}refine ⟨?result, ?encoded," : $"{indent}refine ⟨_, rfl,",
                [confined + ","], "?_⟩");
            if (boolean)
            {
                // The returned word is computed, not named, so the author chooses the Bool it encodes.
                lean.Noted(indent, "case result => sorry", "the Bool the returned word encodes");
                lean.Noted(indent, "case encoded => sorry", "the returned word is that Bool's encoding");
            }
            var held = string.Join(", ", Enumerable.Range(1, stored.Count).Select(index => $"`held{index}`"));
            lean.Noted(indent, "sorry", "Postcondition of the returned value" +
                (branches.Count == 0 ? "" : " where " + string.Join(" and ", branches)) +
                (stored.Count == 0 ? "" : $", with {held} the stored fields"));
        }
    }
}
