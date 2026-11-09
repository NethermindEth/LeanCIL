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
            // Outlines do not follow value arrays, so a value-array field is never a view field.
            foreach (var view in extraction.Views)
                classes[view.FullName] = [.. view.Fields.Where(field => field.Kind != ClassViews.FieldKind.Array)
                    .Select(field => new ViewField(view.Path, field.Lean,
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

    /// <summary>A `newarr` of `Length` elements of the class `Scope` and `Name` quote, the first write of the body,
    /// which binds the fresh array as `Array`.</summary>
    sealed record Allocation(string Array, string Scope, string Name, int Length, int Stores)
    {
        internal string Element => Array + "Element";
    }

    enum ElementKind { Length, Load, Store }

    /// <summary>An access of an array argument after `Stores` earlier writes: its length, or a load or store of the
    /// element at `Index`, a `Nat` term, whose fact is `Slot`. A store writes and a load pushes `Value`: an object
    /// the body reaches as `Target`, null, or a reference outside the model whose formation in the caller's memory
    /// `Formed` states. A `Reread` load reads back what an earlier store on its path wrote.</summary>
    sealed record ElementAccess(string Array, ElementKind Kind, int Stores, string? Index = null,
        string? Value = null, Reached? Target = null, string? Formed = null, string? Slot = null, bool Reread = false)
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
        /// <summary>An array of class references: an argument, or one the body allocates.</summary>
        sealed record ArrayArgument(string Name) : Item;

        /// <summary>The fact naming each element of an array the body loads or stores, by array and index, shared
        /// by every path.</summary>
        Dictionary<(string Array, string Index), string> Slots { get; init; } = [];

        /// <summary>The array the body allocates, if any.</summary>
        internal Allocation? Fresh { get; private set; }

        /// <summary>The value stored into each element fact, shared by every path.</summary>
        Dictionary<string, string> Stored { get; init; } = [];

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
                        calls = calls, splits = splits + 1, Fresh = Fresh, previous = [.. PathSteps] })).ToArray();
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
                else if (ClassViews.Decode(op) is { Store: false, Kind: ClassViews.FieldKind.Word } load)
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
                else if (ClassViews.Decode(op) is { Store: true, Kind: ClassViews.FieldKind.Word } store)
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
                else if (ClassViews.Decode(op) is { Store: false, Kind: ClassViews.FieldKind.Reference } referenceLoad)
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
                else if (ClassViews.Decode(op) is { Store: true, Kind: ClassViews.FieldKind.Reference } referenceStore)
                {
                    var value = Pop();
                    if (Pop() is not Instance instance || Field(instance, referenceStore) is not { } field)
                        return Stop("a reference field store into an object the outline cannot name");
                    if (instance.Object.Holder is not null)
                        return Stop($"a store into `{field.Lean}` of an object a field holds, which the footprint " +
                            "cannot name");
                    if (value is Opaque { } late && CallWrote) return Stop(Uncarried(late));
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
                    Steps.Add(new ElementAccess(array.Name, ElementKind.Length, stores));
                    var length = array.Name == Fresh?.Array ? $"{Fresh.Length}" : array.Name + "Length";
                    stack.Add(new Word($"(BitVec.ofNat 64 {length})", 8));
                }
                else if ((match = Regex.Match(op, @"\A\.newReferenceArray \(\.object (""[^""]*"") (""[^""]*"")\)\z"))
                    .Success)
                {
                    // Facts stated of the caller's memory carry into the fresh one only across this first write.
                    if (Pop() is not Word { Width: 4, Term: { } count } || !Numeral(count) || int.Parse(count) == 0)
                        return Stop("`newarr` of a length that is not a positive literal");
                    if (linear || stores > 0 || calls > 0 || Fresh is not null)
                        return Stop("`newarr` after a write, a call or another allocation");
                    Fresh = new Allocation("fresh1", match.Groups[1].Value, match.Groups[2].Value, int.Parse(count),
                        stores);
                    Steps.Add(Fresh);
                    stores++;
                    stack.Add(new ArrayArgument(Fresh.Array));
                }
                else if (op == ".memory .referenceArrayLoad")
                {
                    if (Pop() is not Word index || Pop() is not ArrayArgument array || Index(index) is not { } at)
                        return Stop("`ldelem.ref` of an array or index the outline cannot name");
                    if ((Outside(array.Name, at) ?? Unseparated(array.Name, at)) is { } reason) return Stop(reason);
                    var slot = Slot(array.Name, at);
                    // The element holds what this path last stored into it, or what it held in the caller's memory.
                    if (PathSteps.OfType<ElementAccess>().LastOrDefault(access => access.Kind == ElementKind.Store &&
                        access.Slot == slot) is { } written)
                    {
                        Item reread = written switch
                        {
                            { Target: { } target } => new Instance(target),
                            { Value: ".null" } => new Null(),
                            _ => new Opaque(written.Value!, written.Formed!)
                        };
                        if (reread is Opaque opaque && CallWrote) return Stop(Uncarried(opaque));
                        Steps.Add(written with { Kind = ElementKind.Load, Stores = stores, Reread = true });
                        stack.Add(reread);
                        continue;
                    }
                    // Every element of a fresh array holds null until a store.
                    if (array.Name == Fresh?.Array)
                    {
                        Steps.Add(new ElementAccess(array.Name, ElementKind.Load, stores, at, ".null", Slot: slot,
                            Reread: true));
                        stack.Add(new Null());
                        continue;
                    }
                    var held = new Opaque($"(ReferenceArray.of initial {array.Name} {at})", slot + "Forms.formed");
                    if (CallWrote) return Stop(Uncarried(held));
                    Steps.Add(new ElementAccess(array.Name, ElementKind.Load, stores, at, held.Term,
                        Formed: held.Formed, Slot: slot));
                    stack.Add(held);
                }
                else if (op == ".memory .referenceArrayStore")
                {
                    var value = Pop();
                    if (Pop() is not Word index || Pop() is not ArrayArgument array || Index(index) is not { } at)
                        return Stop("`stelem.ref` into an array or at an index the outline cannot name");
                    if ((Outside(array.Name, at) ?? Unseparated(array.Name, at)) is { } reason) return Stop(reason);
                    if (value is Opaque late && CallWrote) return Stop(Uncarried(late));
                    var slot = Slot(array.Name, at);
                    ElementAccess? stored = value switch
                    {
                        Instance target => new(array.Name, ElementKind.Store, stores, at,
                            $"(.address {target.Object.Name})", target.Object, Slot: slot),
                        Null => new(array.Name, ElementKind.Store, stores, at, ".null", Slot: slot),
                        Opaque opaque => new(array.Name, ElementKind.Store, stores, at, opaque.Term,
                            Formed: opaque.Formed, Slot: slot),
                        _ => null
                    };
                    if (stored is null) return Stop("`stelem.ref` of a value the outline cannot name");
                    // One premise names what each element's store must pass, so every path stores the same value.
                    if (Stored.TryGetValue(slot, out var other) && other != stored.Value)
                        return Stop($"a second value stored into `{slot}`, which the statement names one store of");
                    Stored[slot] = stored.Value!;
                    Steps.Add(stored);
                    stores++;
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
                    ElementAccess { Kind: ElementKind.Store } element => (object)element,
                    Allocation allocation => allocation,
                    _ => null
                }).OfType<object>().LastOrDefault();
                return last is Access { Target: { } stored } access && access.Object == holder && access.Field == field
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

        /// <summary>A call on this path wrote memory, across which no reference outside the model is known to
        /// form, since its contract keeps only allocations older than its caller's.</summary>
        bool CallWrote => PathSteps.Any(step => step is CallStep { Writes: not null });

        static string Uncarried(Opaque opaque) =>
            $"a use of `{opaque.Term}` after a call that writes, across which the statement's formation of it " +
            "does not carry";

        /// <summary>Why the facts of element `index` of `array` do not carry across this path's element stores:
        /// one into another array, which may be the same one, or one at an index not provably different.</summary>
        string? Unseparated(string array, string index)
        {
            foreach (var store in PathSteps.OfType<ElementAccess>().Where(access => access.Kind == ElementKind.Store))
            {
                if (store.Array != array)
                    return $"an access of `{array}` after a store into `{store.Array}`, which may be the same array";
                if (store.Index != index && !(Numeral(store.Index!) && Numeral(index)))
                    return $"an access of element `{index}` of `{array}` after a store into element `{store.Index}`, " +
                        "which the statement cannot tell apart";
            }
            return null;
        }

        static bool Numeral(string index) => Regex.IsMatch(index, @"\A\d+\z");

        /// <summary>The element facts of `array`, with the index each names.</summary>
        internal (string Slot, string Index)[] SlotsOf(string array) =>
            [.. Slots.Where(pair => pair.Key.Array == array).Select(pair => (pair.Value, pair.Key.Index))];

        /// <summary>Why element `index` of the fresh array is not one its proof names: an index that is not a
        /// literal inside its length, which may throw.</summary>
        string? Outside(string array, string index) =>
            array == Fresh?.Array && !(Numeral(index) && int.Parse(index) < Fresh.Length)
                ? $"an element `{index}` of `{array}` not provably inside its {Fresh.Length} elements" : null;

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
                    if (slot.Any(access => access.Kind == ElementKind.Load && !access.Reread))
                        plan.Premises.Add((slot.Key + "Forms", $"ReferenceArray.Forms initial {array.Name} {index}"));
                    if (slot.FirstOrDefault(access => access.Storable is not null) is { } store)
                        plan.Premises.Add((store.Storable!,
                            $"storableIn initial {array.ElementName} {store.Value} = .ok ()"));
                    if (owned) plan.Entries.Add($"ReferenceArray.entry {array.Name} {index}");
                }
            }
            // A fresh array is charged to the heap budget, and its elements are no memory of the caller's.
            foreach (var made in Flattened.OfType<Allocation>().DistinctBy(made => made.Array))
            {
                plan.Premises.Add((made.Array + "Budget", $"CIL.objectFieldSlot * {made.Length} ≤ initial.heapBudget"));
                foreach (var store in elements
                    .Where(access => access.Array == made.Array && access.Storable is not null)
                    .DistinctBy(access => access.Slot))
                    plan.Premises.Add((store.Storable!, $"storableIn initial {made.Element} {store.Value} = .ok ()"));
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

    /// <summary>A term's words, keeping each short innermost parenthesized group such as `(by decide)` whole, as
    /// parts the writer may wrap between. A longer group splits so no part outgrows the line.</summary>
    static string[] Terms(this string term) =>
        [.. InnermostGroup()
            .Replace(term, group => group.Length <= ShortGroup ? group.Value.Replace(' ', Glue) : group.Value)
            .Split(' ').Select(part => part.Replace(Glue, ' '))];

    const int ShortGroup = 40;
    const char Glue = '\u0001';

    [GeneratedRegex(@"\([^()]*\)")]
    private static partial Regex InnermostGroup();

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
        // A carried element fact also states what the element holds, starting from what it held in `initial`.
        var elements = walk.Flattened.OfType<ElementAccess>().Where(access => access.Slot is not null).ToArray();
        // Every element of a fresh array is owned, so its fact is a `Holds` from the allocation on.
        var fresh = walk.Flattened.OfType<Allocation>().Select(made => made.Array).ToHashSet();
        var owned = elements.Where(access => access.Kind == ElementKind.Store || fresh.Contains(access.Array))
            .Select(access => access.Slot!).ToHashSet();
        foreach (var slot in elements.Select(access => access.Slot!).Distinct())
            known[(slot + "At", 0)] = owned.Contains(slot) ? $"({slot}.holds)" : $"({slot}.reads)";
        foreach (var array in spec.Arrays)
            known[(array.Name + "Live", 0)] = walk.ArrayFact(array.Name) is var fact && fact == array.Name + "Live"
                ? fact : fact + ".toLive";
        var facts = walk.Objects.Where(reached => reached.Holder is null)
            .Select(reached => reached.Name + "Live.formed")
            .Concat(spec.Arrays.Select(array => walk.ArrayFact(array.Name) + ".formed")).ToList();
        new ObjectPath(lean, spec, walk.Owns, owned, widen, returns, "  ", known, [], facts, []).Write(walk);
    }

    /// <summary>One path of an object body's proof from where its walk starts, `indent` deep: `known` names
    /// each fact in the memory after a number of writes, `stored` holds the writes so far, `facts` those not
    /// yet given to a step and `branches` the sides of the splits taken.</summary>
    sealed class ObjectPath(Writer lean, Specification spec, Func<Reached, ViewField, bool> owns,
        HashSet<string> ownedSlots, string widen, string? returns, string indent,
        Dictionary<(string Key, int Stores), string> known, List<object> stored, List<string> facts,
        List<string> branches)
    {
        string Live(Reached reached, int stores) => Carry(reached.Name + "Live", stores, (previous, level) =>
            $"{previous}.after_confined framed{level}");

        string FieldFact(Reached reached, ViewField field, int stores) =>
            Carry(ObjectWalk.Fact(reached, field), stores, (previous, level) =>
            {
                // No object with a located field is an array, so an element store is apart from every field.
                if (stored[level - 1] is Allocation) return $"{previous}.after_confined framed{level} Nowhere";
                if (stored[level - 1] is ElementAccess element)
                    return $"{previous}.after_confined framed{level} (ReferenceArray.apart_single (show " +
                        $"{reached.Name}.allocation ≠ {element.Array}.allocation from " +
                        $"{ArrayLive(element.Array, level - 1)}.field_ne {previous}.located rfl))";
                var store = (Access)stored[level - 1];
                if (store.Field != field)
                    return $"{previous}.after_confined framed{level} (apart_of_entries rfl)";
                if (store.Object == reached) return $"held{level}.1";
                // The two objects may be one, so `across` splits on whether the store reached this field.
                return $"({previous}.across {Live(store.Object, level - 1)} framed{level} held{level}).1";
            });

        /// <summary>An array argument's `Live` fact after `stores` writes, which keep every older allocation.
        /// </summary>
        string ArrayLive(string array, int stores) => Carry(array + "Live", stores, (previous, level) =>
            $"{previous}.after_confined framed{level}");

        /// <summary>What element fact `slot` of `array` holds after `stores` writes: `Holds` when the statement
        /// owns it and `Reads` otherwise. The walk lets no element fact cross a store into another array or at an
        /// index not provably different, nor a call that writes an element.</summary>
        string ElementFact(string array, string slot, int stores) => Carry(slot + "At", stores, (previous, level) =>
            stored[level - 1] switch
            {
                ElementAccess { Slot: var written } when written == slot => $"held{level}",
                ElementAccess => $"{previous}.across_ne framed{level} (by decide)",
                Access store => $"{previous}.after_confined framed{level} (ReferenceArray.apart_single (show " +
                    $"{array}.allocation ≠ {store.Object.Name}.allocation from ({ArrayLive(array, level - 1)}" +
                    $".field_ne {FieldFact(store.Object, store.Field, level - 1)}.located rfl).symm))",
                Allocation => $"{previous}.after_confined framed{level} Nowhere",
                _ => throw new InvalidOperationException($"no carry of `{slot}` across write {level}")
            });

        /// <summary>That nothing lies in the empty footprint an allocation writes.</summary>
        const string Nowhere = "(fun _ member => nomatch member)";

        /// <summary>That write `level` keeps every allocation: a slot store's equation or a field write's.
        /// </summary>
        string Kept(int level) => stored[level - 1] is Access { Field.Width: not null }
            ? $"(write_allocations _ _ _ _ _ written{level})" : $"(ReferenceArray.allocations_of_setSlot wrote{level})";

        /// <summary>`formed`, the formation of a reference in `initial`, after `stores` writes; the walk lets
        /// none cross a call that writes.</summary>
        string FormedAt(string formed, int stores)
        {
            if (stores == 0 || formed == "rfl") return formed;
            var key = formed.EndsWith(".formed", StringComparison.Ordinal) ? formed[..^".formed".Length] : formed;
            known.TryAdd((key, 0), formed);
            // The allocation is the first write, so `initial`'s well-formedness dates what forms in it.
            return Carry(key, stores, (previous, level) => stored[level - 1] is Allocation
                ? $"formObject_of_confined framed{level} wellFormed {previous}"
                : $"(formObject_of_allocations {Kept(level)} _).trans {previous}");
        }

        /// <summary>A store's covariance premise after `stores` writes: an object of the model keeps its class
        /// across any confined write, and any other reference across writes that keep every allocation.</summary>
        string StorableAt(ElementAccess access, int stores)
        {
            known.TryAdd((access.Storable!, 0), access.Storable!);
            return Carry(access.Storable!, stores, (previous, level) => access.Target is { } target
                ? $"ReferenceArray.storableIn_after_confined {previous} framed{level} {Live(target, level - 1)}.old"
                : stored[level - 1] is Allocation
                    ? $"ReferenceArray.storableIn_of_confined {previous} framed{level} wellFormed {access.Formed}"
                    : $"(ReferenceArray.storableIn_of_allocations {Kept(level)} _ _).trans {previous}");
        }

        string Carry(string key, int stores, Func<string, int, string> across)
        {
            if (known.TryGetValue((key, stores), out var name)) return name;
            if (stores == 0) throw new InvalidOperationException($"no fact `{key}` in the caller's memory");
            var previous = Carry(key, stores - 1, across);
            var carried = across(previous, stores);
            name = key + stores;
            lean.Wrapped($"{indent}have {name} :=", carried.Terms(), "");
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
                        new ObjectPath(lean, spec, owns, ownedSlots, widen, returns, indent + "  ", new(known),
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
                if (step is Allocation made)
                {
                    Allocate(made, walk.SlotsOf(made.Array));
                    continue;
                }
                Access((Access)step);
            }
            Return(walk);
        }

        /// <summary>A `newarr` charged to the budget premise, confined to no caller memory, with a `Holds` of null
        /// for each element the body touches; the array and memory it makes are generalized, the array with the
        /// equation `Identity` that dates it after every caller allocation.</summary>
        void Allocate(Allocation made, (string Slot, string Index)[] slots)
        {
            var number = made.Stores + 1;
            var array = made.Array;
            var created = $"(objectMemory initial (referenceArrayType {made.Element}) " +
                $"(CIL.objectFieldSlot * {made.Length}))";
            string Fresh(string index) =>
                $"ReferenceArray.fresh initial {made.Element} (length := {made.Length}) (index := {index}) " +
                "(by decide) (by decide)";
            lean.Wrapped($"{indent}have {array}Allocated :=", ($"newReferenceArray_ok wellFormed {made.Element} " +
                $"(value := .i32 {made.Length}) (length := {made.Length}) (Or.inl rfl) (by decide) (by decide) " +
                $"{array}Budget").Terms(), "");
            lean.Wrapped($"{indent}have {array}Created :=",
                $"allocateObject_ok wellFormed (referenceArrayType {made.Element}) {array}Budget (by decide)".Terms(),
                "");
            lean.Wrapped($"{indent}have framed{number} :",
                ($"Confined [] initial {created} := Confined.ofMemoryBelow " +
                $"(allocateObject_effect {array}Created).below (Nat.le_refl _) (by simp [objectMemory])").Terms(), "");
            foreach (var (slot, index) in slots) lean.Wrapped($"{indent}have {slot} :=", Fresh(index).Terms(), "");
            var live = $"{array}Live{number}";
            lean.Wrapped($"{indent}have {live} :=", $"({Fresh("0")}).1.toLive".Terms(), "");
            var facts = string.Join(" ", slots.Select(slot => slot.Slot).Append(live));
            lean.Wrapped($"{indent}generalize", $"{created} = stored{number}".Terms(),
                $"at {array}Allocated framed{number} {facts}");
            lean.Wrapped($"{indent}generalize {array}Identity :", ["(⟨initial.nextIdentity, 0⟩ : Reference)", "=",
                array], $"at {array}Allocated {facts}");
            foreach (var (slot, _) in slots) known[(slot + "At", number)] = slot;
            known[(array + "Live", number)] = live;
            Add(array + "Allocated");
            Add(made.Element);
            stored.Add(made);
        }

        /// <summary>An array argument's length or element access, with its facts carried across the writes
        /// before it.</summary>
        void Element(ElementAccess access)
        {
            var slot = access.Slot!;
            var level = access.Stores;
            // The array argument is pushed again in the memory the access runs in.
            if (level > 0) Add(ArrayLive(access.Array, level) + ".formed");
            if (access.Kind == ElementKind.Length)
            {
                Add(ArrayLive(access.Array, level) + ".located");
                return;
            }
            // What the access pushes or stores must form in the memory it runs in.
            var formed = access switch
            {
                { Target: { } target } => Live(target, level) + ".formed",
                { Value: ".null" } => "rfl",
                _ => FormedAt(access.Formed!, level)
            };
            if (access.Kind == ElementKind.Load)
            {
                if (level == 0)
                {
                    Add($"({slot}.facts_forms {slot}Forms).1");
                    Add($"({slot}.facts_forms {slot}Forms).2");
                }
                else
                {
                    var fact = ElementFact(access.Array, slot, level);
                    var reads = ownedSlots.Contains(slot) ? fact + ".reads" : fact;
                    Add($"({reads}.facts {formed}).1");
                    Add($"({reads}.facts {formed}).2");
                }
                Add(formed);
                return;
            }
            var number = level + 1;
            var owned = level == 0 ? slot : ElementFact(access.Array, slot, level) + ".1";
            var obtained = access switch
            {
                { Target: not null } => $"{owned}.store {Live(access.Target, level)} {StorableAt(access, level)}",
                { Value: ".null" } => $"{owned}.store_null",
                _ => $"{owned}.store_formed {formed} {StorableAt(access, level)}"
            };
            lean.Wrapped($"{indent}obtain ⟨located{number}, checked{number}, written{number}, framed{number}, " +
                $"held{number}⟩ :=", [obtained], "");
            lean.Wrapped($"{indent}generalize wrote{number} :",
                [$"setSlot {ObjectWalk.Memory(level)}", $"(ReferenceArray.slot {access.Array} {access.Index})",
                    access.Value!, $"= stored{number}"], $"at written{number} framed{number} held{number}");
            if (access.Value != ".null") Add(formed);
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
                var formed = access.Formed is null ? null : FormedAt(access.Formed, access.Stores);
                lean.Line($"{indent}obtain ⟨written{stores}, framed{stores}, held{stores}⟩ := " + (target is null
                    ? $"{fact}.store_formed {(formed == "rfl" ? $"(value := {value}) rfl" : formed)}"
                    : $"{fact}.store {target}"));
                lean.Wrapped($"{indent}generalize wrote{stores} :", [$"setSlot {ObjectWalk.Memory(access.Stores)}",
                    $"({access.Field.Lean}.address {access.Object.Name})", value, $"= stored{stores}"],
                    $"at written{stores} framed{stores} held{stores}");
                // The store checks the stored reference is formed in the memory it writes.
                if (target is not null) Add(target + ".formed");
                else if (formed != "rfl") Add(formed!);
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
            // Elements of a fresh array are no caller memory: the footprint forgets them.
            if (stored.OfType<Allocation>().FirstOrDefault() is { } made)
            {
                var indices = stored.OfType<ElementAccess>().Where(access => access.Array == made.Array)
                    .Select(access => access.Index!).Distinct().ToArray();
                if (indices.Length > 0)
                    confined = $"(Confined.forget_fresh (fresh := [{string.Join(", ", indices)}].map " +
                        $"(ReferenceArray.entry {made.Array})) {confined} " +
                        $"(ReferenceArray.entries_young {made.Array}Identity _))";
            }
            // A chain that forgets fresh entries is too long for one line, so it wraps between its terms.
            string[] Parts(string tail) => stored.OfType<Allocation>().Any()
                ? (confined + tail).Terms() : [confined + tail];
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
                    [.. Parts(",").Select((part, index) => index == 0 ? "⟨" + part : part), returns + "⟩"], "");
                return;
            }
            var boolean = spec.Result is { Boolean: true };
            lean.Wrapped(spec.Result is null ? $"{indent}refine ⟨rfl,"
                : boolean ? $"{indent}refine ⟨?result, ?encoded," : $"{indent}refine ⟨_, rfl,",
                Parts(","), "?_⟩");
            if (boolean)
            {
                // The returned word is computed, not named, so the author chooses the Bool it encodes.
                lean.Noted(indent, "case result => sorry", "the Bool the returned word encodes");
                lean.Noted(indent, "case encoded => sorry", "the returned word is that Bool's encoding");
            }
            // An allocation writes nothing the caller holds, so it leaves no `held` fact.
            var stores = Enumerable.Range(1, stored.Count).Where(index => stored[index - 1] is not Allocation)
                .ToArray();
            var held = string.Join(", ", stores.Select(index => $"`held{index}`"));
            lean.Noted(indent, "sorry", "Postcondition of the returned value" +
                (branches.Count == 0 ? "" : " where " + string.Join(" and ", branches)) +
                (stores.Length == 0 ? "" : $", with {held} the stored fields"));
        }
    }
}
