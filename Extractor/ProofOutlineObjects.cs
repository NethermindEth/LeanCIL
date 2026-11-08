using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Class instances in an outline: the named fields an extraction emits, the premises and footprint they give an
// object argument, and the straight-line walk that steps field loads and one final field store.
internal static partial class ProofOutline
{
    /// <summary>A field an extraction names, as `Path.Name`; a reference field has no width.</summary>
    sealed record ViewField(string Path, string Name, int? Width, int Offset, bool Stored)
    {
        internal string Lean => Path + "." + Name;
    }

    /// <summary>The fields an extraction's `Extracted.Classes` names, by the full name of their class, and whether
    /// any of its methods stores each.</summary>
    sealed class ClassViews
    {
        readonly Dictionary<string, ViewField[]> classes = new(StringComparer.Ordinal);

        internal ClassViews(Extraction extraction)
        {
            var stores = extraction.Emitted.SelectMany(method => method.Ops)
                .Select(op => FieldStore().Match(op)).Where(match => match.Success)
                .Select(match => (Owner: match.Groups["owner"].Value, Offset: int.Parse(match.Groups["offset"].Value)))
                .ToHashSet();
            foreach (Match view in ClassBlock().Matches(extraction.Source))
            {
                var path = view.Groups["path"].Value;
                var owner = view.Groups["type"].Value;
                classes[view.Groups["name"].Value] = ViewDefinition().Matches(view.Groups["body"].Value)
                    .Select(field =>
                    {
                        var offset = int.Parse(field.Groups["offset"].Value);
                        return new ViewField(path, field.Groups["field"].Value,
                            field.Groups["width"].Success ? int.Parse(field.Groups["width"].Value) : null, offset,
                            stores.Contains((owner, offset)));
                    }).ToArray();
            }
        }

        /// <summary>The named fields of an instance of `type`: its class's and its bases', nearest first.</summary>
        internal ViewField[] Of(TypeReference type) =>
            [.. new[] { type }.Concat(ObjectTypes.Bases(type))
                .SelectMany(owner => classes.GetValueOrDefault(owner.FullName) ?? [])];
    }

    [GeneratedRegex(@"\A\.memory \(\.(?:setObjectField|setObjectReferenceField) \((?<owner>.*)\) (?<offset>\d+)" +
        @"(?: \d+)?\)\z")]
    private static partial Regex FieldStore();

    [GeneratedRegex(@"^-- The fields of `(?<name>[^`]+)` this extraction's methods load or store\.\r?\n" +
        @"namespace (?<path>\S+)\r?\n@\[reducible\] def type : Extraction\.TypeExpr := (?<type>.*?)\r?\n" +
        @"(?<body>.*?)^end \k<path>\r?$", RegexOptions.Multiline | RegexOptions.Singleline)]
    private static partial Regex ClassBlock();

    [GeneratedRegex(@"^@\[reducible\] def (?<field>\S+) : Safety\.(?:WordField (?<width>\d+)|ReferenceField) := " +
        @"⟨type, (?<offset>\d+)⟩\r?$", RegexOptions.Multiline)]
    private static partial Regex ViewDefinition();

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

    /// <summary>A straight-line body as the facts that step it: field loads and stores of the objects it reaches,
    /// with locals and null tests of objects followed; null with the reason when it does more.</summary>
    sealed class ObjectWalk(Specification spec, string[] ops, ClassViews views)
    {
        internal string? Stopped { get; private set; }
        internal string? Returned { get; private set; }
        internal List<Reached> Objects { get; } = [];
        internal List<Access> Accesses { get; } = [];

        /// <summary>A field access in program order, after `Stores` earlier stores.</summary>
        internal sealed record Access(Reached Object, ViewField Field, bool Store, bool Signed, int Stores,
            string? Value = null, Reached? Target = null);

        abstract record Item;
        sealed record Word(string Term, int Width) : Item;
        sealed record Instance(Reached Object) : Item;
        sealed record Null : Item;

        int stores;

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
                else if ((match = Regex.Match(op, @"\A\.const(32|64) (\d+)\z")).Success)
                    stack.Add(new Word(match.Groups[2].Value, match.Groups[1].Value == "64" ? 8 : 4));
                else if ((match = Regex.Match(op, @"\A\.(add|sub|mul|band|bor|bxor)\z")).Success)
                {
                    if (Pop() is not Word right || Pop() is not Word left || left.Width != right.Width)
                        return Stop("arithmetic on a value the outline cannot name");
                    var symbol = match.Groups[1].Value switch
                    {
                        "add" => "+", "sub" => "-", "mul" => "*", "band" => "&&&", "bor" => "|||", _ => "^^^"
                    };
                    stack.Add(new Word($"({left.Term} {symbol} {right.Term})", left.Width));
                }
                else if (op is ".convU8" or ".convI8")
                {
                    if (Pop() is not Word { Width: 4 } word)
                        return Stop("a widening of a value the outline cannot name");
                    var widen = op == ".convU8" ? "setWidth" : "signExtend";
                    stack.Add(new Word($"({word.Term}.{widen} 64)", 8));
                }
                else if ((match = Regex.Match(op,
                    @"\A\.memory \(\.objectField \(.*\) (\d+) (\d+) (true|false)\)\z")).Success)
                {
                    if (Pop() is not Instance instance || Field(instance, match) is not { } field)
                        return Stop("a field load of an object the outline cannot name");
                    var signed = match.Groups[3].Value == "true";
                    Accesses.Add(new(instance.Object, field, false, signed, stores));
                    var term = $"({field.Lean}.of {Memory(stores)} {instance.Object.Name})";
                    stack.Add(field.Width switch
                    {
                        < 4 => new Word($"({term}.{(signed ? "signExtend" : "setWidth")} 32)", 4),
                        _ => new Word(term, field.Width!.Value)
                    });
                }
                else if ((match = Regex.Match(op, @"\A\.memory \(\.setObjectField \(.*\) (\d+) (\d+)\)\z")).Success)
                {
                    var value = Pop();
                    if (Pop() is not Instance instance || Field(instance, match) is not { } field)
                        return Stop("a field store into an object the outline cannot name");
                    if (value is not Word word || word.Width != field.Width)
                        return Stop($"a store into `{field.Lean}` of a value of another width, which the field " +
                            "truncates");
                    if (instance.Object.Holder is not null)
                        return Stop($"a store into `{field.Lean}` of an object a field holds, which the footprint " +
                            "cannot name");
                    Accesses.Add(new(instance.Object, field, true, false, stores++, word.Term));
                }
                else if ((match = Regex.Match(op, @"\A\.memory \(\.objectReferenceField \(.*\) (\d+)\)\z")).Success)
                {
                    if (Pop() is not Instance instance || ReferenceField(instance, match) is not { } field)
                        return Stop("a reference field load of an object the outline cannot name");
                    if (stores > 0)
                        return Stop($"a load of `{field.Lean}` after a store, whose target the statement names " +
                            "in the caller's memory");
                    var reached = Accesses.FirstOrDefault(access => !access.Store && access.Target is not null &&
                        access.Object == instance.Object && access.Field == field)?.Target;
                    if (reached is null)
                    {
                        if (spec.Method.Body.Instructions[pc].Operand is not FieldReference { FieldType: var type } ||
                            !ObjectTypes.Is(type))
                            return Stop($"a load of `{field.Lean}`, whose class the outline cannot name");
                        var name = instance.Object.Name + Capitalized(field.Name);
                        reached = new Reached(name + "Target", views.Of(type), name + "Held", instance.Object.Name);
                        Objects.Add(reached);
                    }
                    Accesses.Add(new(instance.Object, field, false, false, stores, Target: reached));
                    stack.Add(new Instance(reached));
                }
                else if ((match = Regex.Match(op,
                    @"\A\.memory \(\.setObjectReferenceField \(.*\) (\d+)\)\z")).Success)
                {
                    var value = Pop();
                    if (Pop() is not Instance instance || ReferenceField(instance, match) is not { } field)
                        return Stop("a reference field store into an object the outline cannot name");
                    if (value is not Instance target)
                        return Stop($"a store into `{field.Lean}` of null, which `owned.store` does not take");
                    if (instance.Object.Holder is not null)
                        return Stop($"a store into `{field.Lean}` of an object a field holds, which the footprint " +
                            "cannot name");
                    Accesses.Add(new(instance.Object, field, true, false, stores++, Target: target.Object));
                }
                else if (op == ".nop") { }
                else if (op == ".ret" || op.StartsWith(".ret (some ", StringComparison.Ordinal))
                {
                    if (spec.Result is not null)
                    {
                        Returned = Pop() switch
                        {
                            Word word when !spec.Result.Boolean && !spec.Result.Object => word.Term,
                            Instance instance when spec.Result.Object => $"(.address {instance.Object.Name})",
                            Null when spec.Result.Object => ".null",
                            _ => null
                        };
                        if (Returned is null) return Stop("a result the outline cannot name");
                    }
                    return true;
                }
                else if (op.StartsWith(".call", StringComparison.Ordinal))
                    return Stop("a call, which `cil_contract_steps` composes through the callee's contract");
                else return Stop($"`{op}`, which the outline does not step");
            }
            Stopped = "the end of the body without a return";
            return false;
        }

        internal static string Memory(int stores) => stores == 0 ? "initial" : $"stored{stores}";

        static ViewField? Field(Instance instance, Match match) => instance.Object.Fields.FirstOrDefault(field =>
            field.Offset == int.Parse(match.Groups[1].Value) && field.Width == int.Parse(match.Groups[2].Value));

        static ViewField? ReferenceField(Instance instance, Match match) => instance.Object.Fields
            .FirstOrDefault(field => field.Width is null && field.Offset == int.Parse(match.Groups[1].Value));

        /// <summary>The statement's facts about the reached objects: each is live, a target is what its field
        /// holds, and each field the body touches is `Owned` when it stores it and `Readable` otherwise.</summary>
        internal ObjectPlan Plan()
        {
            var plan = new ObjectPlan();
            foreach (var reached in Objects)
            {
                if (reached.Holder is not null)
                {
                    plan.Targets.Add(reached.Name);
                    var holder = Accesses.First(access => access.Target == reached && !access.Store);
                    plan.Premises.Add((reached.Held!,
                        $"{holder.Field.Lean}.of initial {holder.Object.Name} = .address {reached.Name}"));
                }
                plan.Premises.Add((reached.Name + "Live", $"LiveObject initial {reached.Name}"));
                foreach (var field in reached.Fields)
                {
                    var touched = Accesses.Where(access => access.Object == reached && access.Field == field).ToArray();
                    if (touched.Length == 0) continue;
                    var kind = touched.Any(access => access.Store) ? "Owned" : "Readable";
                    plan.Premises.Add((Fact(reached, field), $"{field.Lean}.{kind} initial {reached.Name}"));
                    if (kind == "Owned") plan.Entries.Add($"{field.Lean}.entry {reached.Name}");
                }
            }
            return plan;
        }

        internal static string Fact(Reached reached, ViewField field) => reached.Name + Capitalized(field.Name);
    }

    static string Capitalized(string name) => char.ToUpperInvariant(name[0]) + name[1..];

    /// <summary>The straight-line proof of a body over objects: each store through `Owned.store`, the facts
    /// of later accesses carried across the stores before them, the run stepped with every access's facts, and
    /// the postcondition left as the hole.</summary>
    static void ObjectBody(Writer lean, Specification spec, ObjectWalk walk)
    {
        // The name of each fact in the memory after a number of stores, introduced when an access needs it.
        var known = new Dictionary<(string Key, int Stores), string>();
        var stored = new List<ObjectWalk.Access>();
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
                return field.Width is null ? null
                    : $"({previous}.across {Live(store.Object, level - 1)} framed{level} held{level}).1";
            });
        string Carry(string key, int stores, Func<string, int, string?> across)
        {
            if (known.TryGetValue((key, stores), out var name)) return name;
            var previous = Carry(key, stores - 1, across);
            var carried = across(previous, stores) ?? throw new InvalidOperationException(
                $"{key} has no fact after a store into the same reference field of another object");
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
        foreach (var access in walk.Accesses)
        {
            var fact = FieldFact(access.Object, access.Field, access.Stores);
            if (!access.Store)
            {
                Add(access.Field.Width is null ? $"{fact}.facts {access.Target!.Held} {access.Target.Name}Live"
                    : access.Signed ? fact + ".signedFacts" : fact + ".facts");
                continue;
            }
            var index = access.Stores + 1;
            if (access.Field.Width is null)
            {
                var target = Live(access.Target!, access.Stores);
                lean.Line($"  obtain ⟨written{index}, framed{index}, held{index}⟩ := {fact}.store {target}");
                lean.Wrapped("  generalize", [$"setSlot {ObjectWalk.Memory(access.Stores)} " +
                    $"({access.Field.Lean}.address {access.Object.Name}) (.address {access.Target!.Name}) = " +
                    $"stored{index}"], $"at written{index} framed{index} held{index}");
            }
            else lean.Wrapped($"  obtain ⟨stored{index}, written{index}, framed{index}, held{index}⟩ :=",
                [$"{fact}.store {access.Value}"], "");
            Add(fact + ".located");
            Add(Live(access.Object, access.Stores) + ".formed");
            Add($"written{index}");
            stored.Add(access);
        }
        var widened = Enumerable.Range(1, stored.Count).Select(index => $"(framed{index}.widen (by simp [footprint]))")
            .ToArray();
        var confined = widened.Length == 0 ? "Confined.refl _ _"
            : widened.Skip(1).Aggregate(widened[0], (chain, next) => $"({chain}.trans {next})");
        // The return leaves the method's frame, which owns no caller memory.
        facts.Add("leaveFrame");
        lean.Wrapped("  cil_contract_steps", ["[" + string.Join(", ", facts) + "]"], "");
        lean.Wrapped(spec.Result is null ? "  refine ⟨rfl," : "  refine ⟨_, rfl,", [confined + ","], "?_⟩");
        var held = string.Join(", ", Enumerable.Range(1, stored.Count).Select(index => $"`held{index}`"));
        lean.Noted("  ", "sorry", "Postcondition of the returned value" +
            (stored.Count == 0 ? "" : $", with {held} the stored fields"));
    }
}
