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

    /// <summary>A straight-line body of field loads, arithmetic and at most one field store before its return, as
    /// the terms of its stored value and result; null with the reason when the body does more.</summary>
    sealed class ObjectWalk(Specification spec, string[] ops)
    {
        internal string? Stopped { get; private set; }
        internal List<string> Loads { get; } = [];
        internal (Parameter Object, ViewField Field, string Value)? Store { get; private set; }
        internal string? Returned { get; private set; }

        abstract record Item;
        sealed record Word(string Term, int Width) : Item;
        sealed record Instance(Parameter Parameter) : Item;

        internal bool Run(Func<int, string> location)
        {
            var stack = new List<Item>();
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
                var closing = op is ".ret" or ".nop" || op.StartsWith(".ret (some ", StringComparison.Ordinal);
                if (Store is not null && !closing)
                    return Stop($"`{op}` after the field store, whose memory the outline holds no field facts in");
                if ((match = Regex.Match(op, @"\A\.arg (\d+)\z")).Success)
                {
                    var parameter = spec.Parameters[int.Parse(match.Groups[1].Value)];
                    stack.Add(parameter.Shape switch
                    {
                        ParameterShape.Object => new Instance(parameter),
                        ParameterShape.Scalar => new Word(parameter.Name, parameter.Width),
                        _ => null!
                    });
                    if (stack[^1] is null) return Stop($"the argument `{parameter.Name}`, which needs a case split");
                }
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
                else if ((match = Regex.Match(op, @"\A\.memory \(\.objectField \(.*\) (\d+) (\d+) false\)\z")).Success)
                {
                    if (Pop() is not Instance instance || Field(instance, match) is not { } field)
                        return Stop("a field load of an object the outline cannot name");
                    var fact = FieldFact(instance.Parameter, field);
                    if (!Loads.Contains(fact)) Loads.Add(fact);
                    var term = $"({field.Lean}.of initial {instance.Parameter.Name})";
                    stack.Add(field.Width < 4
                        ? new Word($"({term}.setWidth 32)", 4) : new Word(term, field.Width!.Value));
                }
                else if ((match = Regex.Match(op, @"\A\.memory \(\.setObjectField \(.*\) (\d+) (\d+)\)\z")).Success)
                {
                    var value = Pop();
                    if (Pop() is not Instance instance || Field(instance, match) is not { } field)
                        return Stop("a field store into an object the outline cannot name");
                    if (value is not Word word || word.Width != field.Width)
                        return Stop($"a store into `{field.Lean}` of a value of another width, which the field " +
                            "truncates");
                    Store = (instance.Parameter, field, word.Term);
                }
                else if (op is ".convU8" or ".convI8")
                {
                    if (Pop() is not Word { Width: 4 } word)
                        return Stop("a widening of a value the outline cannot name");
                    var widen = op == ".convU8" ? "setWidth" : "signExtend";
                    stack.Add(new Word($"({word.Term}.{widen} 64)", 8));
                }
                else if ((match = Regex.Match(op,
                    @"\A\.memory \(\.(?<kind>objectReferenceField|setObjectReferenceField) " +
                    @"\(.*\) (?<offset>\d+)\)\z")).Success)
                {
                    var store = match.Groups["kind"].Value.StartsWith("set", StringComparison.Ordinal);
                    var owner = stack.Count > (store ? 1 : 0) ? stack[^(store ? 2 : 1)] as Instance : null;
                    var offset = int.Parse(match.Groups["offset"].Value);
                    var named = owner?.Parameter.Fields
                        .FirstOrDefault(field => field.Width is null && field.Offset == offset);
                    var field = named is null ? "a reference field" : $"`{named.Lean}`";
                    return Stop(store
                        ? $"a store into {field}, which `owned.store targetLive` of its `Owned` fact steps"
                        : $"a load of {field}, which `readable.facts held targetLive` of its `Readable` fact steps");
                }
                else if (op == ".nop") { }
                else if (op == ".ret" || op.StartsWith(".ret (some ", StringComparison.Ordinal))
                {
                    if (spec.Result is not null)
                    {
                        Returned = Pop() switch
                        {
                            Word word when !spec.Result.Boolean && !spec.Result.Object => word.Term,
                            Instance instance when spec.Result.Object => $"(.address {instance.Parameter.Name})",
                            _ => null
                        };
                        if (Returned is null) return Stop("a result the outline cannot name");
                    }
                    return pc == ops.Length - 1 || Stop("a return before the end of the body");
                }
                else if (op.StartsWith(".call", StringComparison.Ordinal))
                    return Stop("a call, which `cil_contract_steps` composes through the callee's contract");
                else return Stop($"`{op}`, which the outline does not step");
            }
            Stopped = "the end of the body without a return";
            return false;
        }

        static ViewField? Field(Instance instance, Match match) => instance.Parameter.Fields.FirstOrDefault(field =>
            field.Offset == int.Parse(match.Groups[1].Value) && field.Width == int.Parse(match.Groups[2].Value));
    }

    /// <summary>The straight-line proof of a body over object arguments: its field loads stepped with each field's
    /// facts, its one field store through `Owned.store`, and the postcondition left as the hole.</summary>
    static void ObjectBody(Writer lean, Specification spec, ObjectWalk walk)
    {
        var facts = spec.Parameters.Where(parameter => parameter.Shape == ParameterShape.Object)
            .Select(parameter => parameter.Name + "Live.formed").Concat(walk.Loads.Select(fact => fact + ".facts"))
            .ToList();
        var final = "initial";
        var confined = "Confined.refl _ _";
        if (walk.Store is { } store)
        {
            var stored = FieldFact(store.Object, store.Field);
            lean.Wrapped($"  obtain ⟨stored, written, framed, held⟩ :=", [$"{stored}.store {store.Value}"], "");
            if (!walk.Loads.Contains(stored)) facts.Add(stored + ".located");
            facts.Add("written");
            final = "stored";
            confined = "framed.widen (by simp [footprint])";
        }
        // The run fixes the returned values, which the postcondition then reads.
        lean.Line($"  refine ⟨CIL.executionBound Extracted.program 0, {final}, ?results, ?run, ?postcondition⟩");
        lean.Line($"  case run => cil_checked_steps [{string.Join(", ", facts)}]");
        lean.Line("  case postcondition =>");
        lean.Line(spec.Result is null ? $"    refine ⟨rfl, {confined}, ?_⟩" : $"    refine ⟨_, rfl, {confined}, ?_⟩");
        lean.Noted("    ", "sorry", "Postcondition of the returned value" +
            (walk.Store is null ? "" : ", with `held` the stored field"));
    }
}
