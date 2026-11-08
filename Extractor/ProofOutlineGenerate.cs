using System.Text;
using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// The statement, specification placeholders, entry binding and loop scaffolding of an outline.
internal static partial class ProofOutline
{
    /// <summary>A Lean binder of the theorem and how its argument value is written; a narrow integer
    /// reaches the method sign- or zero-extended to 32 bits.</summary>
    sealed record Parameter(string Name, ParameterShape Shape, string Lean, int Width, bool Signed = false)
    {
        internal string ElementsName => Name + "Elements";

        /// <summary>The named fields of an object argument's class.</summary>
        internal ViewField[] Fields { get; init; } = [];
    }

    enum ParameterShape { Scalar, Boolean, Narrow, Reference, ReadOnlySpan, Object }

    /// <summary>The method's return as a Lean type and value constructor, or none for `void`; a `bool`
    /// is a `Bool` the returned word encodes as 1 or 0, and an object a possibly null reference.</summary>
    sealed record Result(string Lean, string Constructor, bool Boolean = false, bool Object = false)
    {
        internal string Encode(string term) => Object ? $".object {term}" : $".scalar ({Constructor} {term})";
    }

    /// <summary>The comment that starts every hole the outline could not step, so it can be found.</summary>
    const string NotOutlined = "not outlined: ";

    static readonly HashSet<string> Reserved = new(StringComparer.Ordinal)
    {
        "at", "by", "do", "else", "end", "fun", "from", "have", "if", "in", "let", "match", "then", "with",
        "show", "open", "theorem", "def", "where", "import", "namespace", "section", "case", "this",
        "entry", "loop", "State", "header", "invariant", "measure", "Precondition", "Postcondition",
        "correctness", "args", "initial", "final", "memory", "results", "result", "assumed", "wellFormed",
        "current", "frame", "holds", "recurse", "start", "entered", "setup", "entryFrame", "guard",
        "output", "permitted", "input", "calledFrame", "calledFormed", "returned", "footprint", "written",
        "stored", "framed", "held", "instance", "class", "structure", "inductive", "abbrev", "example",
        "for", "return", "mut", "unless", "variable", "universe", "deriving", "extends", "private",
        "protected", "partial", "mutual", "macro", "syntax", "notation", "calc", "nomatch", "nofun",
        "export", "attribute", "opaque", "axiom", "Type", "Prop", "Sort", "middle", "values", "post",
        "confined", "target"
    };

    // `module` is the keyed extraction module the outline imports, ahead of the library modules its form needs.
    static Outline Generate(Extraction extraction, string module)
    {
        var method = extraction.Methods[0];
        var emitted = extraction.Emitted[0];
        var names = new Names();
        var views = new FieldViews(extraction);
        var receiver = method.HasThis ? new[] { Receiver(method, names, views) } : [];
        var parameters = receiver.Concat(method.Parameters.Select(parameter =>
            Describe(method, parameter, names, views))).ToArray();
        var result = DescribeResult(method);
        bool symbolic = parameters.Any(parameter => parameter.Shape is ParameterShape.Reference or
            ParameterShape.ReadOnlySpan or ParameterShape.Object);
        var body = new Body(emitted.Ops);
        var lean = new Writer();
        var loops = body.Loops();
        var spec = new Specification(method, parameters, result, symbolic, extraction.Views.Length > 0);
        string source;
        if (loops.Count == 0)
            source = StraightLine(extraction, spec, body, lean);
        else if (loops.Count == 1)
        {
            LoopPlan(extraction, spec, body);
            source = LoopProof(extraction, spec, body, loops[0], names, lean);
        }
        else
            throw Unsupported($"{method.FullName} has {loops.Count} loops, with back edges at " +
                string.Join(", ", loops.Select(loop => Location(method, loop.Latch))) + "; new-proof binds one " +
                "cutpoint and does not chain the state from one loop's exit into the next");
        source = $"import {module}\n" + source;
        var holes = Regex.Matches(source, @"(?<![`\w])sorry(?![`\w])").Count;
        var paths = Regex.Matches(source, "-- " + NotOutlined).Count;
        return new(method.FullName, source, holes - paths, paths);
    }

    static NotSupportedException Unsupported(string message) =>
        new("new-proof cannot outline this method: " + message + ".");

    /// <summary>`this` of an instance method, named for its class.</summary>
    static Parameter Receiver(MethodDefinition method, Names names, FieldViews views)
    {
        var type = method.DeclaringType;
        if (!ObjectTypes.Is(type))
            throw Unsupported($"{method.FullName} is an instance method of {type.FullName}, which is not an " +
                "admitted class; new-proof binds `this` of class instances only");
        return Instance(names.Claim(char.ToLowerInvariant(type.Name[0]) + type.Name[1..], "receiver"), type, views);
    }

    static Parameter Instance(string name, TypeReference type, FieldViews views) =>
        new(name, ParameterShape.Object, "Reference", 8) { Fields = views.Of(type) };

    static Parameter Describe(MethodDefinition method, ParameterDefinition parameter, Names names, FieldViews views)
    {
        var type = parameter.ParameterType;
        var name = names.Claim(parameter.Name, "argument" + parameter.Index);
        if (ObjectTypes.Is(type)) return Instance(name, type, views);
        if (type is ByReferenceType reference && ElementWidth(reference.ElementType) is { } width)
            return new(name, ParameterShape.Reference, "Reference", width);
        if (Spans.Is(type) && type is GenericInstanceType span &&
            span.ElementType.FullName == "System.ReadOnlySpan`1" &&
            ElementWidth(span.GenericArguments[0]) is { } element)
            return new(name, ParameterShape.ReadOnlySpan, "SpanView", element);
        return type.FullName switch
        {
            "System.UInt32" or "System.Int32" => new(name, ParameterShape.Scalar, "W32", 4),
            "System.UInt64" or "System.Int64" => new(name, ParameterShape.Scalar, "W64", 8),
            "System.Boolean" => new(name, ParameterShape.Boolean, "Bool", 4),
            "System.Byte" => new(name, ParameterShape.Narrow, "BitVec 8", 1),
            "System.SByte" => new(name, ParameterShape.Narrow, "BitVec 8", 1, Signed: true),
            "System.UInt16" or "System.Char" => new(name, ParameterShape.Narrow, "BitVec 16", 2),
            "System.Int16" => new(name, ParameterShape.Narrow, "BitVec 16", 2, Signed: true),
            _ => throw Unsupported($"parameter `{parameter.Name}` of {method.Name} has type {type.FullName}; " +
                "new-proof types `bool`, integers of up to 64 bits, admitted classes, and references to and " +
                "read-only spans of 32- and 64-bit integers")
        };
    }

    static int? ElementWidth(TypeReference type) => type.FullName switch
    {
        "System.UInt32" or "System.Int32" => 4,
        "System.UInt64" or "System.Int64" => 8,
        _ => null
    };

    static Result? DescribeResult(MethodDefinition method) => method.ReturnType.FullName switch
    {
        "System.Void" => null,
        "System.Boolean" => new("Bool", ".i32", Boolean: true),
        "System.UInt32" or "System.Int32" or "System.Byte" or "System.SByte" or "System.UInt16"
            or "System.Int16" or "System.Char" => new("W32", ".i32"),
        "System.UInt64" or "System.Int64" => new("W64", ".i64"),
        _ when ObjectTypes.Is(method.ReturnType) => new("ManagedReference", ".object", Object: true),
        var other => throw Unsupported($"{method.Name} returns {other}; new-proof states integer, object and " +
            "void results")
    };

    static string ScalarConstructor(int width) => width == 8 ? ".i64" : ".i32";
    static string WordType(int width) => width == 8 ? "W64" : "W32";

    /// <summary>The theorem's binders, precondition and postcondition, shared by both proof forms.</summary>
    sealed class Specification(MethodDefinition method, Parameter[] parameters, Result? result, bool symbolic,
        bool classes)
    {
        internal MethodDefinition Method { get; } = method;
        internal Parameter[] Parameters { get; } = parameters;
        internal Result? Result { get; } = result;
        internal bool Symbolic { get; } = symbolic;

        /// <summary>The extraction names class fields, under `Extracted.Classes`.</summary>
        internal bool Classes { get; } = classes;

        internal IEnumerable<Parameter> Objects =>
            Parameters.Where(parameter => parameter.Shape == ParameterShape.Object);

        /// <summary>Object arguments make the statement confine the run to `footprint`.</summary>
        internal bool Framed => Objects.Any();

        /// <summary>The objects a stepped body reaches and the facts it needs of each; without it every object
        /// argument assumes a fact of each field of its class.</summary>
        internal ObjectPlan? Plan { get; set; }

        /// <summary>The caller memory the method may write: the stored fields of its object arguments, or a hole
        /// when it is handed a reference.</summary>
        internal void Footprint(Writer lean)
        {
            var references = Parameters.Any(parameter => parameter.Shape == ParameterShape.Reference);
            lean.Doc(references
                ? "Replace with the caller memory the loop may write, as references with their widths in bytes."
                : "The caller memory the method may write: the fields it stores of its object arguments.");
            var entries = Plan is { } plan
                ? plan.Entries.Select(entry => (Name: entry[(entry.LastIndexOf(' ') + 1)..], Entry: entry)).ToArray()
                : Objects.SelectMany(parameter => parameter.Fields.Where(named => named.Stored)
                    .Select(named => (parameter.Name, Entry: $"{named.Lean}.entry {parameter.Name}"))).ToArray();
            // A binder the list does not name is `_`, so the definition elaborates without warnings.
            var binders = references ? Binders
                : Binders.Select(binder =>
                    entries.Any(entry => entry.Name == binder.Name) ? binder : ("_", binder.Type));
            lean.Wrapped("def footprint", Grouped(binders), ": List (Reference × Nat) :=");
            if (references) lean.Line("  sorry -- caller memory the loop may write");
            else lean.Line("  [" + string.Join(", ", entries.Select(entry => entry.Entry)) + "]");
            lean.Line();
        }

        internal IEnumerable<(string Name, string Type)> Binders => Parameters.SelectMany(parameter =>
            parameter.Shape == ParameterShape.ReadOnlySpan
                ? new[] { (parameter.Name, "SpanView"), (parameter.ElementsName, $"List {WordType(parameter.Width)}") }
                : [(parameter.Name, parameter.Lean)]);

        internal string Arguments => string.Join(" ", Binders.Select(binder => binder.Name));

        internal string ArgumentValues => "[" + string.Join(", ", Parameters.Select(parameter => parameter.Shape switch
        {
            ParameterShape.Scalar => $".scalar ({ScalarConstructor(parameter.Width)} {parameter.Name})",
            ParameterShape.Boolean => $".scalar (.i32 (if {parameter.Name} then 1 else 0))",
            ParameterShape.Narrow =>
                $".scalar (.i32 ({parameter.Name}.{(parameter.Signed ? "signExtend" : "zeroExtend")} 32))",
            ParameterShape.Reference => $".reference (.address {parameter.Name})",
            ParameterShape.Object => $".object (.address {parameter.Name})",
            _ => $".bufferSpan {parameter.Name}"
        })) + "]";

        /// <summary>Premises about the caller's memory that frame entry and stepping need.</summary>
        internal IEnumerable<(string Name, string Statement)> MemoryFacts => Parameters.SelectMany(parameter =>
            Plan is not null && parameter.Shape == ParameterShape.Object ? [] : parameter.Shape switch
            {
                ParameterShape.Reference => new[] { (parameter.Name + "Form",
                    $"form initial {parameter.Name} = .ok {parameter.Name}") },
                ParameterShape.ReadOnlySpan => [
                    (parameter.Name + "Valid", $"{parameter.Name}.validate initial = .ok ()"),
                    (parameter.Name + "ReadOnly", $"{parameter.Name}.writable = false"),
                    (parameter.Name + "Contents",
                        $"SpanContents initial {parameter.Name} {parameter.Width} {parameter.ElementsName}")],
                ParameterShape.Object => new[] { (parameter.Name + "Live", $"LiveObject initial {parameter.Name}") }
                    .Concat(parameter.Fields.Select(named =>
                        (FieldFact(parameter, named), FieldPremise(named, "initial", parameter.Name)))),
                _ => []
            }).Concat(Plan?.Premises ?? []);

        internal string MemoryArguments(string initial, string final) => Symbolic ? $" {initial} {final}" : "";

        internal void Placeholders(Writer lean)
        {
            lean.Line("/-- Replace with what callers must guarantee about the arguments, or `True`. -/");
            lean.Wrapped("def Precondition", Grouped(Binders.Concat(Symbolic ? [("initial", "Memory")] : [])),
                ": Prop := sorry");
            lean.Line();
            var subject = Symbolic ? "its result and the caller's memory" : "its result";
            lean.Line($"/-- Replace with what `{Method.Name}` guarantees about {subject}. -/");
            var binders = Binders.Concat(Symbolic ? [("initial", "Memory"), ("final", "Memory")] : []);
            if (Result is not null) binders = binders.Append(("result", Result.Lean));
            lean.Wrapped("def Postcondition", Grouped(binders), ": Prop := sorry");
            lean.Line();
        }

        internal void Statement(Writer lean)
        {
            var binders = Grouped(Binders.Concat((Plan?.Targets ?? []).Select(target => (target, "Reference"))));
            lean.Wrapped("theorem correctness", binders, ": Ensures Extracted.program 0");
            var memory = Symbolic ? "initial.WellFormed" : "initial = Memory.empty";
            var premises = new[] { $"args = {ArgumentValues}", memory }
                .Concat(MemoryFacts.Select(fact => fact.Statement))
                .Append($"Precondition {Arguments}{(Symbolic ? " initial" : "")}");
            lean.Conjunction("    (fun args initial => ", premises, ")");
            var post = $"Postcondition {Arguments}{MemoryArguments("initial", "final")}";
            var binder = Symbolic ? "fun _ initial final results =>" : "fun _ _ _ results =>";
            var confined = Framed ? new[] { $"Confined (footprint {Arguments}) initial final" } : [];
            if (Result is null)
                lean.Conjunction($"    ({binder} ", ["results = []", .. confined, post], ") := by");
            else
                lean.Conjunction($"    ({binder} ∃ result : {Result.Lean}, ",
                    [$"results = [{Result.Encode(ResultWord)}]", .. confined, post + " result"], ") := by");
            var pattern = new[] { "rfl", Symbolic ? "wellFormed" : "rfl" }
                .Concat(MemoryFacts.Select(fact => fact.Name)).Append("assumed");
            lean.Line($"  rintro args initial ⟨{string.Join(", ", pattern)}⟩");
        }

        string ResultWord => Result is { Boolean: true } ? "(if result then 1 else 0)" : "result";

        /// <summary>The postcondition goal at a return: the returned value is matched when it is a word,
        /// and left with the hole when a `Bool` must be chosen for it.</summary>
        internal void Postcondition(Writer lean, string indent, string note)
        {
            if (Result is null or { Boolean: true })
            {
                var choose = Result is null ? "" : ", for the Bool the returned word encodes";
                lean.Noted(indent, "case postcondition => sorry", note + choose);
                return;
            }
            lean.Line(indent + "case postcondition =>");
            lean.Line(indent + "  refine ⟨_, rfl, ?_⟩");
            lean.Noted(indent + "  ", "sorry", note);
        }
    }

    static IEnumerable<string> Grouped(IEnumerable<(string Name, string Type)> binders)
    {
        var groups = new List<(List<string> Names, string Type)>();
        foreach (var (name, type) in binders)
            if (groups.Count > 0 && groups[^1].Type == type) groups[^1].Names.Add(name);
            else groups.Add(([name], type));
        return groups.Select(group => $"({string.Join(" ", group.Names)} : {group.Type})");
    }

    static string StraightLine(Extraction extraction, Specification spec, Body body, Writer lean)
    {
        if (spec.Framed) return ObjectStraightLine(extraction, spec, body, lean);
        var steppable = spec.Parameters.All(parameter => parameter.Shape == ParameterShape.Scalar) &&
            body.Ops.All(Body.Pure);
        var split = !steppable && SplitsOnBooleans(body.Ops, spec.Parameters);
        Header(lean, spec, ["CIL.Verification", "CIL.Safety.SymbolicExecution"],
            steppable || split ? "`postcondition`" : null);
        spec.Placeholders(lean);
        spec.Statement(lean);
        if (steppable) SteppedRun(lean, spec, "  ", "", "Postcondition of the returned value");
        else if (split)
        {
            // `cases` on each `bool` makes every test a literal, so each side steps to one return.
            var booleans = spec.Parameters.Where(parameter => parameter.Shape == ParameterShape.Boolean).ToArray();
            lean.Line("  " + string.Join(" <;> ", booleans.Select(parameter => "cases " + parameter.Name)));
            for (var side = 0; side < 1 << booleans.Length; side++)
            {
                var where = "where " + string.Join(" and ", booleans.Select((parameter, index) =>
                    $"`{parameter.Name}` is {((side >> (booleans.Length - 1 - index) & 1) == 1 ? "true" : "false")}"));
                lean.Line($"  · -- {where}");
                SteppedRun(lean, spec, "    ", (side + 1).ToString(System.Globalization.CultureInfo.InvariantCulture),
                    $"Postcondition of the returned value {where}");
            }
        }
        else
        {
            lean.Line("  -- Choose a fuel bound and step the body with `cil_checked_steps [facts]`,");
            lean.Line("  -- splitting cases where it branches.");
            lean.Noted("  ", "sorry", $"{NotOutlined}{Unstepped(spec.Method, body.Ops, spec.Parameters)}; " +
                "prove its run and Postcondition");
        }
        Footer(lean);
        return lean.ToString();
    }

    /// <summary>The checked run of a body `cil_checked_steps` takes alone, and its postcondition hole; `suffix`
    /// keeps the named holes of each side of a split apart, since a named hole is shared across tactics.</summary>
    static void SteppedRun(Writer lean, Specification spec, string indent, string suffix, string note)
    {
        lean.Line($"{indent}refine ⟨CIL.executionBound Extracted.program 0, ?final{suffix}, ?results{suffix}, " +
            "?run, ?postcondition⟩");
        lean.Line($"{indent}case run => cil_checked_steps");
        spec.Postcondition(lean, indent, note);
    }

    /// <summary>The most `bool` arguments a straight-line outline splits on, one side per combination.</summary>
    const int MaxBooleanSplits = 3;

    /// <summary>Whether a body over words and `bool`s steps once each `bool` is a literal: every operation is
    /// pure or a jump, and every test reads a `bool` argument just loaded.</summary>
    static bool SplitsOnBooleans(string[] ops, Parameter[] parameters)
    {
        var booleans = parameters.Count(parameter => parameter.Shape == ParameterShape.Boolean);
        if (booleans is 0 or > MaxBooleanSplits ||
            parameters.Any(parameter => parameter.Shape is not (ParameterShape.Scalar or ParameterShape.Boolean)))
            return false;
        bool LoadsBoolean(string op) => Regex.Match(op, @"\A\.arg (\d+)(?: \(some \.unsigned8\))?\z") is
            { Success: true } load && parameters[int.Parse(load.Groups[1].Value,
                System.Globalization.CultureInfo.InvariantCulture)].Shape == ParameterShape.Boolean;
        return ops.Select((op, pc) => Body.Pure(op) || LoadsBoolean(op) ||
                Body.Target(op) is not null && !Body.Conditional(op) ||
                Regex.IsMatch(op, @"\A\.br(non)?zero \d+\z") && pc > 0 && LoadsBoolean(ops[pc - 1]))
            .All(stepped => stepped);
    }

    /// <summary>A straight-line body over object arguments: stepped when it loads fields and stores at most one
    /// before it returns, otherwise one hole naming where the walk stopped.</summary>
    static string ObjectStraightLine(Extraction extraction, Specification spec, Body body, Writer lean)
    {
        var views = new FieldViews(extraction);
        var names = new Names();
        foreach (var parameter in spec.Parameters) names.Claim(parameter.Name, parameter.Name);
        var summaries = new Dictionary<int, Callee?>();
        Callee? Summary(int index)
        {
            if (summaries.TryGetValue(index, out var known)) return known;
            var callee = extraction.Methods[index];
            var name = names.Claim(char.ToLowerInvariant(callee.Name[0]) + callee.Name[1..], "callee" + index);
            return summaries[index] = Summarize(extraction, index, name, views);
        }
        var walk = new ObjectWalk(spec, body.Ops, views, Summary);
        var stepped = spec.Parameters.All(parameter => parameter.Shape is ParameterShape.Scalar or
            ParameterShape.Object) && walk.Run(pc => Location(spec.Method, pc));
        if (stepped) spec.Plan = walk.Plan();
        Header(lean, spec, ["CIL.Verification", "CIL.Safety.SymbolicExecution", "CIL.Safety.ObjectFields"],
            stepped ? "`postcondition`" : null);
        if (stepped)
            foreach (var callee in walk.Flattened.OfType<CallStep>().Select(call => call.Callee).Distinct())
                CalleeContract(lean, callee, callee.Index.ToString(System.Globalization.CultureInfo.InvariantCulture));
        spec.Placeholders(lean);
        spec.Footprint(lean);
        spec.Statement(lean);
        if (stepped) ObjectBody(lean, spec, walk, "simp [footprint]");
        else
        {
            lean.Line("  -- Choose a fuel bound and step the body with `cil_checked_steps [facts]`, giving each");
            lean.Line("  -- field load its `facts` and a store its `Owned.store`.");
            var reason = walk.Stopped ?? Unstepped(spec.Method, body.Ops, spec.Parameters);
            lean.Noted("  ", "sorry", $"{NotOutlined}the body meets {reason}; prove its run and Postcondition");
        }
        Footer(lean);
        return lean.ToString();
    }

    /// <summary>Why the outline leaves a body to the author: the first argument or operation that
    /// `cil_checked_steps` cannot take without facts or a case split.</summary>
    static string Unstepped(MethodDefinition method, string[] ops, IEnumerable<Parameter> parameters)
    {
        if (parameters.FirstOrDefault(parameter => parameter.Shape != ParameterShape.Scalar) is { } argument)
            return $"the body reads `{argument.Name}`, " + argument.Shape switch
            {
                ParameterShape.Boolean => "a `bool` that needs a case split",
                ParameterShape.Narrow => "a narrow integer whose extension needs facts",
                ParameterShape.Reference => "a reference into caller memory",
                ParameterShape.Object => "an object whose fields need facts",
                _ => "a span of caller memory"
            };
        var pc = Array.FindIndex(ops, op => !Body.Pure(op));
        return pc < 0 ? "the body has locals" : $"`{ops[pc]}` at {Location(method, pc)} needs facts or a case split";
    }

    /// <summary>The source line of the instruction at `pc`, or its IL offset without a PDB.</summary>
    static string Location(MethodDefinition method, int pc)
    {
        var offset = method.Body.Instructions[pc].Offset;
        return Symbols.Location(method, offset, Path.GetFileName) is { } at
            ? at[..at.LastIndexOf(':')] : $"IL_{offset:x4}";
    }

    // `tags` names the goals the generated tactics leave, or is null when the proof is one hole.
    static void Header(Writer lean, Specification spec, IEnumerable<string> imports, string? tags)
    {
        foreach (var module in imports) lean.Line("import " + module);
        lean.Line();
        var selected = tags is null ? ""
            : $" The tactics leave obligations tagged {tags}, which the holes select with `case`.";
        lean.Comment("/-! ", "    ", $"A starting proof of `{spec.Method.Name}`, generated by " +
            "`leancil new-proof` from its extraction. Each `sorry` is a hole, and `leancil verify` rejects " +
            $"the file until none remains. A hole commented `{NotOutlined.TrimEnd()}` marks a path the " +
            $"outline could not step.{selected} -/");
        lean.Line();
        lean.Line("open CIL.Safety");
        lean.Line("open CIL (W32 W64)");
        if (spec.Classes) lean.Line("open Extracted.Classes");
        lean.Line("namespace ExampleProof");
        lean.Line();
    }

    static void Footer(Writer lean)
    {
        lean.Line();
        lean.Line("#print axioms correctness");
        lean.Line("end ExampleProof");
    }

    /// <summary>Lean identifiers for metadata and PDB names, unique and clear of generated names.</summary>
    sealed class Names
    {
        readonly HashSet<string> used = new(Reserved, StringComparer.Ordinal);

        internal string Claim(string? wanted, string fallback)
        {
            // A parameter named like a generated hypothesis would be captured by the names the proof introduces.
            var name = Regex.IsMatch(wanted ?? "", @"\A[A-Za-z][A-Za-z0-9_]*\z") && !Generated().IsMatch(wanted!)
                ? wanted! : fallback;
            var candidate = name;
            for (var suffix = 1; !used.Add(candidate); suffix++) candidate = name + suffix;
            return candidate;
        }
    }

    /// <summary>The numbered hypotheses and memories an outline's proof introduces after each store, call and
    /// split.</summary>
    [GeneratedRegex(@"\A(?:stored|framed|held|written|output|called|post|returned|found|branch|initial|memory)\d*\z")]
    private static partial Regex Generated();

    /// <summary>Lean source with two-space indentation and lines kept under 100 characters.</summary>
    sealed class Writer
    {
        const int Limit = 100;
        readonly StringBuilder text = new();

        /// <summary>A line, broken after a comma inside brackets when it is too long; Lean reads a
        /// bracketed term across lines, and the deeper indent keeps it inside its tactic.</summary>
        internal void Line(string line = "")
        {
            while (line.Length > Limit)
            {
                var cut = BreakPoint(line);
                if (cut < 0) throw new InvalidOperationException("Generated line exceeds 100 characters: " + line);
                text.Append(line[..(cut + 1)].TrimEnd()).Append('\n');
                var indent = line.Length - line.TrimStart().Length;
                line = new string(' ', indent + 4) + line[(cut + 1)..].TrimStart();
            }
            text.Append(line.TrimEnd()).Append('\n');
        }

        static int BreakPoint(string line)
        {
            var depth = 0;
            var best = -1;
            for (var index = 0; index < Limit && index < line.Length; index++)
            {
                if (line[index] is '(' or '[' or '⟨') depth++;
                else if (line[index] is ')' or ']' or '⟩') depth--;
                else if (line[index] == ',' && depth > 0 && !line[..index].Contains("--")) best = index;
            }
            return best;
        }


        /// <summary>A doc comment wrapped at word boundaries.</summary>
        internal void Doc(string text) => Words("/-- ", "    ", text + " -/");

        internal void Comment(string first, string rest, string text) => Words(first, rest, text);

        /// <summary>`code` with a trailing `--` note, or the note on comment lines above it when long.</summary>
        internal void Noted(string indent, string code, string note)
        {
            if ((indent + code + " -- " + note).Length <= Limit) Line(indent + code + " -- " + note);
            else
            {
                Words(indent + "-- ", indent + "-- ", note);
                Line(indent + code);
            }
        }

        void Words(string first, string rest, string text)
        {
            var current = first;
            foreach (var word in text.Split(' '))
            {
                if (current.Length + word.Length + 1 > Limit && current.Length > first.Length)
                {
                    Line(current);
                    current = rest + word;
                }
                else current += (current == first ? "" : " ") + word;
            }
            Line(current);
        }

        /// <summary>A head followed by binders and a tail, wrapped at binder boundaries.</summary>
        internal void Wrapped(string head, IEnumerable<string> binders, string tail)
        {
            var current = head;
            var continuation = new string(' ', head.Length - head.TrimStart().Length + 4);
            foreach (var part in binders.Append(tail).Where(part => part.Length > 0))
            {
                if (current.Length + 1 + part.Length > Limit)
                {
                    Line(current);
                    current = continuation + part;
                }
                else current += " " + part;
            }
            Line(current);
        }

        /// <summary>Conjuncts joined by `∧`, wrapped after a conjunction, between a prefix and a suffix.</summary>
        internal void Conjunction(string prefix, IEnumerable<string> conjuncts, string suffix)
        {
            var items = conjuncts.ToArray();
            var current = prefix;
            for (var index = 0; index < items.Length; index++)
            {
                var part = items[index] + (index + 1 < items.Length ? " ∧" : suffix);
                if (current.Length + part.Length + 1 > Limit)
                {
                    Line(current);
                    current = "      " + part;
                }
                else current += (current == prefix ? "" : " ") + part;
            }
            Line(current);
        }

        public override string ToString() => text.ToString();
    }
}
