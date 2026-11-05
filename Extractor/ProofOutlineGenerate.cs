using System.Text;
using System.Text.RegularExpressions;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

// The statement, specification placeholders, entry binding and loop scaffolding of an outline.
internal static partial class ProofOutline
{
    /// <summary>A Lean binder of the theorem and how its argument value is written.</summary>
    sealed record Parameter(string Name, ParameterShape Shape, string Lean, int Width)
    {
        internal string ElementsName => Name + "Elements";
    }

    enum ParameterShape { Scalar, Reference, ReadOnlySpan }

    /// <summary>The method's return as a Lean type and value constructor, or none for `void`.</summary>
    sealed record Result(string Lean, string Constructor);

    static readonly HashSet<string> Reserved = new(StringComparer.Ordinal)
    {
        "at", "by", "do", "else", "end", "fun", "from", "have", "if", "in", "let", "match", "then", "with",
        "show", "open", "theorem", "def", "where", "import", "namespace", "section", "case", "this",
        "entry", "loop", "State", "header", "invariant", "measure", "Precondition", "Postcondition",
        "correctness", "args", "initial", "final", "memory", "results", "result", "assumed", "wellFormed",
        "current", "frame", "holds", "recurse", "start", "entered", "setup", "entryFrame", "guard",
        "output", "permitted", "input", "calledFrame", "calledFormed", "returned"
    };

    static Outline Generate(Extraction extraction)
    {
        var method = extraction.Methods[0];
        var emitted = extraction.Emitted[0];
        var names = new Names();
        var parameters = method.Parameters.Select(parameter => Describe(method, parameter, names)).ToArray();
        if (method.HasThis)
            throw Unsupported($"{method.FullName} is an instance method; new-proof outlines static methods");
        var result = DescribeResult(method);
        bool symbolic = parameters.Any(parameter => parameter.Shape != ParameterShape.Scalar);
        var body = new Body(emitted.Ops);
        var lean = new Writer();
        var loops = body.Loops();
        var spec = new Specification(method, parameters, result, symbolic);
        string source;
        if (loops.Count == 0)
            source = StraightLine(extraction, spec, body, lean);
        else if (loops.Count == 1)
            source = LoopProof(extraction, spec, body, loops[0], names, lean);
        else
            throw Unsupported($"{method.FullName} has {loops.Count} loops; new-proof outlines a method with " +
                "at most one");
        var holes = Regex.Matches(source, @"(?<![`\w])sorry(?![`\w])").Count;
        return new(method.FullName, source, holes);
    }

    static NotSupportedException Unsupported(string message) =>
        new("new-proof cannot outline this method: " + message + ".");

    static Parameter Describe(MethodDefinition method, ParameterDefinition parameter, Names names)
    {
        var type = parameter.ParameterType;
        var name = names.Claim(parameter.Name, "argument" + parameter.Index);
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
            _ => throw Unsupported($"parameter `{parameter.Name}` of {method.Name} has type {type.FullName}; " +
                "new-proof types 32- and 64-bit integers, references to them and read-only spans of them")
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
        "System.UInt32" or "System.Int32" or "System.Boolean" or "System.Byte" or "System.SByte" or "System.UInt16"
            or "System.Int16" or "System.Char" => new("W32", ".i32"),
        "System.UInt64" or "System.Int64" => new("W64", ".i64"),
        var other => throw Unsupported($"{method.Name} returns {other}; new-proof states integer and void results")
    };

    static string ScalarConstructor(int width) => width == 8 ? ".i64" : ".i32";
    static string WordType(int width) => width == 8 ? "W64" : "W32";

    /// <summary>The theorem's binders, precondition and postcondition, shared by both proof forms.</summary>
    sealed class Specification(MethodDefinition method, Parameter[] parameters, Result? result, bool symbolic)
    {
        internal MethodDefinition Method { get; } = method;
        internal Parameter[] Parameters { get; } = parameters;
        internal Result? Result { get; } = result;
        internal bool Symbolic { get; } = symbolic;

        internal IEnumerable<(string Name, string Type)> Binders => Parameters.SelectMany(parameter =>
            parameter.Shape == ParameterShape.ReadOnlySpan
                ? new[] { (parameter.Name, "SpanView"), (parameter.ElementsName, $"List {WordType(parameter.Width)}") }
                : [(parameter.Name, parameter.Lean)]);

        internal string Arguments => string.Join(" ", Binders.Select(binder => binder.Name));

        internal string ArgumentValues => "[" + string.Join(", ", Parameters.Select(parameter => parameter.Shape switch
        {
            ParameterShape.Scalar => $".scalar ({ScalarConstructor(parameter.Width)} {parameter.Name})",
            ParameterShape.Reference => $".reference (.address {parameter.Name})",
            _ => $".bufferSpan {parameter.Name}"
        })) + "]";

        /// <summary>Premises about the caller's memory that frame entry and stepping need.</summary>
        internal IEnumerable<(string Name, string Statement)> MemoryFacts => Parameters.SelectMany(parameter =>
            parameter.Shape switch
            {
                ParameterShape.Reference => new[] { (parameter.Name + "Form",
                    $"form initial {parameter.Name} = .ok {parameter.Name}") },
                ParameterShape.ReadOnlySpan => [
                    (parameter.Name + "Valid", $"{parameter.Name}.validate initial = .ok ()"),
                    (parameter.Name + "ReadOnly", $"{parameter.Name}.writable = false"),
                    (parameter.Name + "Contents",
                        $"SpanContents initial {parameter.Name} {parameter.Width} {parameter.ElementsName}")],
                _ => []
            });

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
            var binders = Grouped(Binders);
            lean.Wrapped("theorem correctness", binders, ": Ensures Extracted.program 0");
            var memory = Symbolic ? "initial.WellFormed" : "initial = Memory.empty";
            var premises = new[] { $"args = {ArgumentValues}", memory }
                .Concat(MemoryFacts.Select(fact => fact.Statement))
                .Append($"Precondition {Arguments}{(Symbolic ? " initial" : "")}");
            lean.Conjunction("    (fun args initial => ", premises, ")");
            var post = $"Postcondition {Arguments}{MemoryArguments("initial", "final")}";
            var binder = Symbolic ? "fun _ initial final results =>" : "fun _ _ _ results =>";
            if (Result is null)
                lean.Conjunction($"    ({binder} ", ["results = []", post], ") := by");
            else
                lean.Conjunction($"    ({binder} ∃ result : {Result.Lean}, ",
                    [$"results = [.scalar ({Result.Constructor} result)]", post + " result"], ") := by");
            var pattern = new[] { "rfl", Symbolic ? "wellFormed" : "rfl" }
                .Concat(MemoryFacts.Select(fact => fact.Name)).Append("assumed");
            lean.Line($"  rintro args initial ⟨{string.Join(", ", pattern)}⟩");
        }

        /// <summary>The tactic text that proves the returned value meets the postcondition shape.</summary>
        internal string ResultShape => Result is null ? "refine ⟨rfl, ?_⟩" : "refine ⟨_, rfl, ?_⟩";
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
        var steppable = !spec.Symbolic && body.Ops.All(Body.Pure);
        Header(lean, spec, ["CIL.Verification", "CIL.Safety.SymbolicExecution"], loop: false);
        spec.Placeholders(lean);
        spec.Statement(lean);
        if (steppable)
        {
            lean.Line("  refine ⟨CIL.executionBound Extracted.program 0, ?final, ?results, ?run, ?postcondition⟩");
            lean.Line("  case run => cil_checked_steps");
            lean.Line("  case postcondition =>");
            lean.Line("    " + spec.ResultShape);
            lean.Noted("    ", "sorry", "Postcondition of the returned value");
        }
        else
        {
            var reason = spec.Symbolic ? "reads caller memory" : "branches, calls or can fault";
            lean.Line($"  -- The body {reason}: choose a fuel bound and step it with");
            lean.Line("  -- `cil_checked_steps [facts]`, splitting cases where it branches.");
            lean.Line("  sorry -- the run and Postcondition of its result");
        }
        Footer(lean);
        return lean.ToString();
    }

    static void Header(Writer lean, Specification spec, IEnumerable<string> imports, bool loop)
    {
        lean.Line("import Extracted");
        foreach (var module in imports) lean.Line("import " + module);
        lean.Line();
        var tags = loop ? "`invariant`, `measure`, `postcondition` and `precondition` (at a call)"
            : "`run` and `postcondition`";
        lean.Comment("/-! ", "    ", $"A starting proof of `{spec.Method.Name}`, generated by " +
            "`leancil new-proof` from " +
            "its extraction. Each `sorry` is a hole, and `leancil verify` rejects the file until none remains. " +
            $"The tactics leave obligations tagged {tags}, which the holes select with `case`. -/");
        lean.Line();
        lean.Line("open CIL.Safety");
        lean.Line("open CIL (W32 W64)");
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
            var name = Regex.IsMatch(wanted ?? "", @"\A[A-Za-z][A-Za-z0-9_]*\z") ? wanted! : fallback;
            var candidate = name;
            for (var suffix = 1; !used.Add(candidate); suffix++) candidate = name + suffix;
            return candidate;
        }
    }

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
