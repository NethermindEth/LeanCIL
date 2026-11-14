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

        /// <summary>The C# name of a parameter the outline binds under another name, or null when they agree.
        /// </summary>
        internal string? Source { get; init; }

        /// <summary>The element class and length binders of an array argument.</summary>
        internal string ElementName => Name + "Element";
        internal string LengthName => Name + "Length";

        /// <summary>A span or array argument the method may write through, with authority over its
        /// elements.</summary>
        internal bool Writable { get; init; }

        /// <summary>The premise naming a span's access mode, and its statement.</summary>
        internal string Mode => Name + (Writable ? "Writable" : "ReadOnly");
        internal string ModeStatement => $"{Name}.writable = {(Writable ? "true" : "false")}";

        /// <summary>The named fields of an object argument's class.</summary>
        internal ViewField[] Fields { get; init; } = [];

        /// <summary>The element of a word or value array argument, as a Lean `ArrayElement` term such as
        /// `.signed32`.</summary>
        internal string ArrayElement { get; init; } = "";

        /// <summary>The element of a word or value array argument, as the extraction names it.</summary>
        internal Arrays.Element? Element { get; init; }

        /// <summary>The element term a value array argument's `ArrayElement` names, when it is too long to state
        /// inline and no named field's `elementType` names it.</summary>
        internal string? ElementDefinition { get; init; }

        /// <summary>The premise that a value array argument is a whole live array of its length.</summary>
        internal string WholeName => Name + "Whole";

        /// <summary>Whether the theorem names the argument's elements: a span or array the method only
        /// reads.</summary>
        internal bool Listed => Shape is ParameterShape.WordArray or ParameterShape.Span && !Writable;

        /// <summary>The caller memory a written span or array lends the method.</summary>
        internal string FootprintTerm => Shape == ParameterShape.WordArray ? $"{Name}.storage.footprint"
            : $"{Name}.footprint";
    }

    /// <summary>How an argument is bound; `StructReference` is `this` of a struct instance method, a reference to
    /// the caller's struct. `StructValue` binds every byte, including padding, of a private by-value copy.</summary>
    /// <remarks>An `Array` is an array of class references, bound with the element class and length its
    /// allocation records, since covariance lets it hold a class derived from its static element type. A
    /// `WordArray` is an array of 32- or 64-bit integers, bound as an `ArrayView` with its elements, and a
    /// `ValueArray` an array of other value elements, bound by its origin and its length. An object-field store
    /// adds a whole-array premise to a word array without changing its element view.</remarks>
    enum ParameterShape
    {
        Scalar, Boolean, Narrow, Reference, Span, Object, StructReference, StructValue, Array, WordArray, ValueArray
    }

    /// <summary>The method's return as a Lean type and value constructor, or none for `void`; a `bool`
    /// is a `Bool` the returned word encodes as 1 or 0, an object a possibly null reference, and a value array
    /// the view of its origin, length and element.</summary>
    sealed record Result(string Lean, int Width, bool Boolean = false, bool Object = false,
        bool Array = false)
    {
        /// <summary>The value constructor of the result: by word width for a scalar.</summary>
        internal string Constructor => Object ? ".object" : Array ? ".array" : Width == 8 ? ".i64" : ".i32";

        internal string Encode(string term) => Object ? $".object {term}"
            : Array ? $".array {term}" : $".scalar ({Constructor} {term})";
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
        "confined", "target", "objectEntry", "entryMemory", "entryFrames", "exited", "enter"
    };

    // `module` is the keyed extraction module the outline imports, ahead of the library modules its form needs.
    static Outline Generate(Extraction extraction, string module)
    {
        var method = extraction.Methods[0];
        var emitted = extraction.Emitted[0];
        var names = new Names();
        var views = new FieldViews(extraction);
        var receiver = method.HasThis ? new[] { Receiver(method, names, views) } : [];
        var parameters = WrittenArrays(method, receiver.Concat(method.Parameters.Select(parameter =>
            Describe(method, parameter, names, views, extraction.Architecture))).ToArray(), emitted.Operations,
            new Body(emitted.Operations).Loops().Count);
        var result = DescribeResult(method, extraction.Architecture);
        bool symbolic = parameters.Any(parameter => parameter.Shape is ParameterShape.Reference or
            ParameterShape.Span or ParameterShape.Object or ParameterShape.StructReference or
            ParameterShape.Array or ParameterShape.WordArray or ParameterShape.ValueArray);
        var body = new Body(emitted.Operations);
        var lean = new Writer();
        var loops = body.Loops();
        var spec = new Specification(method, parameters, result, symbolic, extraction.Views.Length > 0);
        string source;
        var structReceiver = parameters.Any(parameter => parameter.Shape == ParameterShape.StructReference);
        if (loops.Count > 0 && parameters.FirstOrDefault(parameter => parameter.Shape == ParameterShape.Array) is
            { } array)
            throw Unsupported($"parameter `{array.Name}` of {method.Name} is an array of class references, which " +
                "new-proof outlines only in bodies without loops");
        if (structReceiver && parameters.FirstOrDefault(parameter => parameter.Shape == ParameterShape.ValueArray)
            is { } structValues)
            throw Unsupported($"parameter `{structValues.Name}` of {method.FullName} is an array of values, which " +
                "new-proof outlines only beside class instances, not a struct receiver");
        if (loops.Count > 0 && parameters.FirstOrDefault(parameter => parameter.Shape == ParameterShape.ValueArray)
            is { } values)
            throw Unsupported($"parameter `{values.Name}` of {method.Name} is an array of values, which new-proof " +
                "outlines only in bodies without loops");
        if (result is { Array: true } && (loops.Count > 0 || !spec.Framed))
            throw Unsupported($"{method.Name} returns an array, which new-proof states only of straight-line " +
                "bodies over objects and arrays");
        var spanStore = loops.Count == 0 ? SpanStores(extraction, 0) : null;
        if (loops.Count == 0 && spanStore is null && parameters.Any(parameter => parameter.Writable))
            throw Unsupported($"{method.FullName} writes a span outside a loop other than by storing its value " +
                "into `target[0]`; new-proof follows a span written from the front by a loop or that one store");
        if (spanStore is { } store)
            source = SpanStoreLine(spec, store.Op, lean);
        else if (structReceiver && loops.Count > 0)
            source = new ReceiverLoop(spec, body, lean).Generate();
        else if (structReceiver)
            source = StructStraightLine(spec, body, names, lean);
        else if (loops.Count == 0 && !spec.Framed && ArrayRead(extraction, spec, body.Operations) is { } read)
            source = ArrayReadLine(spec, read, lean);
        else if (loops.Count == 0)
            source = StraightLine(extraction, spec, body, lean);
        // Loops in sequence chain from each exit into the next; a nested or interleaved loop has no such order.
        else if (loops.Zip(loops.Skip(1)).All(pair => pair.First.Latch < pair.Second.Head))
        {
            LoopPlan(extraction, spec, body);
            source = LoopProof(extraction, spec, body, loops, names, lean);
        }
        else
            throw Unsupported($"{method.FullName} has {loops.Count} loops, with back edges at " +
                string.Join(", ", loops.Select(loop => Location(method, loop.Latch))) + ", one inside another; " +
                "new-proof chains loops in sequence only");
        source = $"import {module}\n" + source;
        var holes = Regex.Matches(source, @"(?<![`\w])sorry(?![`\w])").Count;
        var paths = Regex.Matches(source, "-- " + NotOutlined).Count;
        return new(method.FullName, source, holes - paths, paths);
    }

    /// <summary>`parameters` with the array a loop stores into, by index or through a writable span over it,
    /// marked written; a loop's store is followed only into a method's one array argument. A straight-line store
    /// stays a hole over the array's contents.</summary>
    static Parameter[] WrittenArrays(MethodDefinition method, Parameter[] parameters, Operation[] ops, int loops)
    {
        var arrays = parameters.Where(parameter => parameter.Shape == ParameterShape.WordArray).ToArray();
        if (loops == 0 || arrays.Length == 0 || !ops.Any(op => op is Memory
            { Operation: ArrayStore or ArraySpan { Element.Compound: false, Writable: true } })) return parameters;
        if (arrays.Length > 1)
            throw Unsupported($"{method.FullName} stores into one of {arrays.Length} array arguments in a loop; " +
                "new-proof follows a loop's stores into a method's one array argument");
        return parameters.Select(parameter => parameter == arrays[0] ? parameter with { Writable = true } : parameter)
            .ToArray();
    }

    static NotSupportedException Unsupported(string message) =>
        new("new-proof cannot outline this method: " + message + ".");

    /// <summary>`this` of an instance method, named for its class.</summary>
    static Parameter Receiver(MethodDefinition method, Names names, FieldViews views)
    {
        var type = method.DeclaringType;
        if (type.IsValueType && !type.HasGenericParameters)
            return new(names.Claim(char.ToLowerInvariant(type.Name[0]) + type.Name[1..], "receiver"),
                ParameterShape.StructReference, "Reference", 8);
        if (!ObjectTypes.Is(type))
            throw Unsupported($"{method.FullName} is an instance method of {type.FullName}, which is not an " +
                "admitted class; new-proof binds `this` of class instances only");
        return Instance(names.Claim(char.ToLowerInvariant(type.Name[0]) + type.Name[1..], "receiver"), type, views);
    }

    static Parameter Instance(string name, TypeReference type, FieldViews views) =>
        new(name, ParameterShape.Object, "Reference", 8) { Fields = views.Of(type) };

    static Parameter Describe(MethodDefinition method, ParameterDefinition parameter, Names names, FieldViews views,
        string architecture)
    {
        var name = names.Claim(parameter.Name, "argument" + parameter.Index);
        var bound = Bind(method, parameter, name, views, architecture);
        return name == parameter.Name || string.IsNullOrEmpty(parameter.Name) ? bound
            : bound with { Source = parameter.Name };
    }

    /// <summary>The binder `name` of `parameter`, shaped by its type.</summary>
    static Parameter Bind(MethodDefinition method, ParameterDefinition parameter, string name, FieldViews views,
        string architecture)
    {
        var type = parameter.ParameterType;
        if (ObjectTypes.Is(type)) return Instance(name, type, views);
        if (ReferenceArrays.Is(type)) return new(name, ParameterShape.Array, "Reference", 8);
        if (type is ArrayType { IsVector: true } array && WordArrayElement(array.ElementType) is { } word)
            return new(name, ParameterShape.WordArray, "ArrayView", ElementWidth(array.ElementType)!.Value)
                { ArrayElement = word.Expression, Element = word };
        if (Arrays.Of(type, architecture) is { } values)
        {
            // A struct, vector or enumeration element names its type by a quoted identity, often wider than a line.
            var named = views.ElementType(values);
            var quoted = named is null && values.Compound;
            return new(name, ParameterShape.ValueArray, "Reference", values.Width)
            {
                ArrayElement = named ?? (quoted ? name + "Element" : values.Expression),
                ElementDefinition = quoted ? values.Expression : null,
                Element = values
            };
        }
        if (type is ByReferenceType reference && ElementWidth(reference.ElementType) is { } width)
            return new(name, ParameterShape.Reference, "Reference", width);
        if (Spans.Is(type) && type is GenericInstanceType span &&
            span.ElementType.FullName is "System.ReadOnlySpan`1" or "System.Span`1" &&
            ElementWidth(span.GenericArguments[0]) is { } element)
            return new(name, ParameterShape.Span, "SpanView", element)
                { Writable = span.ElementType.FullName == "System.Span`1" };
        if (MetadataValidation.IsAggregate(type, method.Module) && !MetadataValidation.IsByRefLike(type) &&
            Spans.ElementWidth(type, architecture) is { } size)
            return new(name, ParameterShape.StructValue, $"Vector (BitVec 8) {size}", size);
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
                "new-proof types `bool`, integers of up to 64 bits, admitted classes, arrays of class references " +
                "and of values, reference-free structs, and references to and spans of 32- and 64-bit integers")
        };
    }

    /// <summary>The `ArrayElement` the extraction gives an array of 32- or 64-bit integers.</summary>
    static Arrays.Element? WordArrayElement(TypeReference type) =>
        ElementWidth(type) is null ? null : Arrays.Primitive(type);

    static int? ElementWidth(TypeReference type) => type.FullName switch
    {
        "System.UInt32" or "System.Int32" => 4,
        "System.UInt64" or "System.Int64" => 8,
        _ => null
    };

    static Result? DescribeResult(MethodDefinition method, string architecture) => method.ReturnType.FullName switch
    {
        "System.Void" => null,
        "System.Boolean" => new("Bool", 4, Boolean: true),
        "System.UInt32" or "System.Int32" or "System.Byte" or "System.SByte" or "System.UInt16"
            or "System.Int16" or "System.Char" => new("W32", 4),
        "System.UInt64" or "System.Int64" => new("W64", 8),
        _ when ObjectTypes.Is(method.ReturnType) => new("ManagedReference", 0, Object: true),
        _ when Arrays.Of(method.ReturnType, architecture) is not null => new("ArrayView", 0, Array: true),
        var other => throw Unsupported($"{method.Name} returns {other}; new-proof states integer, object, " +
            "value array and void results")
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

        /// <summary>This specification stated of any well-formed initial memory rather than the empty one.
        /// </summary>
        internal Specification InMemory() => new(Method, Parameters, Result, true, Classes) { NonNull = NonNull };

        internal IEnumerable<Parameter> Objects =>
            Parameters.Where(parameter => parameter.Shape == ParameterShape.Object);

        internal IEnumerable<Parameter> Arrays =>
            Parameters.Where(parameter => parameter.Shape == ParameterShape.Array);

        internal IEnumerable<Parameter> ValueArrays =>
            Parameters.Where(parameter => parameter.Shape == ParameterShape.ValueArray);

        /// <summary>Object and array arguments make the statement confine the run to `footprint`.</summary>
        internal bool Framed => Objects.Any() || Arrays.Any() || ValueArrays.Any();

        /// <summary>The objects a stepped body reaches and the facts it needs of each; without it every object
        /// argument assumes a fact of each field of its class.</summary>
        internal ObjectPlan? Plan { get; set; }

        /// <summary>The caller memory the method may write: the stored fields of its object arguments and the
        /// bytes of its writable spans, or a hole when it is handed a reference.</summary>
        internal void Footprint(Writer lean)
        {
            // Which elements of an array argument an unstepped body writes is the author's to state.
            var loop = Parameters.Any(parameter => parameter.Shape == ParameterShape.Reference);
            var references = loop || Plan is null && (Arrays.Any() || ValueArrays.Any());
            var writer = loop ? "loop" : "method";
            var lent = Parameters.Where(parameter => parameter.Writable).ToArray();
            var spans = lent.Select(parameter => parameter.Name).ToArray();
            var parts = (Arrays.Any() ? new[] { "the fields and elements it stores of its arguments" }
                    : Objects.Any() ? ["the fields it stores of its object arguments"] : [])
                .Concat(lent.Any(parameter => parameter.Shape == ParameterShape.Span)
                    ? ["the bytes of its writable spans"] : [])
                .Concat(lent.Any(parameter => parameter.Shape == ParameterShape.WordArray)
                    ? ["the elements of the array it stores into"] : []);
            if (references) lean.Quiet();
            lean.Doc(references
                ? $"Replace with the caller memory the {writer} may write, as references with their widths in bytes."
                : $"The caller memory the method may write: {string.Join(" and ", parts)}.");
            var entries = Plan is { } plan
                ? plan.Entries.Select(entry => (Name: entry[(entry.LastIndexOf(' ') + 1)..], Entry: entry)).ToArray()
                : Objects.SelectMany(parameter => parameter.Fields.Where(named => named.Stored)
                    .Select(named => (parameter.Name, Entry: $"{named.Lean}.entry {parameter.Name}"))).ToArray();
            // A binder the list does not name is `_`, so the definition elaborates without warnings.
            var binders = references ? Binders
                : Binders.Select(binder => entries.Any(entry =>
                    Regex.IsMatch(entry.Entry, $@"(?<![\w.]){binder.Name}(?!\w)")) || spans.Contains(binder.Name)
                    ? binder : ("_", binder.Type));
            lean.Wrapped("def footprint", Grouped(binders), ": List (Reference × Nat) :=");
            if (references) lean.Line($"  sorry -- caller memory the {writer} may write");
            else lean.Line("  " + string.Join(" ++ ", (entries.Length > 0 || spans.Length == 0
                ? ["[" + string.Join(", ", entries.Select(entry => entry.Entry)) + "]"] : Array.Empty<string>())
                .Concat(lent.Select(parameter => parameter.FootprintTerm))));
            lean.Line();
        }

        internal IEnumerable<(string Name, string Type)> Binders => Parameters.SelectMany(parameter =>
            parameter.Shape switch
            {
                ParameterShape.Array => new[] { (parameter.Name, parameter.Lean),
                    (parameter.ElementName, "CIL.Extraction.TypeExpr"), (parameter.LengthName, "Nat") },
                ParameterShape.ValueArray => [(parameter.Name, parameter.Lean), (parameter.LengthName, "Nat")],
                _ when parameter.Listed =>
                    [(parameter.Name, parameter.Lean), (parameter.ElementsName, $"List {WordType(parameter.Width)}")],
                _ => [(parameter.Name, parameter.Lean)]
            });

        internal string Arguments => string.Join(" ", Binders.Select(binder => binder.Name));

        internal string ArgumentValues => "[" + string.Join(", ", Parameters.Select(parameter => parameter.Shape switch
        {
            ParameterShape.Scalar => $".scalar ({ScalarConstructor(parameter.Width)} {parameter.Name})",
            ParameterShape.Boolean => $".scalar (.i32 (if {parameter.Name} then 1 else 0))",
            ParameterShape.Narrow =>
                $".scalar (.i32 ({parameter.Name}.{(parameter.Signed ? "signExtend" : "zeroExtend")} 32))",
            ParameterShape.StructValue => $".scalar (.aggregate (List.ofFn {parameter.Name}.get))",
            ParameterShape.Reference or ParameterShape.StructReference => $".reference (.address {parameter.Name})",
            ParameterShape.Object or ParameterShape.Array => $".object (.address {parameter.Name})",
            ParameterShape.WordArray => $".array {parameter.Name}",
            ParameterShape.ValueArray =>
                $".array ⟨.address {parameter.Name}, {parameter.LengthName}, {parameter.ArrayElement}⟩",
            _ => $".bufferSpan {parameter.Name}"
        })) + "]";

        /// <summary>Premises about the caller's memory that frame entry and stepping need.</summary>
        internal IEnumerable<(string Name, string Statement)> MemoryFacts => Parameters.SelectMany(parameter =>
            Plan is not null && parameter.Shape is ParameterShape.Object or ParameterShape.Array ? []
            : parameter.Shape switch
            {
                ParameterShape.Reference => new[] { (parameter.Name + "Form",
                    $"form initial {parameter.Name} = .ok {parameter.Name}") },
                // A written span's bytes need not be readable: it needs only authority over its elements.
                ParameterShape.Span when parameter.Writable => [
                    (parameter.Name + "Valid", $"{parameter.Name}.validate initial = .ok ()"),
                    (parameter.Mode, parameter.ModeStatement),
                    (parameter.Name + "Width", $"{parameter.Name}.width = {parameter.Width}"),
                    (parameter.Name + "Authority", $"SpanWritable initial (footprint {Arguments}) {parameter.Name}")],
                ParameterShape.Span => [
                    (parameter.Name + "Valid", $"{parameter.Name}.validate initial = .ok ()"),
                    (parameter.Mode, parameter.ModeStatement),
                    (parameter.Name + "Contents",
                        $"SpanContents initial {parameter.Name} {parameter.Width} {parameter.ElementsName}")],
                // A stored-into array needs only authority over its storage span's elements.
                ParameterShape.WordArray when parameter.Writable => [
                    (parameter.Name + "Valid", $"{parameter.Name}.validate initial = .ok ()"),
                    (parameter.Name + "Type", $"{parameter.Name}.elementType = {parameter.ArrayElement}"),
                    (parameter.Name + "Authority",
                        $"SpanWritable initial (footprint {Arguments}) {parameter.Name}.storage")],
                // An array's elements are the bytes of its storage span; a null array has none.
                ParameterShape.WordArray => [
                    (parameter.Name + "Valid", $"{parameter.Name}.validate initial = .ok ()"),
                    (parameter.Name + "Type", $"{parameter.Name}.elementType = {parameter.ArrayElement}"),
                    (parameter.Name + "Contents", $"SpanContents initial {parameter.Name}.storage {parameter.Width} " +
                        parameter.ElementsName)],
                ParameterShape.Object => new[] { (parameter.Name + "Live", $"LiveObject initial {parameter.Name}") }
                    .Concat(parameter.Fields.Select(named =>
                        (FieldFact(parameter, named), FieldPremise(named, "initial", parameter.Name)))),
                ParameterShape.Array => [(parameter.Name + "Live", $"ReferenceArray.Live initial {parameter.Name} " +
                    $"{parameter.ElementName} {parameter.LengthName}")],
                ParameterShape.ValueArray => [(parameter.WholeName, $"WholeArray initial {parameter.ArrayElement} " +
                    $"{parameter.Name} {parameter.LengthName}")],
                _ => []
            }).Concat(Plan?.Premises ?? []);

        internal string MemoryArguments(string initial, string final) => Symbolic ? $" {initial} {final}" : "";

        /// <summary>The array arguments whose null the proof excludes from `Precondition`, since the body reads
        /// their length before any element.</summary>
        internal Parameter[] NonNull { get; set; } = [];

        internal void Placeholders(Writer lean)
        {
            lean.Quiet();
            var binders = Grouped(Binders.Concat(Symbolic ? [("initial", "Memory")] : []));
            if (NonNull.Length == 0)
            {
                lean.Line("/-- Replace with what callers must guarantee about the arguments, or `True`. -/");
                lean.Wrapped("def Precondition", binders, ": Prop := sorry");
            }
            else
            {
                lean.Doc("Replace `sorry` with what else callers must guarantee about the arguments, or `True`.");
                lean.Wrapped("def Precondition", binders, ": Prop :=");
                foreach (var array in NonNull)
                    lean.Comment("  -- ", "  -- ", $"`{array.Name}` is not null: " +
                        $"`{array.Source ?? array.Name}.Length` throws on a null array.");
                lean.Conjunction("  ", NonNull.Select(array => $"{array.Name}.reference ≠ .null").Append("sorry"), "");
            }
            lean.Line();
            var subject = Symbolic ? "its result and the caller's memory" : "its result";
            lean.Quiet();
            lean.Line($"/-- Replace with what `{Method.Name}` guarantees about {subject}. -/");
            var results = Binders.Concat(Symbolic ? [("initial", "Memory"), ("final", "Memory")] : []);
            if (Result is not null) results = results.Append(("result", Result.Lean));
            lean.Wrapped("def Postcondition", Grouped(results), ": Prop := sorry");
            lean.Line();
        }

        internal void Statement(Writer lean)
        {
            var binders = Grouped(Binders.Concat(Plan?.Targets ?? []));
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
            var names = pattern.ToArray();
            lean.Wrapped("  rintro args initial", names.Select((name, index) =>
                (index == 0 ? "⟨" : "") + name + (index + 1 < names.Length ? "," : "⟩")), "");
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
        if (spec.Framed) return ObjectStraightLine(extraction, spec, body, lean)!;
        var steppable = spec.Parameters.All(parameter => parameter.Shape is ParameterShape.Scalar or
            ParameterShape.StructValue) && body.Operations.All(op => Body.Pure(op) || Steps(spec.Method, op));
        var split = !steppable && SplitsOnBooleans(body.Operations, spec.Parameters);
        var paths = steppable || split ? null : ScalarPaths(spec, body.Operations);
        // A body over words that calls helpers composes them through stub contracts, as a body over objects does.
        if (!steppable && !split && paths is null &&
            spec.Parameters.All(parameter => parameter.Shape == ParameterShape.Scalar) &&
            body.Operations.Any(op => op is Call { Kind: CallKind.Static }) &&
            ObjectStraightLine(extraction, spec, body, lean, stubsOnly: true) is { } composed)
            return composed;
        Header(lean, spec, paths is null ? ["CIL.Verification", "CIL.Safety.SymbolicExecution"]
                : ["CIL.Verification", "CIL.Safety.SymbolicExecution", "CIL.Safety.LoopObligations"],
            steppable || split || paths is not null ? "`postcondition`" : null);
        spec.Placeholders(lean);
        spec.Statement(lean);
        if (steppable) SteppedRun(lean, spec, "  ", "", "Postcondition of the returned value");
        else if (paths is not null) ScalarRun(lean, spec, paths);
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
            lean.Noted("  ", "sorry", $"{NotOutlined}{Unstepped(spec.Method, body.Operations, spec.Parameters)}; " +
                "prove its run and Postcondition");
        }
        Footer(lean);
        return lean.ToString();
    }

    /// <summary>A frame, field or duplicate operation the stepping tactics take without facts: a local access
    /// other than to a narrow integer local, an aggregate initialisation or a field access whose load is not
    /// sign-extending.</summary>
    static bool Steps(MethodDefinition method, Operation op) => op switch
    {
        Local load => !NarrowLocal(method, load.Index),
        SetLocal store => !NarrowLocal(method, store.Index),
        _ => op is LocalAddress or AggregateTransfer { Access: AggregateAccess.Initialize } or
            StackOperation { Kind: StackOpcode.Dup } or
            StructField { Access: FieldAccess.Address or FieldAccess.Store or FieldAccess.LoadAggregate or
                FieldAccess.StoreAggregate } or StructField { Access: FieldAccess.Load, Signed: false }
    };

    /// <summary>Whether local `index` is a declared local of a narrow integer type, whose loads and stores the
    /// outlines leave to the author. Argument homes follow the declared locals and are never narrow.</summary>
    static bool NarrowLocal(MethodDefinition method, int index) => index < method.Body.Variables.Count &&
        LeanEmitter.Narrow(method.Body.Variables[index].VariableType) is not null;

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
    static bool SplitsOnBooleans(Operation[] ops, Parameter[] parameters)
    {
        var booleans = parameters.Count(parameter => parameter.Shape == ParameterShape.Boolean);
        if (booleans is 0 or > MaxBooleanSplits ||
            parameters.Any(parameter => parameter.Shape is not (ParameterShape.Scalar or ParameterShape.Boolean)))
            return false;
        bool LoadsBoolean(Operation op) => op is Arg { Narrow: null or Narrowing.Unsigned8 } load &&
            parameters[load.Index].Shape == ParameterShape.Boolean;
        return ops.Select((op, pc) => Body.Pure(op) || LoadsBoolean(op) || op is Jump { Kind: JumpKind.Always } ||
                op is Jump { Kind: JumpKind.IfZero or JumpKind.IfNonzero } && pc > 0 && LoadsBoolean(ops[pc - 1]))
            .All(stepped => stepped);
    }

    /// <summary>A straight-line body over object arguments: stepped when it loads fields and stores at most one
    /// before it returns, otherwise one hole naming where the walk stopped. With `stubsOnly`, for a body over
    /// words, null unless the walk steps it, each call through a stub contract or the contract of a helper that
    /// keeps locals.</summary>
    static string? ObjectStraightLine(Extraction extraction, Specification spec, Body body, Writer lean,
        bool stubsOnly = false)
    {
        var views = new FieldViews(extraction);
        var names = new Names();
        foreach (var parameter in spec.Parameters) names.Claim(parameter.Name, parameter.Name);
        var summaries = new Dictionary<int, Callee?>();
        var calleeNames = new Dictionary<int, string>();
        string CalleeName(int index)
        {
            if (calleeNames.TryGetValue(index, out var claimed)) return claimed;
            var callee = extraction.Methods[index];
            return calleeNames[index] =
                names.Claim(char.ToLowerInvariant(callee.Name[0]) + callee.Name[1..], "callee" + index);
        }
        Callee? Summary(int index) => summaries.TryGetValue(index, out var known) ? known
            : summaries[index] = Summarize(extraction, index, CalleeName(index), views, splits: true);
        var stubs = new Dictionary<int, Stub?>();
        Stub? Stubbed(int index) => stubs.TryGetValue(index, out var known) ? known
            : stubs[index] = StubOf(extraction, index, CalleeName(index));
        // A body over words reads a callee's contract from its body only where no stub states it: a helper that
        // keeps locals, whose homes change the memory a stub's `post` keeps.
        Func<int, Callee?> summarized = !stubsOnly ? Summary
            : index => Stubbed(index) is null && Summary(index) is { Walk.NumericHomes: true } read ? read : null;
        var numericHomes = HasNumericObjectHomes(spec.Method) || body.Operations
            .OfType<Call>().Where(call => call.Kind != CallKind.Tail)
            .Any(call => summarized(call.Method)?.Walk.NumericHomes == true);
        // Local homes belong to the entry memory, so the statement accepts any well-formed entry memory.
        if (numericHomes && !spec.Symbolic) spec = spec.InMemory();
        var walk = new ObjectWalk(spec, body.Operations, views, summarized, numericHomes: numericHomes,
            stubs: Stubbed);
        var stepped = spec.Parameters.All(parameter => parameter.Shape is ParameterShape.Scalar or
            ParameterShape.Object or ParameterShape.Array or ParameterShape.ValueArray or ParameterShape.WordArray) &&
            walk.Run(pc => Location(spec.Method, pc));
        if (stubsOnly && !stepped) return null;
        if (stepped) spec.Plan = walk.Plan();
        string[] imports = ["CIL.Verification", "CIL.Safety.SymbolicExecution", "CIL.Safety.ObjectFields"];
        if (numericHomes) imports = [.. imports, "CIL.Safety.LoopScaffold"];
        if (spec.Parameters.Any(parameter => parameter.Shape == ParameterShape.WordArray))
            imports = [.. imports, "CIL.Safety.ArrayContents", "CIL.Safety.LoopCallerFacts"];
        var fresh = stepped ? walk.Flattened.OfType<Allocation>().FirstOrDefault() : null;
        if (spec.Arrays.Any() || fresh is not null) imports = [.. imports, "CIL.Safety.ReferenceArrayElements"];
        var stubbed = stepped ? walk.Flattened.OfType<StubCall>().Select(call => call.Stub).Distinct().ToArray() : [];
        // A helper's contract proof closes each side that throws from its `pre`.
        var thrown = stepped && walk.Flattened.OfType<CallStep>().Any(call =>
            call.Callee.Walk.Flattened.Any(step => step is Thrown));
        if (stubbed.Length > 0 || thrown) imports = [.. imports, "CIL.Safety.LoopObligations"];
        Header(lean, spec, imports, stepped ? "`postcondition`" : null);
        if (stepped)
            foreach (var callee in walk.Flattened.OfType<CallStep>().Select(call => call.Callee).Distinct())
                CalleeContract(lean, callee, callee.Index.ToString(System.Globalization.CultureInfo.InvariantCulture),
                    spec.Method.Name);
        foreach (var stub in stubbed) StubContract(lean, extraction, stub, spec.Method.Name);
        if (fresh is not null)
        {
            lean.Doc($"The element class of the array `{spec.Method.Name}` allocates, as its `newarr` names it.");
            lean.Wrapped($"def {fresh.Element} : CIL.Extraction.TypeExpr := .object", [fresh.Scope, fresh.Name], "");
            lean.Line();
        }
        foreach (var array in spec.ValueArrays.Where(array => array.ElementDefinition is not null))
            ElementDefinition(lean, array);
        spec.Placeholders(lean);
        if (spec.Framed) spec.Footprint(lean);
        if (stepped && numericHomes) ObjectEntry(lean, spec, "objectEntry", "0");
        spec.Statement(lean);
        if (stepped) ObjectBody(lean, spec, walk, "simp [footprint]");
        else
        {
            lean.Line("  -- Choose a fuel bound and step the body with `cil_checked_steps [facts]`, giving a store");
            lean.Line("  -- its `Owned.store`; a scalar field's load is read from its fact in the context.");
            var reason = walk.Stopped ?? Unstepped(spec.Method, body.Operations, spec.Parameters);
            lean.Noted("  ", "sorry", $"{NotOutlined}the body meets {reason}; prove its run and Postcondition");
        }
        Footer(lean);
        return lean.ToString();
    }

    /// <summary>The outline text that builds contract evidence by name: the final memory, output and facts a
    /// `Holds` proof gives `MethodContract.Holds.intro` for a returning run.</summary>
    static class ContractEvidence
    {
        /// <summary>The evidence of a run that returns one word and leaves `memory` as it was, with the goals
        /// `run` and `postcondition` under `suffix` left open and the returned word found by the run.</summary>
        internal static void Returns(Writer lean, string indent, string suffix)
        {
            lean.Line($"{indent}refine MethodContract.Holds.intro memory ?output{suffix} ?run{suffix} " +
                "(Confined.refl _ memory)");
            lean.Line($"{indent}  ?postcondition{suffix}");
        }

        /// <summary>The term that closes the goal contract stepping leaves at a return, `Confined ∧ Returns`,
        /// from the proof `confined` of the footprint and the proof of `post`, as parts the writer may wrap
        /// between. The returned values name the output, except that of a method that returns nothing.
        /// </summary>
        internal static IEnumerable<string> Returned(Returning returning, IEnumerable<string> confined) =>
            ["MethodContract.Holds.returns", .. returning.Unit ? ["(output := ())"] : Array.Empty<string>(),
                .. confined, returning.Post];

        /// <summary>The note of the hole a contract whose `post` the author states leaves at each return.
        /// </summary>
        internal static string PostHole(string contract, string where) =>
            $"what `{contract}.post` states of the returned value{where}, from `permitted`, its `pre`";
    }

    /// <summary>How a callee's contract proof closes each return of its body: whether its output is `Unit`, and
    /// the proof of `post`. The `post` of an `Open` contract is a hole of what its author states, after the
    /// memory it has `Kept`.</summary>
    sealed record Returning(string Contract, bool Unit, string Post, bool Open = false, bool Kept = false);

    /// <summary>The static helper at `index` as a stub named `name`, when its parameters and result are 32- or
    /// 64-bit words and its body, without locals, only computes, tests and throws, so every returning side of
    /// its contract proof steps; null for any other callee.</summary>
    static Stub? StubOf(Extraction extraction, int index, string name)
    {
        var method = extraction.Methods[index];
        if (method.HasThis || method.Parameters.Count == 0 || ElementWidth(method.ReturnType) is not { } result ||
            method.Parameters.Any(parameter => ElementWidth(parameter.ParameterType) is null) ||
            !(LoopOutline.Computes(extraction, index) || LoopOutline.Branches(extraction, index)))
            return null;
        var names = new Names();
        return new Stub(index, name, method,
            [.. method.Parameters.Select(parameter => names.Claim(parameter.Name, "argument" + parameter.Index))],
            [.. method.Parameters.Select(parameter => ElementWidth(parameter.ParameterType)!.Value)], result);
    }

    /// <summary>Writes a stub's contract, with `pre` and `post` left to the author, and the proof that the
    /// helper's body meets it, stepped along every returning side.</summary>
    static void StubContract(Writer lean, Extraction extraction, Stub stub, string caller)
    {
        var program = stub.Index.ToString(System.Globalization.CultureInfo.InvariantCulture);
        var single = stub.Inputs.Length == 1;
        var pattern = single ? stub.Inputs[0] : $"({string.Join(", ", stub.Inputs)})";
        var inputType = single ? WordType(stub.Widths[0])
            : $"({string.Join(" × ", stub.Widths.Select(WordType))})";
        var arguments = string.Join(", ", stub.Inputs.Select((input, position) =>
            $".scalar ({ScalarConstructor(stub.Widths[position])} {input})"));
        lean.Quiet();
        lean.Doc($"`{stub.Method.Name}`, method {program} of the extraction, as `{caller}` calls it: replace the " +
            "`sorry` of `pre` with what the caller must guarantee, or `True`, and the `sorry` of `post` with what " +
            "the caller learns of `result`. The helper stores nothing, so `post` keeps the memory.");
        lean.Line($"def {stub.Name}Contract : MethodContract {inputType} {WordType(stub.Result)} where");
        lean.Line($"  args := fun {pattern} => [{arguments}]");
        lean.Line($"  results result := [.scalar ({ScalarConstructor(stub.Result)} result)]");
        lean.Line($"  pre := fun {pattern} memory => sorry");
        lean.Line("  footprint _ := []");
        lean.Line($"  post := fun {pattern} initial final result => final = initial ∧ sorry");
        lean.Line();
        lean.Doc($"`{stub.Method.Name}` meets its contract; the proof of `{caller}` uses only the contract.");
        lean.Line($"theorem {stub.Name}_holds : {stub.Name}Contract.Holds Extracted.program {program} := by");
        LoopOutline.WordCalleeProof(lean, extraction, stub.Index, stub.Name,
            single ? pattern : $"⟨{string.Join(", ", stub.Inputs)}⟩", stub.Inputs, kept: true);
        lean.Line();
        lean.Line($"#print axioms {stub.Name}_holds");
        lean.Line();
    }

    /// <summary>The postcondition of a returning side of a stub's contract proof: the memory is as it was, and
    /// what `post` states of the result is a hole.</summary>
    static void KeptPost(Writer lean, string indent, string name, string suffix, string where)
    {
        lean.Line($"{indent}case postcondition{suffix} =>");
        lean.Line($"{indent}  dsimp only [{name}Contract] at permitted ⊢");
        lean.Line($"{indent}  refine ⟨rfl, ?_⟩");
        lean.Noted(indent + "  ", "sorry", ContractEvidence.PostHole(name + "Contract", where));
    }

    /// <summary>Names the element of a value array argument, reducible so stepping sees the element itself; a
    /// quoted identity wider than a line continues on the next through a string gap, which reads as no text.
    /// </summary>
    static void ElementDefinition(Writer lean, Parameter array)
    {
        lean.Doc($"The element of `{array.Name}`, as the extraction names its type.");
        lean.Line($"@[reducible] def {array.ArrayElement} : CIL.ArrayElement :=");
        var term = array.ElementDefinition!;
        var rest = "  " + (term.StartsWith('(') ? term[1..^1] : term);
        var quoted = false;
        while (rest.Length > Writer.Limit)
        {
            var cut = rest.LastIndexOf(' ', Writer.Limit - 2);
            // A gap continues only a string, so the break must fall inside the quoted identity.
            quoted ^= cut > 0 && rest[..cut].Count(character => character == '"') % 2 == 1;
            if (!quoted)
                throw Unsupported($"the element of `{array.Name}` has a term the outline cannot wrap: {term}");
            lean.Line(rest[..(cut + 1)] + "\\");
            rest = "    " + rest[(cut + 1)..];
        }
        lean.Line(rest);
        lean.Line();
    }

    /// <summary>Why the outline leaves a body to the author: the first argument or operation that
    /// `cil_checked_steps` cannot take without facts or a case split.</summary>
    static string Unstepped(MethodDefinition method, Operation[] ops, IEnumerable<Parameter> parameters)
    {
        if (parameters.FirstOrDefault(parameter => parameter.Shape != ParameterShape.Scalar) is { } argument)
            return $"the body reads `{argument.Name}`, " + argument.Shape switch
            {
                ParameterShape.Boolean => "a `bool` that needs a case split",
                ParameterShape.Narrow => "a narrow integer whose extension needs facts",
                ParameterShape.Reference => "a reference into caller memory",
                ParameterShape.Object => "an object whose fields need facts",
                ParameterShape.StructReference => "a struct of caller memory",
                ParameterShape.StructValue => "a by-value struct whose fields need facts",
                ParameterShape.Array or ParameterShape.ValueArray => "an array whose elements need facts",
                ParameterShape.WordArray => "an array of caller memory",
                _ => "a span of caller memory"
            };
        var pc = Array.FindIndex(ops, op => !Body.Pure(op));
        if (pc < 0) return "the body has locals";
        // A call the outline cannot compose names the contract the author must write and prove.
        return ops[pc] is Call { Kind: CallKind.Static or CallKind.Instance } call
            ? $"`{ops[pc].ToLean()}` at {Location(method, pc)} calls method {call.Method}, which " +
                "`cil_contract_steps` composes through a `MethodContract` you write and prove with " +
                $"`Holds Extracted.program {call.Method}`"
            : $"`{ops[pc].ToLean()}` at {Location(method, pc)} needs facts or a case split";
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
            "`leancil new-proof` from its extraction. Each `sorry` is a hole: `leancil verify --goals` prints " +
            "the goal at each, and `leancil verify` rejects " +
            $"the file until none remains. A hole commented `{NotOutlined.TrimEnd()}` marks a path the " +
            $"outline could not step.{selected}{Renamed(spec)} -/");
        lean.Line();
        lean.Line("open CIL.Safety");
        lean.Line("open CIL (W32 W64)");
        if (spec.Classes) lean.Line("open Extracted.Classes");
        lean.Line("namespace ExampleProof");
        lean.Line();
    }

    /// <summary>The header's note of each parameter bound under another name than its C# one, which the proof
    /// reserves or another binder has.</summary>
    static string Renamed(Specification spec)
    {
        var renamed = spec.Parameters.Where(parameter => parameter.Source is not null)
            .Select(parameter => $"`{parameter.Source}` is bound as `{parameter.Name}`").ToArray();
        return renamed.Length == 0 ? ""
            : $" The C# parameter {string.Join(" and ", renamed)}, " +
                $"{(renamed.Length == 1 ? "a name" : "names")} clear of the proof's own.";
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
    [GeneratedRegex(@"\A(?:(?:stored|framed|held|written|output|called|post|returned|found|branch|initial|memory|" +
        @"encoded|changed|combined|formed|form|loadSigned|arrayApart|localHome|localWritten|localLoaded|" +
        @"frameFacts|below|fuel|invoked|callFormed|permitted)\d*|held\d+Final|" +
        @"(?:owned|kept|added|loaded)\d+(?:Field\d+)?(?:Signed)?)\z")]
    private static partial Regex Generated();

    /// <summary>Lean source with two-space indentation and lines kept under 100 characters.</summary>
    sealed class Writer
    {
        internal const int Limit = 100;
        readonly StringBuilder text = new();

        /// <summary>A line, broken after a comma inside brackets when it is too long; Lean reads a
        /// bracketed term across lines, and the deeper indent keeps it inside its tactic.</summary>
        internal void Line(string line = "")
        {
            // Text already broken into lines, such as a string gap, is measured line by line.
            if (line.Contains('\n'))
            {
                foreach (var part in line.Split('\n')) Line(part);
                return;
            }
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


        /// <summary>Keeps the next definition, whose binders its users fix, from an unused-variable warning for
        /// each binder the author's body leaves out.</summary>
        internal void Quiet() => Line("set_option linter.unusedVariables false in");

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
