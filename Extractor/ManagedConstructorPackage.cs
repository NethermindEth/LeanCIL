using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

/// <summary>
/// The literal-message exception constructions bound to their CoreLib constructors, and the Lean that binds them: a
/// single-method package for a caller whose only call is the construction, and otherwise rebound callers with the
/// CoreLib rows appended after the local methods.
/// </summary>
internal static class ManagedConstructorPackage
{
    /// <summary>The parameter lists of the bound overloads, by the Lean <c>TypeExpr</c> each parameter has.</summary>
    internal enum Shape { Message, MessageMessage, MessageActualMessage, MessageMessageInner, MessageInner }

    /// <summary>
    /// A bound overload, named by exception owner and parameter list as <c>ConstructorImage.of?</c> takes it.
    /// </summary>
    internal readonly record struct Overload(ExceptionType Raised, Shape Shape)
    {
        /// <summary>The Lean selector of this overload.</summary>
        internal string Lean => $"(.{Raised.LeanName()}, [{string.Join(", ", Parameters)}])";

        string[] Parameters => Shape switch
        {
            Shape.Message => [Message],
            Shape.MessageMessage => [Message, Message],
            Shape.MessageActualMessage => [Message, "Extraction.actualParameter", Message],
            Shape.MessageMessageInner => [Message, Message, Inner],
            Shape.MessageInner => [Message, Inner],
            _ => throw new ArgumentOutOfRangeException(nameof(Shape))
        };

        const string Message = "Extraction.messageParameter";
        const string Inner = "Extraction.innerParameter";

        /// <summary>The CoreLib definitions <c>ConstructorImage.of?</c> places for this overload alone.</summary>
        internal int Definitions => Raised == ExceptionType.ArgumentOutOfRange ? 7 : 6;
    }

    /// <summary>A caller's construction links and the binding its evidence states.</summary>
    internal sealed record BoundCaller(IReadOnlyList<(int Pc, string Link)> Links, GenericEvidence.Binding Evidence);

    /// <summary>
    /// The links of <paramref name="method"/>'s bound constructions to the image's head definition, the first slot
    /// after the <paramref name="locals"/> local methods.
    /// </summary>
    internal static BoundCaller Binding(MethodDefinition method, IReadOnlySet<Instruction> sites, int locals)
    {
        var code = method.Body.Instructions;
        var pcs = Enumerable.Range(0, code.Count).Where(pc => sites.Contains(code[pc])).ToArray();
        var links = pcs.Select(pc =>
        {
            var constructor = ((MethodReference)code[pc].Operand).Resolve() ??
                throw new InvalidDataException($"Unresolved bound constructor: {code[pc].Operand}");
            var (bases, size) = Allocation(constructor.DeclaringType);
            return (pc, $".object {locals} {LeanText.ClassList(bases)} {size}");
        }).ToArray();
        return new(links, new(locals, pcs));
    }

    /// <summary>
    /// The CoreLib bases of a bound exception class, nearest first and without System.Object, and its size at one
    /// slot per instance field. Its bound constructor rows, not the extractor's class admission, run its
    /// initialisation.
    /// </summary>
    static (string[] Bases, int Size) Allocation(TypeDefinition type)
    {
        List<TypeDefinition> chain = [];
        for (var current = type; current is not null && current.BaseType is not null;
             current = current.BaseType.Resolve())
            chain.Add(current);
        var fields = chain.Sum(owner => owner.Fields.Count(field => !field.IsStatic));
        return ([.. chain.Skip(1).Select(GenericEvidence.ObjectType)], ObjectTypes.FieldSlot * fields);
    }

    /// <summary>The image of a package's overload, with the kernel budget its binding and rows need.</summary>
    internal static void EmitImage(StringBuilder lean, Package package) =>
        lean.AppendLine($$"""
            set_option maxRecDepth 65536
            set_option maxHeartbeats 30000000
            /-- The CoreLib definitions, getter declarations and dependency slices of the bound constructions. -/
            def constructorImage : Runtime.Net11WinX64.ConstructorImage :=
              (Runtime.Net11WinX64.ConstructorImage.of? [{{package.Overload.Lean}}]).get (by cil_kernel_rfl)
            """);

    /// <summary>The image's rows after the local methods, checked with the pins of the first bound caller.</summary>
    internal static void EmitRows(StringBuilder lean, string locals, int caller) =>
        lean.AppendLine($$"""
            /-- The local methods in program order, the first slots of the call table. -/
            def localMethods : List Extraction.SpecializedMethod := [{{locals}}]
            /-- The image's CoreLib definitions after the local methods, and its getter declarations. -/
            def runtimeRows : List (Extraction.MethodEvidence × Method) × List Extraction.MethodEvidence :=
              (constructorImage.rows? localMethods method{{caller}}Body profile environment).get (by cil_kernel_rfl)
            def managedDeclarations : List Extraction.MethodEvidence := runtimeRows.2
            """);

    /// <summary>
    /// The appended CoreLib methods as literals with their instruction equations, the rows they equal and the check
    /// of those rows against the callable table.
    /// </summary>
    internal static void EmitRuntimeMethods(StringBuilder lean, int locals, int count)
    {
        var names = Enumerable.Range(locals, count).Select(n => $"method{n}").ToArray();
        for (var index = 0; index < count; index++)
        {
            var decoder = $"constructorImage.rowMethod? localMethods profile environment {index}";
            lean.AppendLine($"""
                cil_decoded_method {names[index]} := {decoder}
                cil_instruction_equations {names[index]}
                cil_resolution_facts {names[index]}
                """);
        }
        lean.AppendLine($$"""
            theorem runtime_methods : runtimeRows.1.map Prod.snd = [{{string.Join(", ", names)}}] := by cil_kernel_rfl
            theorem runtime_validated : runtimeRows.1.all (Extraction.ManagedPackage.rowValid environment assemblies
                platformDefinitions callableMethods) = true := by cil_kernel_rfl
            """);
    }

    /// <summary>The literal-message sites a package binds, by method, all of one overload.</summary>
    internal sealed class Package(Overload overload,
        IReadOnlyDictionary<MethodDefinition, IReadOnlySet<Instruction>> sites)
    {
        internal Overload Overload { get; } = overload;

        /// <summary>The bound sites of <paramref name="method"/>, or null for a method without one.</summary>
        internal IReadOnlySet<Instruction>? Of(MethodDefinition method) => sites.GetValueOrDefault(method);
    }

    /// <summary>The construction of a single-method extraction with no imports, or null.</summary>
    internal static Instruction? Site(MethodDefinition[] methods, FeatureProfile profile, int imports) =>
        methods.Length == 1 && imports == 0 ? Site(methods[0], profile) : null;

    /// <summary>The construction of a single-method package: the bound site that is the method's only call.</summary>
    internal static Instruction? Site(MethodDefinition entry, FeatureProfile profile)
    {
        if (!entry.HasBody) return null;
        var calls = entry.Body.Instructions.Where(site => site.OpCode.FlowControl == FlowControl.Call)
            .Take(2).ToArray();
        return calls is [var site] && Sites(entry, profile).Contains(site) ? site : null;
    }

    /// <summary>
    /// The sites bound across a multi-method extraction, or null when it binds none. Every bound caller carries the
    /// dependency slices of one overload, so sites of a second overload keep their fold, as do all sites of a method
    /// whose metadata also names a type of a second overload.
    /// </summary>
    internal static Package? Bind(MethodDefinition[] methods, FeatureProfile profile, int imports)
    {
        if (imports != 0 || Site(methods, profile, imports) is not null) return null;
        var first = methods.Select(method => (Method: method, Sites: Sites(method, profile)))
            .Where(entry => entry.Sites.Count != 0)
            .Select(entry => entry.Method.Body.Instructions.First(entry.Sites.Contains)).FirstOrDefault();
        if (first is null) return null;
        var overload = OverloadOf((MethodReference)first.Operand)!.Value;
        // Rechecked for the selected overload alone, whose slices define no other overload's types.
        var sites = methods.Select(method => (Method: method, Sites: Sites(method, profile, overload)))
            .Where(entry => entry.Sites.Count != 0).ToDictionary(entry => entry.Method, entry => entry.Sites);
        return sites.Count == 0 ? null : new(overload, sites);
    }

    /// <summary>The bound constructions of each method of an extraction, single-method or packaged.</summary>
    internal static Func<MethodDefinition, IReadOnlySet<Instruction>?> Bound(MethodDefinition[] methods,
        FeatureProfile profile, int imports)
    {
        if (Site(methods, profile, imports) is { } site) return _ => new HashSet<Instruction> { site };
        var package = Bind(methods, profile, imports);
        return method => package?.Of(method);
    }

    /// <summary>
    /// The live constructions of <paramref name="only"/>, or of any bound overload, in <paramref name="method"/> whose
    /// literal loads run on every entry, when every System.Runtime type the method's metadata names is the owner or a
    /// parameter type of one of those constructions.
    /// </summary>
    internal static IReadOnlySet<Instruction> Sites(MethodDefinition method, FeatureProfile profile,
        Overload? only = null)
    {
        if (!method.HasBody || method.HasGenericParameters || method.DeclaringType.HasGenericParameters ||
            profile.Architecture == "arm64" || profile.NativeWidth != 64 || !profile.LittleEndian) return Empty;
        HashSet<Instruction> sites = [];
        foreach (var site in method.Body.Instructions)
            if (site is { OpCode.Code: Code.Newobj, Operand: MethodReference constructor } &&
                OverloadOf(constructor) is { } overload && (only is null || overload == only) &&
                LoadsOnEveryEntry(method.Body, site, Loads(overload)))
                sites.Add(site);
        return sites.Count != 0 && RuntimeTypesCovered(method, sites) ? sites : Empty;
    }

    static readonly IReadOnlySet<Instruction> Empty = new HashSet<Instruction>();

    static Overload? OverloadOf(MethodReference ctor)
    {
        if (ctor.Name != ".ctor" || !ctor.HasThis || ctor is GenericInstanceMethod ||
            ctor.Parameters.Any(parameter => LayoutEvidence.Scope(parameter.ParameterType) != TypeTests.RuntimeScope))
            return null;
        var parameters = ctor.Parameters.Select(parameter => parameter.ParameterType.MetadataType).ToArray();
        var innerException = ctor.Parameters is [.., { ParameterType.FullName: "System.Exception" }];
        Shape? shape = (Throws.Owner(ctor.DeclaringType), parameters) switch
        {
            (ExceptionType.ArgumentOutOfRange, [MetadataType.String, MetadataType.String]) => Shape.MessageMessage,
            (ExceptionType.ArgumentOutOfRange, [MetadataType.String, MetadataType.Object, MetadataType.String]) =>
                Shape.MessageActualMessage,
            (ExceptionType.Argument, [MetadataType.String, MetadataType.String]) => Shape.MessageMessage,
            (ExceptionType.Argument, [MetadataType.String, MetadataType.String, MetadataType.Class])
                when innerException => Shape.MessageMessageInner,
            (ExceptionType.InvalidOperation, [MetadataType.String]) => Shape.Message,
            (ExceptionType.InvalidOperation, [MetadataType.String, MetadataType.Class])
                when innerException => Shape.MessageInner,
            _ => null
        };
        return shape is { } bound ? new(Throws.Owner(ctor.DeclaringType)!.Value, bound) : null;
    }

    // The loads directly before newobj that make the message a literal, so no resource getter runs.
    static Code[] Loads(Overload overload) => overload switch
    {
        { Raised: ExceptionType.Argument } => [],
        { Shape: Shape.MessageInner } => [Code.Ldstr, Code.Ldnull],
        _ => [Code.Ldstr]
    };

    /// <summary>
    /// Whether each System.Runtime type a reference of <paramref name="method"/> names is System.Object, a bound
    /// constructor's owner or one of its parameter classes: a bound caller resolves every such reference through the
    /// carried facade, and the dependency slices define only those.
    /// </summary>
    static bool RuntimeTypesCovered(MethodDefinition method, IReadOnlySet<Instruction> sites)
    {
        var constructors = sites.Select(site => (MethodReference)site.Operand).ToArray();
        HashSet<TypeDefinition?> covered = [method.Module.TypeSystem.Object.Resolve()];
        foreach (var constructor in constructors)
        {
            covered.Add(constructor.DeclaringType.Resolve());
            foreach (var parameter in constructor.Parameters) covered.Add(parameter.ParameterType.Resolve());
        }
        return MetadataReferences(method).All(type => covered.Contains(type.Resolve()));
    }

    /// <summary>
    /// The System.Runtime type references a method's metadata rows may name, as named class references.
    /// </summary>
    static IEnumerable<TypeReference> MetadataReferences(MethodDefinition method)
    {
        List<TypeReference> types = [method.ReturnType,
            .. method.Parameters.Select(parameter => parameter.ParameterType),
            .. method.Body.Variables.Select(variable => variable.VariableType)];
        for (var owner = method.DeclaringType; owner is not null; owner = owner.DeclaringType)
            if (owner.BaseType is { } baseType) types.Add(baseType);
        for (var owner = method.DeclaringType.BaseType?.Resolve(); owner?.Module == method.Module;
             owner = owner.BaseType?.Resolve())
            if (owner.BaseType is { } baseType) types.Add(baseType);
        foreach (var instruction in method.Body.Instructions)
            switch (instruction.Operand)
            {
                case MethodReference reference:
                    types.Add(reference.DeclaringType);
                    types.Add(reference.ReturnType);
                    types.AddRange(reference.Parameters.Select(parameter => parameter.ParameterType));
                    break;
                case FieldReference reference:
                    types.Add(reference.DeclaringType);
                    types.Add(reference.FieldType);
                    break;
                case TypeReference reference:
                    types.Add(reference);
                    break;
            }
        return types.SelectMany(Named).Where(type => type is not TypeDefinition &&
            type.MetadataType is MetadataType.Class or MetadataType.ValueType &&
            LayoutEvidence.Scope(type) == TypeTests.RuntimeScope);
    }

    static IEnumerable<TypeReference> Named(TypeReference type) => type switch
    {
        GenericInstanceType generic => Named(generic.ElementType).Concat(generic.GenericArguments.SelectMany(Named)),
        TypeSpecification specification => Named(specification.ElementType),
        GenericParameter => [],
        _ => [type]
    };
    /// <summary>
    /// The instructions before <paramref name="site"/> are <paramref name="loads"/> in order, and no branch
    /// enters after the first load, so every path to the allocation runs them all.
    /// </summary>
    static bool LoadsOnEveryEntry(MethodBody body, Instruction site, Code[] loads)
    {
        var entered = body.Instructions.SelectMany(instruction => instruction.Operand switch
        {
            Instruction target => [target],
            Instruction[] targets => targets,
            _ => Array.Empty<Instruction>()
        }).ToHashSet();
        var current = site;
        for (var index = loads.Length - 1; index >= 0; index--)
        {
            if (entered.Contains(current)) return false;
            current = current.Previous;
            if (current?.OpCode.Code != loads[index]) return false;
        }
        return !entered.Contains(site);
    }

    internal static void EmitSource(StringBuilder lean, int assembly) =>
        lean.AppendLine($$"""
            /-- The physical source fields for binding a managed constructor entry. -/
            def constructorSource : Runtime.Net11WinX64.ConstructorSource := {
              original := method0Original, body := method0Body, arguments := method0TypeArgumentsRaw,
              reachable := method0Reachable, featureStates := method0FeatureStates,
              layoutUses := method0LayoutUses, dispatchTypes := method0DispatchTypes,
              assembly := assembly{{assembly}}, signature := method0Signature }
            /-- The executable definitions and managed declarations derived from this caller. -/
            def managedPackage : Option Extraction.ManagedPackage :=
              Runtime.Net11WinX64.constructorPackage? constructorSource imports profile environment
            """);

    internal static void Emit(StringBuilder lean, int assembly)
    {
        EmitSource(lean, assembly);
        lean.AppendLine("""
            set_option maxRecDepth 65536
            set_option maxHeartbeats 30000000
            /-- Binding must succeed to publish this extraction. -/
            def boundPackage := managedPackage.get (by cil_kernel_rfl)
            def assemblies := Runtime.Net11WinX64.packagePins sourceAssemblies
            def methodEvidence := boundPackage.rows.map Prod.fst
            def managedDeclarations := boundPackage.declarations
            def specializedMethods := Extraction.specializationTable
              (Extraction.callableEvidence methodEvidence managedDeclarations)
            def program : Program := boundPackage.methods
            @[cil_code] def method0 : Method := boundPackage.root.2
            def signatures : List String := methodEvidence.map Extraction.MethodEvidence.signature
            theorem signatures_length : signatures.length = program.length := by cil_kernel_rfl
            def importSignatures : List String := []
            theorem importSignatures_length : importSignatures.length = imports.length := rfl
            theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts
                assemblies platformDefinitions methodEvidence imports program managedDeclarations :=
              Extraction.ManagedPackage.translationValid (package := boundPackage) (environment := environment)
                (pins := assemblies) (platform := platformDefinitions) (by cil_kernel_rfl)
            #print axioms translation_valid
            """);
    }
}
