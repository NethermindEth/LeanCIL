using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

/// <summary>The physical inputs and certified method table of a bound range-constructor entry.</summary>
internal static class ManagedConstructorPackage
{
    internal static Instruction? Site(MethodDefinition[] methods, FeatureProfile profile, int imports) =>
        methods.Length == 1 && imports == 0 ? Site(methods[0], profile) : null;

    internal static Instruction? Site(MethodDefinition entry, FeatureProfile profile)
    {
        if (!entry.HasBody || entry.HasGenericParameters || entry.DeclaringType.HasGenericParameters ||
            profile.Architecture == "arm64" || profile.NativeWidth != 64 || !profile.LittleEndian) return null;
        var calls = entry.Body.Instructions.Where(site => site.OpCode.FlowControl == FlowControl.Call).Take(2).ToArray();
        if (calls is not [{ OpCode.Code: Code.Newobj,
                Operand: MethodReference ctor } site]) return null;
        if (ctor.Name != ".ctor" || !ctor.HasThis || ctor is GenericInstanceMethod ||
            ctor.Parameters.Any(parameter => LayoutEvidence.Scope(parameter.ParameterType) != TypeTests.RuntimeScope))
            return null;
        var parameters = ctor.Parameters.Select(parameter => parameter.ParameterType.MetadataType).ToArray();
        return (Throws.Owner(ctor.DeclaringType), parameters) switch
        {
            (ExceptionType.ArgumentOutOfRange, [MetadataType.String, MetadataType.String] or
                [MetadataType.String, MetadataType.Object, MetadataType.String])
                when site.Previous?.OpCode.Code == Code.Ldstr => site,
            (ExceptionType.Argument, [MetadataType.String, MetadataType.String, MetadataType.Class])
                when ctor.Parameters[2].ParameterType.FullName == "System.Exception" => site,
            _ => null
        };
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
