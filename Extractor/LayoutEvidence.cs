using System.Text;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Raw metadata is serialized separately from computed sizes/offsets. Lean recomputes
// those values and checks their uses in the emitted method rather than trusting them.
internal sealed class LayoutEvidence(TypeReference[] types, string architecture = "scalar")
{
    readonly TypeReference[] rawTypes = Topological(types);

    static TypeReference[] Topological(TypeReference[] entries)
    {
        var ordered = new List<TypeReference>();
        var seen = new HashSet<string>();
        void Include(TypeReference type)
        {
            if (!seen.Add(type.FullName)) return;
            foreach (var field in MetadataValidation.Fields(type))
                if (MetadataValidation.IsAggregate(field.Type, type.Module)) Include(field.Type);
            ordered.Add(type);
        }
        foreach (TypeReference entry in entries.OrderBy(Identity, StringComparer.Ordinal)) Include(entry);
        return [.. ordered];
    }

    internal static string Scope(TypeReference type) => type.Scope is AssemblyNameReference assembly
        ? assembly.FullName : type.Module.Assembly.Name.FullName;

    internal static string Identity(TypeReference type) => Scope(type) + "::" + type.FullName;

    internal string[] Identities => rawTypes.Select(Identity).ToArray();

    internal int Index(TypeReference type) => Array.FindIndex(rawTypes, entry => entry.FullName == type.FullName);

    internal string RawFieldType(TypeReference type, ModuleDefinition module)
    {
        if (MetadataValidation.IsAggregate(type, module))
        {
            var index = Index(type);
            if (index < 0) throw new InvalidDataException("Missing raw aggregate metadata: " + type.FullName);
            return $".aggregate {index}";
        }
        if (MetadataValidation.VectorWidth(type) is int width) return width == 16 ? ".vector128" : ".vector256";
        return EnumTypes.Storage(type).FullName switch
        {
            "System.SByte" => ".signed8", "System.Byte" => ".unsigned8", "System.Boolean" => ".boolean",
            "System.Int16" => ".signed16", "System.UInt16" => ".unsigned16", "System.Char" => ".character",
            "System.Int32" => ".signed32", "System.UInt32" => ".unsigned32",
            "System.Int64" => ".signed64", "System.UInt64" => ".unsigned64",
            "System.IntPtr" => ".nativeInt", "System.UIntPtr" => ".nativeUInt",
            _ => throw new InvalidDataException("Unsupported raw layout field: " + type.FullName)
        };
    }

    internal void EmitLayouts(StringBuilder lean)
    {
        lean.AppendLine("def rawLayouts : List Extraction.RawLayout := [");
        lean.AppendLine(string.Join(",\n", rawTypes.Select(type =>
        {
            var metadata = ValueTuples.Is(type) ? ((GenericInstanceType)type).ElementType.Resolve() : type.Resolve();
            var fields = MetadataValidation.Fields(type).Select(field =>
                $"{{ type := {RawFieldType(field.Type, type.Module)}, offset := {(field.Definition.Offset < 0 ? "none" : $"some {field.Definition.Offset}")} }}");
            return $"  {{ identity := {JsonSerializer.Serialize(Identity(type))}, explicit := {metadata.IsExplicitLayout.ToString().ToLowerInvariant()}, " +
                (metadata.IsAutoLayout ? "auto := true, " : "") +
                $"packing := {metadata.PackingSize}, declaredSize := {metadata.ClassSize}, fields := [{string.Join(", ", fields)}] }}";
        })));
        lean.AppendLine("]");
        lean.AppendLine("def computedLayouts : Array Extraction.ComputedLayout := #[" +
            string.Join(", ", rawTypes.Select(type => $"⟨layout{Array.FindIndex(types, entry => entry.FullName == type.FullName)}, {MetadataValidation.AggregateLayout(type, type.Module, architecture).Alignment}⟩")) + "]");
        lean.AppendLine($"theorem layouts_validated : Extraction.LayoutsValid rawLayouts computedLayouts .{architecture} := " + LeanEmitter.Decide);
    }

    internal void EmitMethod(StringBuilder lean, MethodDefinition method, int number, HashSet<Instruction> reachable,
        int[] parameterIndices)
    {
        var uses = new List<string>();
        for (int pc = 0; pc < method.Body.Instructions.Count; pc++)
        {
            var instruction = method.Body.Instructions[pc];
            if (!reachable.Contains(instruction)) continue;
            if (instruction.OpCode.Code is Code.Ldfld or Code.Stfld or Code.Ldflda)
            {
                var reference = (FieldReference)instruction.Operand;
                var field = reference.Resolve();
                var owner = ValueTuples.Is(reference.DeclaringType) ? reference.DeclaringType : field.DeclaringType;
                var fieldIndex = Array.FindIndex(MetadataValidation.Fields(owner), candidate => candidate.Definition == field);
                var access = instruction.OpCode.Code switch { Code.Ldfld => "load", Code.Stfld => "store", _ => "address" };
                uses.Add($".field {pc} {Index(owner)} {fieldIndex} .{access}");
            }
            else if (instruction.Operand is TypeReference type && MetadataValidation.IsAggregate(type, method.Module))
            {
                var access = instruction.OpCode.Code switch
                {
                    Code.Ldobj => "load", Code.Stobj => "store", Code.Initobj => "initialize",
                    Code.Cpobj => "copy", Code.Sizeof => "sizeOf", _ => null
                };
                if (access is not null) uses.Add($".size {pc} {Index(type)} .{access}");
            }
            else if (instruction.OpCode.Code == Code.Newobj && instruction.Operand is MethodReference constructor &&
                MetadataValidation.IsAggregate(constructor.DeclaringType, method.Module))
                uses.Add($".size {pc} {Index(constructor.DeclaringType)} .construct");
            else if (instruction.OpCode.Code == Code.Call && instruction.Operand is GenericInstanceMethod generic &&
                generic.DeclaringType.FullName == "System.Runtime.CompilerServices.Unsafe" && generic.GenericArguments.Count == 1 &&
                MetadataValidation.IsAggregate(generic.GenericArguments[0], method.Module) && generic.Name is "SizeOf" or "Add")
                uses.Add($".size {pc} {Index(generic.GenericArguments[0])} .{(generic.Name == "SizeOf" ? "sizeOf" : "referenceAdd")}");
        }
        foreach (var local in method.Body.Variables)
            if (MetadataValidation.IsAggregate(local.VariableType, method.Module))
                uses.Add($".local {local.Index} {Index(local.VariableType)}");
        for (int home = 0; home < parameterIndices.Length; home++)
        {
            var type = MethodArguments.Type(method, parameterIndices[home]);
            if (MetadataValidation.IsAggregate(type, method.Module)) uses.Add($".parameter {home} {Index(type)}");
        }
        lean.AppendLine($"def method{number}LayoutUses : List Extraction.LayoutUse := [{string.Join(", ", uses)}]");
        lean.AppendLine($"theorem method{number}_layouts_validated : Extraction.MethodLayoutsValid rawLayouts computedLayouts method{number} method{number}LayoutUses := {LeanEmitter.Decide}");
    }
}
