using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

/// <summary>The storage and managed targets admitted for raw instruction operands.</summary>
internal static class InstructionOperands
{
    /// <summary>The encoded CIL opcode, including the 0xFE prefix on two-byte opcodes.</summary>
    internal static int RawOpcode(Instruction instruction) => (ushort)instruction.OpCode.Value;

    internal static bool MethodTableLoad(Instruction site, NativeOperands.Certificate native) =>
        native.Incoming.TryGetValue(site, out var stack) && stack.Length >= 2 &&
        stack[^2].Kind == NativeOperands.Kind.MethodTable;

    internal static void ValidateTailStack(Instruction site, NativeOperands.Certificate native)
    {
        if (TailCalls.IsCall(site) && site.Operand is MethodReference target &&
            native.Incoming.TryGetValue(site, out var stack) &&
            stack.Length != target.Parameters.Count + (target.HasThis ? 1 : 0))
            throw new InvalidDataException("Tail call requires exactly its arguments on the evaluation stack");
    }

    internal static int AddressedLocal(MethodDefinition method, Instruction site)
    {
        var local = (VariableDefinition)site.Operand;
        if (ObjectTypes.Rooted(local.VariableType) || ReferenceArrays.Is(local.VariableType))
            throw new InvalidDataException($"Unsupported address of a class instance local: {method.FullName}");
        return local.Index;
    }

    internal static int HomedArgument(MethodDefinition method, Instruction site, IReadOnlyDictionary<int, int> homes)
    {
        var parameter = (ParameterDefinition)site.Operand;
        if (site.OpCode.Code is Code.Ldarga or Code.Ldarga_S)
        {
            var receiver = method.HasThis && parameter == method.Body.ThisParameter;
            if (receiver && ObjectTypes.Candidate(method.DeclaringType))
                throw new InvalidDataException($"Unsupported address of a class instance receiver: {method.FullName}");
            if (ObjectTypes.Rooted(parameter.ParameterType))
                throw new InvalidDataException($"Unsupported address of a class instance argument: {method.FullName}");
        }
        var argument = MethodArguments.Index(method, parameter);
        if (!homes.ContainsKey(argument)) throw new InvalidDataException("Missing parameter storage");
        return argument;
    }

    /// <summary>Whether this integer conversion throws on overflow.</summary>
    internal static bool IsCheckedConversion(Code code) => code is
        Code.Conv_Ovf_I1 or Code.Conv_Ovf_I1_Un or Code.Conv_Ovf_U1 or Code.Conv_Ovf_U1_Un or
        Code.Conv_Ovf_I2 or Code.Conv_Ovf_I2_Un or Code.Conv_Ovf_U2 or Code.Conv_Ovf_U2_Un or
        Code.Conv_Ovf_I4 or Code.Conv_Ovf_I4_Un or Code.Conv_Ovf_U4 or Code.Conv_Ovf_U4_Un or
        Code.Conv_Ovf_I8 or Code.Conv_Ovf_I8_Un or Code.Conv_Ovf_U8 or Code.Conv_Ovf_U8_Un or
        Code.Conv_Ovf_I or Code.Conv_Ovf_I_Un or Code.Conv_Ovf_U or Code.Conv_Ovf_U_Un;

    internal static (int? Bytes, int? ScalarWidth, bool Signed) ObjectStorage(MethodDefinition method,
        Instruction site, TypeReference operand, InstructionIndex instructions,
        MetadataValidation.LayoutContext layouts, FeatureProfile profile)
    {
        RuntimeModels.ValidateTypeIdentity(operand, method.Module, profile.Architecture);
        if (Spans.Is(operand))
        {
            if (site.OpCode.Code == Code.Initobj) SpanReferences.ValidateReset(site, instructions);
            else if (site.OpCode.Code != Code.Ldobj)
                throw new InvalidDataException($"Unsupported store to a span home: {site}");
            else SpanReferences.ValidateCopy(method, site, instructions);
        }
        else if (site.OpCode.Code == Code.Sizeof)
        {
            var size = MetadataValidation.IsAggregate(operand, method.Module) ? layouts.Size(operand) :
                MetadataValidation.IntegerVectorWidth(operand) ?? MetadataValidation.PrimitiveWidth(operand);
            return (size, null, false);
        }
        else if (!MetadataValidation.IsAggregate(operand, method.Module) &&
            MetadataValidation.IntegerVectorWidth(operand) is null)
        {
            var width = MetadataValidation.PrimitiveWidth(operand);
            var signed = EnumTypes.Storage(operand).MetadataType is MetadataType.SByte or MetadataType.Int16;
            return (null, width, signed);
        }
        return (null, null, false);
    }

    internal static (FieldAccess Access, int Offset, int Width, bool Signed) StructField(FieldReference operand,
        FieldDefinition field, FieldAccess access, MethodDefinition method, FeatureProfile profile,
        MetadataValidation.LayoutContext layouts)
    {
        layouts.Size(operand.DeclaringType);
        var type = MetadataValidation.InstanceFieldOf(operand).Type;
        RuntimeModels.ValidateTypeIdentity(type, method.Module, profile.Architecture);
        var aggregate = MetadataValidation.IsAggregate(type, method.Module);
        var width = layouts.FieldSize(type);
        var offset = layouts.FieldOffset(operand.DeclaringType, field);
        if (aggregate && access != FieldAccess.Address)
            return (access == FieldAccess.Load ? FieldAccess.LoadAggregate : FieldAccess.StoreAggregate,
                offset, width, false);
        var signed = access == FieldAccess.Load &&
            EnumTypes.Storage(type).FullName is "System.SByte" or "System.Int16";
        return (access, offset, width, signed);
    }

    internal static (MethodDefinition Method, int Index) DirectTarget(MethodReference reference, bool tail,
        int caller, IReadOnlyDictionary<MethodDefinition, int> methods)
    {
        var method = reference.Resolve() ?? throw new InvalidDataException($"Unresolved method: {reference.FullName}");
        var index = methods.GetValueOrDefault(method, -1);
        if (index > caller || tail && index >= 0) return (method, index);
        var scope = reference.DeclaringType.Scope.Name;
        throw new InvalidDataException($"Unsupported or unresolved call: {reference.FullName} [{scope}]");
    }

    internal static (MethodDefinition Method, int Index) AddressTarget(MethodReference reference,
        IReadOnlyDictionary<MethodDefinition, int> methods)
    {
        var method = reference.Resolve() ?? throw new InvalidDataException("Unresolved managed pointer target");
        var index = methods.GetValueOrDefault(method, -1);
        if (index < 0) throw new InvalidDataException("Managed pointer target is outside the catalog");
        return (method, index);
    }

    internal static (MethodDefinition Method, int Index) ConstrainedTarget(MethodDefinition caller, Instruction site,
        InstructionIndex instructions, FeatureProfile profile, ConstrainedCalls.TargetIndex targets,
        IReadOnlyDictionary<MethodDefinition, int> methods)
    {
        var method = targets.Find(ConstrainedCalls.Resolve(caller, site, instructions, profile.Architecture));
        var index = methods.GetValueOrDefault(method, -1);
        if (index <= methods[caller]) throw new InvalidDataException("Unresolved constrained implementation");
        return (method, index);
    }

    internal static void ValidateVirtualTarget(VirtualDispatch.Entry entry,
        IReadOnlyDictionary<MethodDefinition, int> methods, int caller)
    {
        var index = methods.GetValueOrDefault(entry.Body, -1);
        if (index <= caller)
            throw new InvalidDataException($"Unresolved virtual implementation: {entry.Body.FullName}");
    }

    internal static void ValidateLiteral(string text)
    {
        if (text.Any(character => char.IsSurrogate(character) || character is '\b' or '\f'))
            throw new InvalidDataException("Unsupported string literal: a surrogate, backspace or form feed");
    }
}
