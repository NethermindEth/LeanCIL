using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class OutlineInstructions
{
    internal static void Validate(Instruction i, MethodDefinition m,
        IReadOnlyDictionary<MethodDefinition, int> methods, InstructionIndex instructions,
        ResolvedCallSites callSites, FeatureProfile? profile = null, NativeOperands.Certificate? nativeOperands = null,
        IReadOnlyDictionary<int, int>? parameterHomes = null, ImportResolution? imports = null,
        MetadataValidation.LayoutContext? layouts = null)
    {
        InstructionPrefixes.ValidatePrefix(m, i);
        if (i.Previous is { } previous) InstructionPrefixes.ValidatePrefix(m, previous);
        if (imports?.Slot(i) is not null) return;
        profile ??= FeatureProfile.Scalar;
        layouts ??= new(m.Module, profile.Architecture);
        layouts.Require(m.Module, profile.Architecture);
        var reachable = nativeOperands is null || parameterHomes is null ? Reachability.Analyze(m, profile) : null;
        nativeOperands ??= NativeOperands.Certify(m, reachable!, profile);
        if (i.OpCode.Code is Code.Calli or Code.Ldftn) return;
        // Handler tables carry method pointers and cannot supply numeric array outline steps.
        if (i.OpCode.Code == Code.Ldelem_Any && InstructionOperands.MethodTableLoad(i, nativeOperands))
            return;
        InstructionOperands.ValidateTailStack(i, nativeOperands);
        if (ReferenceArrays.SupportsInstruction(i))
            return;
        if (Arrays.SupportsInstruction(i, profile.Architecture))
            return;
        parameterHomes ??= ParameterStorage.IndexHomes(ParameterStorage.Analyze(m, reachable!), m.Body.Variables.Count);
        ValidateCore(i, m, methods, instructions, profile, parameterHomes,
            layouts, callSites);
    }

    internal static bool IsStackCode(Code code) => InstructionOperands.IsCheckedConversion(code) ||
        code is Code.Add or Code.Sub or Code.Mul or Code.And or Code.Or or Code.Xor or Code.Not or Code.Neg or
            Code.Shl or Code.Shr or Code.Shr_Un or Code.Ceq or Code.Clt or Code.Clt_Un or Code.Cgt or Code.Cgt_Un or
            Code.Conv_I1 or Code.Conv_I2 or Code.Conv_I4 or Code.Conv_I8 or Code.Conv_I or
            Code.Conv_U1 or Code.Conv_U2 or Code.Conv_U4 or Code.Conv_U8 or Code.Conv_U or
            Code.Add_Ovf or Code.Add_Ovf_Un or Code.Sub_Ovf or Code.Sub_Ovf_Un or Code.Mul_Ovf or Code.Mul_Ovf_Un or
            Code.Div or Code.Div_Un or Code.Rem or Code.Rem_Un or Code.Dup or Code.Pop or Code.Ldnull or
            Code.Ldind_I1 or Code.Ldind_U1 or Code.Ldind_I2 or Code.Ldind_U2 or Code.Ldind_I4 or Code.Ldind_U4 or
            Code.Ldind_I8 or Code.Ldind_I or Code.Stind_I1 or Code.Stind_I2 or Code.Stind_I4 or Code.Stind_I8 or
            Code.Stind_I or Code.Ret;

    static void ValidateCore(Instruction i, MethodDefinition m,
        IReadOnlyDictionary<MethodDefinition, int> methods, InstructionIndex instructions,
        FeatureProfile profile, IReadOnlyDictionary<int, int> parameterHomes, MetadataValidation.LayoutContext layouts,
        ResolvedCallSites callSites)
    {
        var typeTests = TypeTests.Analyze(m);
        if (i.OpCode.Code is Code.Cpblk or Code.Initblk)
        {
            MemoryPrefixes.BlockAlignment(i);
            return;
        }
        if (i.OpCode.Code == Code.Tail)
        {
            TailCalls.ValidateReachable(m, i, profile.Architecture);
            return;
        }
        if (typeTests.Operands.Contains(i) || i.OpCode.Code == Code.Call && typeTests.Results.ContainsKey(i))
            return;
        var throws = Throws.Analyze(m);
        if (i.OpCode.Code == Code.Constrained) return;
        var receiverCall = ObjectTypes.ReceiverCall(i);
        if (!receiverCall &&
            (i.OpCode.Code == Code.Callvirt || i is { OpCode.Code: Code.Call, Previous.OpCode.Code: Code.Constrained }))
        {
            callSites.Target(i, methods);
            return;
        }
        if (throws.Raises.ContainsKey(i)) return;
        if (i.OpCode.Code != Code.Ldnull && throws.Operands.Contains(i)) return;
        if (i.Operand is Instruction &&
            i.OpCode.OperandType is OperandType.InlineBrTarget or OperandType.ShortInlineBrTarget &&
            i.OpCode.Code is not (Code.Leave or Code.Leave_S))
            return;
        if (InstructionOperands.AddressSlot(m, i, parameterHomes).HasValue) return;
        if (InstructionOperands.StoreSlot(m, i, parameterHomes).HasValue) return;
        if (i.OpCode.Code is Code.Ldobj or Code.Stobj or Code.Initobj or Code.Sizeof or Code.Cpobj &&
            i.Operand is TypeReference operand)
        {
            InstructionOperands.ObjectStorage(m, i, operand, instructions, layouts, profile);
            return;
        }
        if (callSites.VirtualTargets(i) is not null) return;
        if (i.OpCode.Code is Code.Call or Code.Newobj || receiverCall)
        {
            var r = (MethodReference)i.Operand;
            if (i.OpCode.Code == Code.Call && RuntimeModels.CallModel(r, profile))
                return;
            if (i.OpCode.Code == Code.Newobj && Spans.ConstructorOperation(r, profile.Architecture))
                return;
            if (i.OpCode.Code == Code.Newobj) return;
            callSites.Target(i, methods);
            return;
        }
        if (i.OpCode.Code is Code.Castclass or Code.Isinst)
        {
            ObjectTypes.ValidateTestOperand(i);
            return;
        }
        if (i.OpCode.Code == Code.Ldstr)
        {
            InstructionOperands.ValidateLiteral((string)i.Operand);
            return;
        }
        var code = i.OpCode.Code;
        if (IsStackCode(code) || code is Code.Nop or Code.Readonly or Code.Unaligned or
            Code.Localloc or Code.Switch or Code.Ldloc_0 or Code.Ldloc_1 or Code.Ldloc_2 or
            Code.Ldloc_3 or Code.Ldloc or Code.Ldloc_S or Code.Ldfld or Code.Ldflda or Code.Stfld or
            >= Code.Ldc_I4_M1 and <= Code.Ldc_I8 || MethodArguments.LoadIndex(m, i).HasValue) return;
        if (code is Code.Ldsfld or Code.Ldsflda or Code.Ldtoken && i.Operand is FieldReference) return;
        if (code == Code.Stsfld)
            throw new InvalidDataException($"Unsupported static field store: {i}\n  Static fields are written only by their static constructor, which is never extracted.");
        throw new InvalidDataException($"Unsupported instruction: {i}");
    }
}
