using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class InstructionTranslation
{
    internal static Operation Translate(Instruction i, MethodDefinition m,
        IReadOnlyDictionary<MethodDefinition, int> methods, InstructionIndex instructions,
        ResolvedCallSites callSites, FeatureProfile? profile = null, NativeOperands.Certificate? nativeOperands = null,
        IReadOnlyDictionary<int, int>? parameterHomes = null, ImportResolution? imports = null,
        MetadataValidation.LayoutContext? layouts = null)
    {
        InstructionPrefixes.ValidatePrefix(m, i);
        if (i.Previous is { } previous) InstructionPrefixes.ValidatePrefix(m, previous);
        if (imports is not null && imports.TryTranslate(i, methods.Count, out Operation? imported)) return imported;
        profile ??= FeatureProfile.Scalar;
        layouts ??= new(m.Module, profile.Architecture);
        layouts.Require(m.Module, profile.Architecture);
        var reachable = nativeOperands is null || parameterHomes is null ? Reachability.Analyze(m, profile) : null;
        nativeOperands ??= NativeOperands.Certify(m, reachable!, profile);
        if (i.OpCode.Code is Code.Calli or Code.Ldftn) return Unoutlined.Site;
        // Handler tables carry method pointers and cannot supply numeric array outline steps.
        if (i.OpCode.Code == Code.Ldelem_Any && InstructionOperands.MethodTableLoad(i, nativeOperands))
            return Unoutlined.Site;
        InstructionOperands.ValidateTailStack(i, nativeOperands);
        if (ReferenceArrays.Translate(i) is { } referenceOperation) return referenceOperation;
        if (Arrays.Translate(i, profile.Architecture) is { } arrayOperation) return arrayOperation;
        parameterHomes ??= ParameterStorage.IndexHomes(ParameterStorage.Analyze(m, reachable!), m.Body.Variables.Count);
        return TranslateCore(i, m, methods, instructions, profile, parameterHomes,
            layouts, callSites);
    }

    static Operation TranslateCore(Instruction i, MethodDefinition m,
        IReadOnlyDictionary<MethodDefinition, int> methods, InstructionIndex instructions,
        FeatureProfile profile, IReadOnlyDictionary<int, int> parameterHomes, MetadataValidation.LayoutContext layouts,
        ResolvedCallSites callSites)
    {
        var typeTests = TypeTests.Analyze(m);
        if (i.OpCode.Code is Code.Cpblk or Code.Initblk)
        {
            MemoryPrefixes.BlockAlignment(i);
            return Unoutlined.Site;
        }
        if (i.OpCode.Code == Code.Tail)
        {
            TailCalls.ValidateReachable(m, i, profile.Architecture);
            return StackOperation.Nop;
        }
        if (typeTests.Operands.Contains(i) || i.OpCode.Code == Code.Call && typeTests.Results.ContainsKey(i))
            return Unoutlined.Site;
        var throws = Throws.Analyze(m);
        if (i.OpCode.Code == Code.Constrained) return StackOperation.Nop;
        var receiverCall = ObjectTypes.ReceiverCall(i);
        if (!receiverCall &&
            (i.OpCode.Code == Code.Callvirt || i is { OpCode.Code: Code.Call, Previous.OpCode.Code: Code.Constrained }))
        {
            var (resolved, index) = callSites.Target(i, methods);
            return new Call(CallKind.Static, index, resolved.Parameters.Count + (resolved.HasThis ? 1 : 0));
        }
        if (throws.Raises.ContainsKey(i)) return new StackOperation(i.OpCode.Code);
        if (i.OpCode.Code != Code.Ldnull && throws.Operands.Contains(i)) return StackOperation.Nop;
        if (i.Operand is Instruction destination &&
            i.OpCode.OperandType is OperandType.InlineBrTarget or OperandType.ShortInlineBrTarget &&
            i.OpCode.Code is not (Code.Leave or Code.Leave_S))
            return new Jump(i.OpCode.Value, instructions.Position(destination));
        if (InstructionOperands.AddressSlot(m, i, parameterHomes).HasValue) return Unoutlined.Site;
        if (InstructionOperands.StoreSlot(m, i, parameterHomes).HasValue) return Unoutlined.Site;
        if (i.OpCode.Code is Code.Ldobj or Code.Stobj or Code.Initobj or Code.Sizeof or Code.Cpobj &&
            i.Operand is TypeReference operand)
        {
            var shape = InstructionOperands.ObjectStorage(m, i, operand, instructions, layouts, profile);
            return new ObjectInstruction(i.OpCode.Code, ScalarWidth: shape.ScalarWidth,
                Signed: shape.Signed, ByteSize: shape.Bytes);
        }
        if (callSites.VirtualTargets(i) is not null) return Unoutlined.Site;
        if (i.OpCode.Code is Code.Call or Code.Newobj || receiverCall)
        {
            var r = (MethodReference)i.Operand;
            if (i.OpCode.Code == Code.Call && RuntimeModels.CallModel(r, profile) is { } model)
                return model;
            if (i.OpCode.Code == Code.Newobj && Spans.ConstructorOperation(r, profile.Architecture) is { } source)
                return source;
            if (i.OpCode.Code == Code.Newobj) return Unoutlined.Site;
            var (resolved, index) = callSites.Target(i, methods);
            var kind = TailCalls.IsCall(i) ? CallKind.Tail : receiverCall ? CallKind.Instance : CallKind.Static;
            return new Call(kind, index, resolved.Parameters.Count + (resolved.HasThis ? 1 : 0));
        }
        if (i.OpCode.Code is Code.Castclass or Code.Isinst)
        {
            ObjectTypes.ValidateTestOperand(i);
            return Unoutlined.Site;
        }
        if (InstructionOperands.IsCheckedConversion(i.OpCode.Code)) return new StackOperation(i.OpCode.Code);
        if (i.OpCode.Code == Code.Ldstr)
        {
            InstructionOperands.ValidateLiteral((string)i.Operand);
            return Unoutlined.Site;
        }
        return i.OpCode.Code switch
        {
            Code.Add or Code.Sub or Code.Mul or Code.And or Code.Or or Code.Xor or Code.Not or Code.Neg or
            Code.Shl or Code.Shr or Code.Shr_Un or Code.Ceq or Code.Clt or Code.Clt_Un or Code.Cgt or Code.Cgt_Un or
            Code.Conv_I1 or Code.Conv_I2 or Code.Conv_I4 or Code.Conv_I8 or Code.Conv_I or
            Code.Conv_U1 or Code.Conv_U2 or Code.Conv_U4 or Code.Conv_U8 or Code.Conv_U or
            Code.Add_Ovf or Code.Add_Ovf_Un or Code.Sub_Ovf or Code.Sub_Ovf_Un or Code.Mul_Ovf or Code.Mul_Ovf_Un or
            Code.Div or Code.Div_Un or Code.Rem or Code.Rem_Un or Code.Dup or Code.Pop or Code.Ldnull or
            Code.Ldind_I1 or Code.Ldind_U1 or Code.Ldind_I2 or Code.Ldind_U2 or Code.Ldind_I4 or Code.Ldind_U4 or
            Code.Ldind_I8 or Code.Ldind_I or Code.Stind_I1 or Code.Stind_I2 or Code.Stind_I4 or Code.Stind_I8 or
            Code.Stind_I or Code.Ret =>
                new StackOperation(i.OpCode.Code),
            Code.Nop or Code.Readonly => StackOperation.Nop,
            // Ordinary accesses already use the documented byte-aligned runtime model.
            // For block instructions the validated prefix selects the required alignment.
            Code.Unaligned => StackOperation.Nop,
            Code.Localloc or Code.Switch => Unoutlined.Site,
            Code.Ldsfld when FeatureProfile.PlatformField((FieldReference)i.Operand) is int constant =>
                new Constant(32, constant, true),
            Code.Ldsfld or Code.Ldsflda or Code.Ldtoken when i.Operand is FieldReference =>
                Unoutlined.Site,
            Code.Stsfld => throw new InvalidDataException($"Unsupported static field store: {i}\n  Static fields are written only by their static constructor, which is never extracted."),
            _ when MethodArguments.LoadIndex(m, i) is int index =>
                parameterHomes.ContainsKey(index) ? Unoutlined.Site : new Arg(index),
            Code.Ldloc_0 or Code.Ldloc_1 or Code.Ldloc_2 or Code.Ldloc_3 or Code.Ldloc or Code.Ldloc_S =>
                Unoutlined.Site,
            Code.Ldfld or Code.Ldflda or Code.Stfld => Unoutlined.Site,
            Code.Ldc_I4_M1 => new Constant(32, -1, false),
            Code.Ldc_I4_0 => new Constant(32, 0, true),
            Code.Ldc_I4_1 => new Constant(32, 1, true),
            Code.Ldc_I4_2 => new Constant(32, 2, true),
            Code.Ldc_I4_3 => new Constant(32, 3, true),
            Code.Ldc_I4_4 => new Constant(32, 4, true),
            Code.Ldc_I4_5 => new Constant(32, 5, true),
            Code.Ldc_I4_6 => new Constant(32, 6, true),
            Code.Ldc_I4_7 => new Constant(32, 7, true),
            Code.Ldc_I4_8 => new Constant(32, 8, true),
            Code.Ldc_I4 or Code.Ldc_I4_S => new Constant(32, Convert.ToInt64(i.Operand), false),
            Code.Ldc_I8 => new Constant(64, (long)i.Operand, false),
            _ => throw new InvalidDataException($"Unsupported instruction: {i}")
        };
    }
}
