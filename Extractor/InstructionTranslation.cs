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
        // Element loads of a handler table emit their decoded instructions with every other array.
        if (i.OpCode.Code == Code.Ldelem_Any && InstructionOperands.MethodTableLoad(i, nativeOperands))
            return new TypedElementAccess(false, null);
        InstructionOperands.ValidateTailStack(i, nativeOperands);
        if (ReferenceArrays.Translate(i) is { } referenceOperation) return referenceOperation;
        if (Arrays.Translate(i, profile.Architecture) is { } arrayOperation) return arrayOperation;
        parameterHomes ??= ParameterStorage.IndexHomes(ParameterStorage.Analyze(m, reachable!));
        return TranslateCore(i, m, methods, instructions, profile, parameterHomes,
            layouts, callSites);
    }

    static Operation TranslateCore(Instruction i, MethodDefinition m,
        IReadOnlyDictionary<MethodDefinition, int> methods, InstructionIndex instructions,
        FeatureProfile profile, IReadOnlyDictionary<int, int> parameterHomes, MetadataValidation.LayoutContext layouts,
        ResolvedCallSites callSites)
    {
        var typeTests = TypeTests.Analyze(m);
        if (i.OpCode.Code == Code.Tail)
        {
            TailCalls.ValidateReachable(m, i, profile.Architecture);
            return StackOperation.Nop;
        }
        if (typeTests.Results.TryGetValue(i, out bool same))
        {
            if (i.Operand is Instruction target)
                return same ? new Jump(JumpKind.Always, instructions.Position(target)) : StackOperation.Nop;
            return same ? new Constant(32, 1, true) : new Constant(32, 0, true);
        }
        if (typeTests.Operands.Contains(i)) return StackOperation.Nop;
        var throws = Throws.Analyze(m);
        if (i.OpCode.Code == Code.Constrained) return StackOperation.Nop;
        var receiverCall = ObjectTypes.ReceiverCall(i);
        if (!receiverCall &&
            (i.OpCode.Code == Code.Callvirt || i is { OpCode.Code: Code.Call, Previous.OpCode.Code: Code.Constrained }))
        {
            var (resolved, index) = callSites.Target(i, methods);
            return new Call(CallKind.Static, index, resolved.Parameters.Count + (resolved.HasThis ? 1 : 0));
        }
        if (throws.Raises.TryGetValue(i, out ExceptionType raised)) return new Throw(raised);
        if (throws.Operands.Contains(i)) return StackOperation.Nop;
        Operation JumpTo(JumpKind kind) => new Jump(kind, instructions.Position((Instruction)i.Operand));
        int LocalIndex() => ((VariableDefinition)i.Operand).Index;
        Operation LoadLocal(int index) => new Local(index);
        Operation StoreLocal(int index) => new SetLocal(index);
        Operation AddressLocal(int index) => new LocalAddress(index);
        Operation Field(FieldAccess access)
        {
            var field = (FieldReference)i.Operand;
            var resolved = field.Resolve() ?? throw new InvalidDataException("Unresolved field");
            if (ObjectTypes.Candidate(field.DeclaringType))
                return new ClassField(ObjectTypes.FieldOperation(field, resolved, access == FieldAccess.Store,
                    access == FieldAccess.Address, profile.Architecture));
            var shape = InstructionOperands.StructField(field, resolved, access, m, profile, layouts);
            return new StructField(shape.Access, shape.Offset, shape.Width, shape.Signed);
        }
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
                return MemoryOperation.Of(source);
            if (i.OpCode.Code == Code.Newobj) return Unoutlined.Site;
            var (resolved, index) = callSites.Target(i, methods);
            var kind = TailCalls.IsCall(i) ? CallKind.Tail : receiverCall ? CallKind.Instance : CallKind.Static;
            return new Call(kind, index, resolved.Parameters.Count + (resolved.HasThis ? 1 : 0));
        }
        if (InstructionOperands.CheckedConversion(i.OpCode.Code) is { } conversion)
            return new CheckedConvert(conversion.Target, conversion.Unsigned);
        return i.OpCode.Code switch
        {
            Code.Nop or Code.Readonly => StackOperation.Nop,
            // Ordinary accesses already use the documented byte-aligned runtime model.
            // For block instructions the validated prefix selects the required alignment.
            Code.Unaligned => StackOperation.Nop,
            Code.Localloc => new Localloc(),
            Code.Cpblk => MemoryOperation.Other($"(.copyBlock {MemoryPrefixes.BlockAlignment(i)})"),
            Code.Initblk => MemoryOperation.Other($"(.initBlock {MemoryPrefixes.BlockAlignment(i)})"),
            Code.Starg or Code.Starg_S => new Starg(InstructionOperands.HomedArgument(m, i, parameterHomes)),
            Code.Ldarga or Code.Ldarga_S => new Ldarga(InstructionOperands.HomedArgument(m, i, parameterHomes)),
            Code.Conv_I => new StackOperation(StackOpcode.ConvI),
            Code.Ldind_I => new IndirectAccess(NumericKind.I, false),
            Code.Stind_I => new IndirectAccess(NumericKind.I, true),
            Code.Add_Ovf => new CheckedArithmetic(CheckedOperator.Add, true),
            Code.Add_Ovf_Un => new CheckedArithmetic(CheckedOperator.Add, false),
            Code.Sub_Ovf => new CheckedArithmetic(CheckedOperator.Sub, true),
            Code.Sub_Ovf_Un => new CheckedArithmetic(CheckedOperator.Sub, false),
            Code.Mul_Ovf => new CheckedArithmetic(CheckedOperator.Mul, true),
            Code.Mul_Ovf_Un => new CheckedArithmetic(CheckedOperator.Mul, false),
            Code.Div => new Divide(true, false),
            Code.Div_Un => new Divide(false, false),
            Code.Rem => new Divide(true, true),
            Code.Rem_Un => new Divide(false, true),
            Code.Switch => new Switch(((Instruction[])i.Operand).Select(instructions.Position).ToArray()),
            Code.Ldind_I1 => new IndirectAccess(NumericKind.I1, false),
            Code.Ldind_U1 => new IndirectAccess(NumericKind.U1, false),
            Code.Ldind_I2 => new IndirectAccess(NumericKind.I2, false),
            Code.Ldind_U2 => new IndirectAccess(NumericKind.U2, false),
            Code.Ldind_I4 => new IndirectAccess(NumericKind.I4, false),
            Code.Ldind_U4 => new IndirectAccess(NumericKind.U4, false),
            Code.Stind_I1 => new IndirectAccess(NumericKind.I1, true),
            Code.Stind_I2 => new IndirectAccess(NumericKind.I2, true),
            Code.Stind_I4 => new IndirectAccess(NumericKind.I4, true),
            Code.Conv_I1 => new StackOperation(StackOpcode.ConvI1),
            Code.Conv_I2 => new StackOperation(StackOpcode.ConvI2),
            Code.Conv_U2 => new StackOperation(StackOpcode.ConvU2),
            Code.Neg => new StackOperation(StackOpcode.Neg),
            Code.Ldnull => new LoadNull(),
            Code.Castclass => new CastClass(ObjectTypes.TestOperand(i)),
            Code.Isinst => new IsInstance(ObjectTypes.TestOperand(i)),
            Code.Ldstr => StringOperation((string)i.Operand),
            Code.Cgt => new StackOperation(StackOpcode.Cgt),
            Code.Bgt or Code.Bgt_S => JumpTo(JumpKind.Greater),
            Code.Ble or Code.Ble_S => JumpTo(JumpKind.LessOrEqual),
            Code.Ble_Un or Code.Ble_Un_S => JumpTo(JumpKind.LessOrEqualUnsigned),
            Code.Ldsfld when FeatureProfile.PlatformField((FieldReference)i.Operand) is int constant =>
                new Constant(32, constant, true),
            Code.Ldsfld or Code.Ldsflda or Code.Ldtoken when i.Operand is FieldReference =>
                Unoutlined.Site,
            Code.Stsfld => throw new InvalidDataException($"Unsupported static field store: {i}\n  Static fields are written only by their static constructor, which is never extracted."),
            Code.Ldarg_0 => new Arg(0),
            Code.Ldarg_1 => new Arg(1),
            Code.Ldarg_2 => new Arg(2),
            Code.Ldarg_3 => new Arg(3),
            Code.Ldarg or Code.Ldarg_S => new Arg(MethodArguments.Index(m, (ParameterDefinition)i.Operand)),
            Code.Ldloc_0 => LoadLocal(0),
            Code.Ldloc_1 => LoadLocal(1),
            Code.Ldloc_2 => LoadLocal(2),
            Code.Ldloc_3 => LoadLocal(3),
            Code.Ldloc or Code.Ldloc_S => LoadLocal(LocalIndex()),
            Code.Ldloca or Code.Ldloca_S => AddressLocal(InstructionOperands.AddressedLocal(m, i)),
            Code.Stloc_0 => StoreLocal(0),
            Code.Stloc_1 => StoreLocal(1),
            Code.Stloc_2 => StoreLocal(2),
            Code.Stloc_3 => StoreLocal(3),
            Code.Stloc or Code.Stloc_S => StoreLocal(LocalIndex()),
            Code.Ldfld => Field(FieldAccess.Load),
            Code.Ldflda => Field(FieldAccess.Address),
            Code.Stfld => Field(FieldAccess.Store),
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
            Code.Conv_I8 => new StackOperation(StackOpcode.ConvI8),
            Code.Conv_U => new StackOperation(StackOpcode.ConvU),
            Code.Conv_U1 => new StackOperation(StackOpcode.ConvU1),
            Code.Add => new StackOperation(StackOpcode.Add),
            Code.Conv_U4 => new StackOperation(StackOpcode.ConvU4),
            Code.Conv_U8 => new StackOperation(StackOpcode.ConvU8),
            Code.Not => new StackOperation(StackOpcode.Not),
            Code.Sub => new StackOperation(StackOpcode.Sub),
            Code.And => new StackOperation(StackOpcode.And),
            Code.Or => new StackOperation(StackOpcode.Or),
            Code.Xor => new StackOperation(StackOpcode.Xor),
            Code.Mul => new StackOperation(StackOpcode.Mul),
            Code.Shl => new StackOperation(StackOpcode.Shl),
            Code.Shr => new StackOperation(StackOpcode.Shr),
            Code.Shr_Un => new StackOperation(StackOpcode.ShrUn),
            Code.Conv_I4 => new StackOperation(StackOpcode.ConvI4),
            Code.Clt => new StackOperation(StackOpcode.Clt),
            Code.Clt_Un => new StackOperation(StackOpcode.CltUn),
            Code.Cgt_Un => new StackOperation(StackOpcode.CgtUn),
            Code.Ceq => new StackOperation(StackOpcode.Ceq),
            Code.Ldind_I8 => new IndirectAccess(NumericKind.I8, false),
            Code.Stind_I8 => new IndirectAccess(NumericKind.I8, true),
            Code.Dup => new StackOperation(StackOpcode.Dup),
            Code.Pop => new StackOperation(StackOpcode.Pop),
            Code.Br or Code.Br_S => JumpTo(JumpKind.Always),
            Code.Brfalse or Code.Brfalse_S => JumpTo(JumpKind.IfZero),
            Code.Brtrue or Code.Brtrue_S => JumpTo(JumpKind.IfNonzero),
            Code.Blt_Un or Code.Blt_Un_S => JumpTo(JumpKind.LessUnsigned),
            Code.Bge_Un or Code.Bge_Un_S => JumpTo(JumpKind.GreaterOrEqualUnsigned),
            Code.Bgt_Un or Code.Bgt_Un_S => JumpTo(JumpKind.GreaterUnsigned),
            Code.Bge or Code.Bge_S => JumpTo(JumpKind.GreaterOrEqual),
            Code.Blt or Code.Blt_S => JumpTo(JumpKind.Less),
            Code.Beq or Code.Beq_S => JumpTo(JumpKind.Equal),
            Code.Bne_Un or Code.Bne_Un_S => JumpTo(JumpKind.NotEqual),
            Code.Ret => new Return(),
            _ => throw new InvalidDataException($"Unsupported instruction: {i}")
        };
    }

    // Lean reads a surrogate escape as NUL, which would give distinct literals one key, and has no \b or \f.
    static Operation StringOperation(string text)
    {
        InstructionOperands.ValidateLiteral(text);
        return MemoryOperation.Of(new StringLiteral(text));
    }
}
