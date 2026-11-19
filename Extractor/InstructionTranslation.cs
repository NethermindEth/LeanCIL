using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class InstructionTranslation
{
    internal static Operation Translate(Instruction i, MethodDefinition m,
        IReadOnlyDictionary<MethodDefinition, int> methods, int methodIndex, InstructionIndex instructions,
        FeatureProfile? profile = null, NativeOperands.Certificate? nativeOperands = null,
        IReadOnlyDictionary<int, int>? parameterHomes = null, ImportResolution? imports = null,
        MetadataValidation.LayoutContext? layouts = null, ConstrainedCalls.TargetIndex? constrainedTargets = null)
    {
        InstructionPrefixes.ValidatePrefix(m, i);
        if (i.Previous is { } previous) InstructionPrefixes.ValidatePrefix(m, previous);
        if (imports is not null && imports.TryTranslate(i, methods.Count, out Operation? imported)) return imported;
        profile ??= FeatureProfile.Scalar;
        layouts?.Require(m.Module, profile.Architecture);
        var reachable = nativeOperands is null || parameterHomes is null
            ? Reachability.Analyze(m, profile) : null;
        nativeOperands ??= NativeOperands.Certify(m, reachable!, profile);
        if (i.OpCode.Code == Code.Calli && i.Operand is Mono.Cecil.CallSite indirect)
        {
            var tail = i.Previous?.OpCode.Code == Code.Tail;
            var signature = ManagedPointers.SignatureEvidence(indirect);
            return new IndirectCall(signature, ManagedPointers.Catalog(indirect, methods, methodIndex, tail), tail);
        }
        // Element loads of a handler table emit their decoded instructions with every other array.
        if (i.OpCode.Code is Code.Ldelem_Any &&
            nativeOperands.Incoming.TryGetValue(i, out var tableStack) && tableStack.Length >= 2 &&
            tableStack[^2] is { Kind: NativeOperands.Kind.MethodTable })
            return new TypedElementAccess(false, null);
        if (i.OpCode.Code == Code.Ldftn && i.Operand is MethodReference address)
        {
            var target = address.Resolve() ?? throw new InvalidDataException("Unresolved managed pointer target");
            var targetIndex = methods.GetValueOrDefault(target, -1);
            if (targetIndex < 0) throw new InvalidDataException("Managed pointer target is outside the catalog");
            return new MethodAddress(ManagedPointers.Target(target, targetIndex),
                ManagedPointers.SignatureEvidence(target));
        }
        if (TailCalls.IsCall(i) && i.Operand is MethodReference tailTarget &&
            nativeOperands.Incoming.TryGetValue(i, out var tailStack) &&
            tailStack.Length != tailTarget.Parameters.Count + (tailTarget.HasThis ? 1 : 0))
            throw new InvalidDataException("Tail call requires exactly its arguments on the evaluation stack");
        if (ReferenceArrays.Translate(i) is { } referenceOperation) return referenceOperation;
        if (Arrays.Translate(i, profile.Architecture) is { } arrayOperation) return arrayOperation;
        parameterHomes ??= ParameterStorage.IndexHomes(ParameterStorage.Analyze(m, reachable!));
        return TranslateCore(i, m, methods, methodIndex, instructions, profile, parameterHomes,
            layouts, constrainedTargets);
    }

    static Operation TranslateCore(Instruction i, MethodDefinition m,
        IReadOnlyDictionary<MethodDefinition, int> methods, int methodIndex, InstructionIndex instructions,
        FeatureProfile profile, IReadOnlyDictionary<int, int> parameterHomes, MetadataValidation.LayoutContext? layouts,
        ConstrainedCalls.TargetIndex? constrainedTargets)
    {
        profile ??= FeatureProfile.Scalar;
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
        if (i.OpCode.Code == Code.Constrained)
        {
            if (i.Next is null) throw new InvalidDataException("Constrained prefix has no call");
            ConstrainedCalls.Resolve(m, i.Next, instructions, profile.Architecture);
            return StackOperation.Nop;
        }
        var receiverCall = ObjectTypes.ReceiverCall(i);
        if (!receiverCall &&
            (i.OpCode.Code == Code.Callvirt || i is { OpCode.Code: Code.Call, Previous.OpCode.Code: Code.Constrained }))
        {
            var resolved = (constrainedTargets ?? new ConstrainedCalls.TargetIndex(methods.Keys))
                .Find(ConstrainedCalls.Resolve(m, i, instructions, profile.Architecture));
            var index = methods.GetValueOrDefault(resolved, -1);
            if (index <= methodIndex) throw new InvalidDataException("Unresolved constrained implementation");
            return new Call(CallKind.Static, index, resolved.Parameters.Count + (resolved.HasThis ? 1 : 0),
                Constrained: true);
        }
        if (throws.Raises.TryGetValue(i, out ExceptionType raised)) return new Throw(raised);
        if (throws.Operands.Contains(i)) return StackOperation.Nop;
        Operation JumpTo(JumpKind kind) => new Jump(kind, instructions.Position((Instruction)i.Operand));
        int LocalIndex() => ((VariableDefinition)i.Operand).Index;
        Operation LoadLocal(int index) => new Local(index);
        Operation StoreLocal(int index) => new SetLocal(index);
        Operation AddressLocal(int index) => new LocalAddress(index);
        // A store or address names the argument, which must have a home; the step reaches the home's slot.
        Operation Parameter(Func<int, Operation> operation)
        {
            var argument = MethodArguments.Index(m, (ParameterDefinition)i.Operand);
            if (!parameterHomes.ContainsKey(argument)) throw new InvalidDataException("Missing parameter storage");
            return operation(argument);
        }
        int Layout(TypeReference type) => layouts?.Size(type) ??
            MetadataValidation.Layout(type, m.Module, profile.Architecture);
        Operation Field(FieldAccess access)
        {
            var f = (FieldReference)i.Operand;
            FieldDefinition resolved = f.Resolve() ?? throw new InvalidDataException("Unresolved field");
            if (ObjectTypes.Candidate(f.DeclaringType))
                return ObjectTypes.FieldOperation(f, resolved, store: access == FieldAccess.Store,
                    address: access == FieldAccess.Address, profile.Architecture);
            Layout(f.DeclaringType);
            var actual = MetadataValidation.InstanceFieldOf(f);
            var fieldType = actual.Type;
            RuntimeModels.ValidateTypeIdentity(fieldType, m.Module, profile.Architecture);
            var aggregate = MetadataValidation.IsAggregate(fieldType, m.Module);
            int width = layouts?.FieldSize(fieldType) ??
                MetadataValidation.FieldSize(fieldType, m.Module, profile.Architecture);
            var owner = f.DeclaringType;
            int offset = layouts?.FieldOffset(owner, resolved) ??
                MetadataValidation.FieldOffset(owner, resolved, m.Module, profile.Architecture);
            if (aggregate && access != FieldAccess.Address)
                return new StructField(access == FieldAccess.Load ? FieldAccess.LoadAggregate :
                    FieldAccess.StoreAggregate, offset, width, false);
            var signed = access == FieldAccess.Load &&
                EnumTypes.Storage(fieldType).FullName is "System.SByte" or "System.Int16";
            return new StructField(access, offset, width, signed);
        }
        if (i.OpCode.Code is Code.Ldobj or Code.Stobj or Code.Initobj or Code.Sizeof or Code.Cpobj &&
            i.Operand is TypeReference operand)
        {
            RuntimeModels.ValidateTypeIdentity(operand, m.Module, profile.Architecture);
            if (Spans.Is(operand))
            {
                if (i.OpCode.Code == Code.Initobj) SpanReferences.ValidateReset(i, instructions);
                else if (i.OpCode.Code != Code.Ldobj)
                    throw new InvalidDataException($"Unsupported store to a span home: {i}");
                else SpanReferences.ValidateCopy(m, i, instructions);
            }
            else if (i.OpCode.Code == Code.Sizeof)
            {
                var size = MetadataValidation.IsAggregate(operand, m.Module)
                    ? layouts?.Size(operand) ?? MetadataValidation.Layout(operand, m.Module, profile.Architecture)
                    : MetadataValidation.IntegerVectorWidth(operand) ?? MetadataValidation.PrimitiveWidth(operand);
                return new ObjectInstruction(Code.Sizeof, ByteSize: size);
            }
            else if (!MetadataValidation.IsAggregate(operand, m.Module) &&
                MetadataValidation.IntegerVectorWidth(operand) is null)
            {
                var width = MetadataValidation.PrimitiveWidth(operand);
                var signed = EnumTypes.Storage(operand).MetadataType is MetadataType.SByte or MetadataType.Int16;
                return new ObjectInstruction(i.OpCode.Code, ScalarWidth: width, Signed: signed);
            }
            return new ObjectInstruction(i.OpCode.Code);
        }
        if (VirtualDispatch.Is(i))
        {
            var slot = (MethodReference)i.Operand;
            var entries = VirtualDispatch.Table(slot).Select(entry =>
            {
                var index = methods.GetValueOrDefault(entry.Body, -1);
                if (index <= methodIndex)
                    throw new InvalidDataException("Unresolved virtual implementation: " + entry.Body.FullName);
                return (Class: GenericEvidence.ObjectType(entry.Class), Method: index);
            }).ToArray();
            return new CallVirtual(entries, slot.Parameters.Count + 1);
        }
        if (i.OpCode.Code is Code.Call or Code.Newobj || receiverCall)
        {
            var r = (MethodReference)i.Operand;
            if (i.OpCode.Code == Code.Call && RuntimeModels.CallModel(r, profile) is { } model)
                return new ModelCall(model);
            if (i.OpCode.Code == Code.Newobj && Spans.ConstructorOperation(r, profile.Architecture) is { } source)
                return new ModelCall(MemoryOperation.Of(source)) { Constructs = true };
            if (RuntimeModels.Translate(r, profile) is { } modeled) return modeled;
            MethodDefinition resolved = r.Resolve() ?? throw new InvalidDataException($"Unresolved method: {r.FullName}");
            int index = methods.GetValueOrDefault(resolved, -1);
            if (index > methodIndex || index >= 0 && TailCalls.IsCall(i))
            {
                if (i.OpCode.Code == Code.Newobj && ObjectTypes.Candidate(resolved.DeclaringType))
                    return new Newobj(index, ObjectTypes.AllocationOf(resolved), null);
                if (i.OpCode.Code == Code.Newobj)
                    return new Newobj(index, new Allocation.Aggregate(
                        Layout(MethodSpecialization.DeclaringType(resolved))), null);
                var kind = TailCalls.IsCall(i) ? CallKind.Tail : receiverCall ? CallKind.Instance : CallKind.Static;
                return new Call(kind, index, resolved.Parameters.Count + (resolved.HasThis ? 1 : 0));
            }
            throw new InvalidDataException($"Unsupported or unresolved call: {r.FullName} [{r.DeclaringType.Scope.Name}]");
        }
        return i.OpCode.Code switch
        {
            Code.Nop or Code.Readonly => StackOperation.Nop,
            // Ordinary accesses already use the documented byte-aligned runtime model.
            // For block instructions the validated prefix selects the required alignment.
            Code.Unaligned => StackOperation.Nop,
            Code.Localloc => new Localloc(),
            Code.Cpblk => MemoryOperation.Other($"(.copyBlock {MemoryPrefixes.BlockAlignment(i)})"),
            Code.Initblk => MemoryOperation.Other($"(.initBlock {MemoryPrefixes.BlockAlignment(i)})"),
            Code.Starg or Code.Starg_S => Parameter(index => new Starg(index)),
            Code.Ldarga or Code.Ldarga_S when m.HasThis && i.Operand == m.Body.ThisParameter &&
                ObjectTypes.Candidate(m.DeclaringType) =>
                throw new InvalidDataException("Unsupported address of a class instance receiver: " + m.FullName),
            Code.Ldarga or Code.Ldarga_S when ObjectTypes.Rooted(((ParameterDefinition)i.Operand).ParameterType) =>
                throw new InvalidDataException("Unsupported address of a class instance argument: " + m.FullName),
            Code.Ldarga or Code.Ldarga_S => Parameter(index => new Ldarga(index)),
            Code.Conv_I => new StackOperation(StackOpcode.ConvI),
            Code.Ldind_I => new IndirectAccess(NumericKind.I, false),
            Code.Stind_I => new IndirectAccess(NumericKind.I, true),
            Code.Conv_Ovf_I1 => new CheckedConvert(ConvTarget.I1, false),
            Code.Conv_Ovf_I1_Un => new CheckedConvert(ConvTarget.I1, true),
            Code.Conv_Ovf_U1 => new CheckedConvert(ConvTarget.U1, false),
            Code.Conv_Ovf_U1_Un => new CheckedConvert(ConvTarget.U1, true),
            Code.Conv_Ovf_I2 => new CheckedConvert(ConvTarget.I2, false),
            Code.Conv_Ovf_I2_Un => new CheckedConvert(ConvTarget.I2, true),
            Code.Conv_Ovf_U2 => new CheckedConvert(ConvTarget.U2, false),
            Code.Conv_Ovf_U2_Un => new CheckedConvert(ConvTarget.U2, true),
            Code.Conv_Ovf_I4 => new CheckedConvert(ConvTarget.I4, false),
            Code.Conv_Ovf_I4_Un => new CheckedConvert(ConvTarget.I4, true),
            Code.Conv_Ovf_U4 => new CheckedConvert(ConvTarget.U4, false),
            Code.Conv_Ovf_U4_Un => new CheckedConvert(ConvTarget.U4, true),
            Code.Conv_Ovf_I8 => new CheckedConvert(ConvTarget.I8, false),
            Code.Conv_Ovf_I8_Un => new CheckedConvert(ConvTarget.I8, true),
            Code.Conv_Ovf_U8 => new CheckedConvert(ConvTarget.U8, false),
            Code.Conv_Ovf_U8_Un => new CheckedConvert(ConvTarget.U8, true),
            Code.Conv_Ovf_I => new CheckedConvert(ConvTarget.I, false),
            Code.Conv_Ovf_I_Un => new CheckedConvert(ConvTarget.I, true),
            Code.Conv_Ovf_U => new CheckedConvert(ConvTarget.U, false),
            Code.Conv_Ovf_U_Un => new CheckedConvert(ConvTarget.U, true),
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
            Code.Castclass or Code.Isinst => ObjectTypes.Test(i),
            Code.Ldstr => StringOperation((string)i.Operand),
            Code.Cgt => new StackOperation(StackOpcode.Cgt),
            Code.Bgt or Code.Bgt_S => JumpTo(JumpKind.Greater),
            Code.Ble or Code.Ble_S => JumpTo(JumpKind.LessOrEqual),
            Code.Ble_Un or Code.Ble_Un_S => JumpTo(JumpKind.LessOrEqualUnsigned),
            Code.Ldsfld when FeatureProfile.PlatformField((FieldReference)i.Operand) is int constant =>
                new Constant(32, constant, true),
            Code.Ldsfld or Code.Ldsflda or Code.Ldtoken when i.Operand is FieldReference =>
                StaticField(i, m.Module, profile.Architecture),
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
            Code.Ldloca or Code.Ldloca_S when ObjectTypes.Rooted(((VariableDefinition)i.Operand).VariableType) ||
                ReferenceArrays.Is(((VariableDefinition)i.Operand).VariableType) =>
                throw new InvalidDataException("Unsupported address of a class instance local: " + m.FullName),
            Code.Ldloca or Code.Ldloca_S => AddressLocal(LocalIndex()),
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

    // Literal methods and profile templates render the same validated field operand as the decoder.
    static Operation StaticField(Instruction instruction, ModuleDefinition module, string architecture)
    {
        StaticData.FieldOf(instruction, module, architecture);
        var opcode = instruction.OpCode.Code switch
        {
            Code.Ldsfld => StaticFieldOpcode.Ldsfld,
            Code.Ldsflda => StaticFieldOpcode.Ldsflda,
            _ => StaticFieldOpcode.Ldtoken
        };
        return new StaticFieldInstruction(opcode, null);
    }

    // Lean reads a surrogate escape as NUL, which would give distinct literals one key, and has no \b or \f.
    static Operation StringOperation(string text)
    {
        var unrepresentable = text.Any(c => char.IsSurrogate(c) || c is '\b' or '\f');
        if (unrepresentable)
            throw new InvalidDataException("Unsupported string literal: a surrogate, backspace or form feed");
        return MemoryOperation.Of(new StringLiteral(text));
    }
}
