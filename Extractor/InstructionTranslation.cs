using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class InstructionTranslation
{
    internal static Operation? RuntimeModel(MethodReference reference, FeatureProfile? profile = null)
    {
        if (FeatureProfile.PlatformConstant(reference) is int constant) return new Constant(32, constant, true);
        if (FeatureProfile.Getter(reference) is Feature feature) return new FeatureTest(feature);
        return RuntimeModels.Translate(reference, profile ?? FeatureProfile.Scalar);
    }
    internal static Operation Translate(Instruction i, MethodDefinition m,
        IReadOnlyDictionary<MethodDefinition, int> methods, int methodIndex, InstructionIndex instructions,
        FeatureProfile? profile = null, NativeOperands.Certificate? nativeOperands = null,
        IReadOnlyDictionary<int, int>? parameterHomes = null, ImportResolution? imports = null,
        MetadataValidation.LayoutContext? layouts = null, ConstrainedCalls.TargetIndex? constrainedTargets = null)
    {
        if (imports is not null && imports.TryTranslate(i, methods.Count, out Operation? imported)) return imported;
        profile ??= FeatureProfile.Scalar;
        layouts?.Require(m.Module, profile.Architecture);
        var reachable = nativeOperands is null || parameterHomes is null
            ? Reachability.Analyze(m, profile) : null;
        nativeOperands ??= NativeOperands.Certify(m, reachable!, profile);
        if (nativeOperands.Incoming.TryGetValue(i, out var dispatchStack))
        {
            if (i.OpCode.Code == Code.Add && dispatchStack.Length >= 2 &&
                NativeOperands.NativeTableAddition(dispatchStack[^2], dispatchStack[^1]))
                return new TableOffset();
            if (i.OpCode.Code == Code.Ldind_I && dispatchStack.LastOrDefault() is
                { Kind: NativeOperands.Kind.NativeMethodTable, Metadata: LocalKind.NativeMethodTable nativeTable })
                return new TableLoad(nativeTable.Signature);
        }
        if (i.OpCode.Code == Code.Calli && i.Operand is Mono.Cecil.CallSite indirect)
        {
            var tail = i.Previous?.OpCode.Code == Code.Tail;
            var signature = ManagedPointers.SignatureEvidence(indirect);
            return new IndirectCall(signature, ManagedPointers.Catalog(indirect, methods, methodIndex, tail), tail);
        }
        if (i.OpCode.Code is Code.Ldlen or Code.Ldelem_I or Code.Ldelem_Any &&
            nativeOperands.Incoming.TryGetValue(i, out var tableStack) &&
            tableStack.Length >= (i.OpCode.Code == Code.Ldlen ? 1 : 2) &&
            tableStack[^(i.OpCode.Code == Code.Ldlen ? 1 : 2)] is
                { Kind: NativeOperands.Kind.MethodTable, Metadata: LocalKind.MethodTable table })
            return i.OpCode.Code == Code.Ldlen ? new TableLength() : new TableElement(table.Signature);
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
        if (i.OpCode.Code == Code.Add && nativeOperands.Incoming.TryGetValue(i, out var incoming) &&
            incoming.Length >= 2 && NativeOperands.ReferenceAddition(incoming[^2], incoming[^1]))
            return MemoryOperation.Of(new AddOffset(1, true));
        if (i.OpCode.Code == Code.Readonly)
        {
            Arrays.ValidateReadOnly(instructions, i);
            return StackOperation.Nop;
        }
        if (i.Previous?.OpCode.Code == Code.Readonly) Arrays.ValidateReadOnly(instructions, i.Previous);
        var referenceArray = i.OpCode.Code == Code.Ldlen &&
            nativeOperands.Incoming.TryGetValue(i, out var lengthStack) &&
            lengthStack.LastOrDefault().Kind == NativeOperands.Kind.Object;
        if (ReferenceArrays.Translate(i, referenceArray) is { } referenceOperation) return referenceOperation;
        if (Arrays.Translate(i, profile.Architecture) is { } arrayOperation) return arrayOperation;
        parameterHomes ??= ParameterStorage.IndexHomes(ParameterStorage.Analyze(m, reachable!));
        var translated = TranslateCore(i, m, methods, methodIndex, instructions, profile, parameterHomes,
            layouts, constrainedTargets);
        return nativeOperands.Mixed.Contains(i) ? new NativeBinary(translated) : translated;
    }

    static Operation Checked(int width, bool signed, bool unsignedSource) =>
        new CheckedConvert(width, signed, unsignedSource);

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
            return new Call(CallKind.Static, index, resolved.Parameters.Count + (resolved.HasThis ? 1 : 0));
        }
        if (throws.Raises.TryGetValue(i, out string? raised)) return new Throw(raised);
        var spans = Spans.Analyze(m, profile);
        if (spans.Constructors.TryGetValue(i, out var constructor)) return constructor;
        if (throws.Operands.Contains(i) || spans.Operands.Contains(i)) return StackOperation.Nop;
        Operation JumpTo(JumpKind kind) => new Jump(kind, instructions.Position((Instruction)i.Operand));
        int LocalIndex() => ((VariableDefinition)i.Operand).Index;
        Narrowing? NarrowOf(TypeReference type) => LeanEmitter.Narrow(type);
        Operation LoadLocal(int index) => new Local(index, NarrowOf(m.Body.Variables[index].VariableType));
        Operation StoreLocal(int index) => new SetLocal(index, NarrowOf(m.Body.Variables[index].VariableType));
        Operation AddressLocal(int index) => new LocalAddress(index);
        Operation LoadArgument(int index)
        {
            var home = parameterHomes.GetValueOrDefault(index, -1);
            return home < 0 ? new Arg(index, NarrowOf(MethodArguments.Type(m, index))) :
                new Local(m.Body.Variables.Count + home, null);
        }
        Operation Parameter(Func<int, Operation> operation)
        {
            var home = parameterHomes.GetValueOrDefault(MethodArguments.Index(m, (ParameterDefinition)i.Operand), -1);
            if (home < 0) throw new InvalidDataException("Missing parameter storage");
            return operation(m.Body.Variables.Count + home);
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
        if (i.OpCode.Code is Code.Ldobj or Code.Stobj or Code.Initobj or Code.Sizeof or Code.Cpobj && i.Operand is TypeReference operandType)
            RuntimeModels.ValidateTypeIdentity(operandType, m.Module, profile.Architecture);
        if (i.OpCode.Code is Code.Ldobj or Code.Stobj or Code.Initobj or Code.Cpobj &&
            i.Operand is TypeReference spanType && Spans.Is(spanType))
        {
            // A span address on the stack is the view itself, so a copy leaves it in place.
            if (i.OpCode.Code != Code.Ldobj)
                throw new InvalidDataException($"Unsupported store to a span home: {i}");
            SpanReferences.ValidateCopy(m, i, instructions);
            return StackOperation.Nop;
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
            if (i.OpCode.Code == Code.Call
                && RuntimeModels.ObjectConstructor(r)) return new StackOperation(StackOpcode.Pop);
            if (RuntimeModel(r, profile) is { } modeled) return modeled;
            MethodDefinition resolved = r.Resolve() ?? throw new InvalidDataException($"Unresolved method: {r.FullName}");
            int index = methods.GetValueOrDefault(resolved, -1);
            if (index > methodIndex || index >= 0 && TailCalls.IsCall(i))
            {
                if (i.OpCode.Code == Code.Newobj && ObjectTypes.Candidate(resolved.DeclaringType))
                    return ObjectTypes.Construction(resolved, index);
                if (i.OpCode.Code == Code.Newobj)
                    return new NewAggregate(index, resolved.Parameters.Count,
                        Layout(MethodSpecialization.DeclaringType(resolved)));
                var kind = TailCalls.IsCall(i) ? CallKind.Tail : receiverCall ? CallKind.Instance : CallKind.Static;
                return new Call(kind, index, resolved.Parameters.Count + (resolved.HasThis ? 1 : 0));
            }
            throw new InvalidDataException($"Unsupported or unresolved call: {r.FullName} [{r.DeclaringType.Scope.Name}]");
        }
        return i.OpCode.Code switch
        {
            Code.Nop => StackOperation.Nop,
            // Ordinary accesses already use the documented byte-aligned runtime model.
            // For block instructions the validated prefix selects the required alignment.
            Code.Unaligned => StackOperation.Nop,
            Code.Localloc => new StackAlloc(m.Body.InitLocals),
            Code.Cpblk => MemoryOperation.Other($"(.copyBlock {MemoryPrefixes.BlockAlignment(i)})"),
            Code.Initblk => MemoryOperation.Other($"(.initBlock {MemoryPrefixes.BlockAlignment(i)})"),
            Code.Starg or Code.Starg_S => Parameter(index => new SetLocal(index, null)),
            Code.Ldarga or Code.Ldarga_S when m.HasThis && i.Operand == m.Body.ThisParameter &&
                ObjectTypes.Candidate(m.DeclaringType) =>
                throw new InvalidDataException("Unsupported address of a class instance receiver: " + m.FullName),
            Code.Ldarga or Code.Ldarga_S when ObjectTypes.Rooted(((ParameterDefinition)i.Operand).ParameterType) =>
                throw new InvalidDataException("Unsupported address of a class instance argument: " + m.FullName),
            Code.Ldarga or Code.Ldarga_S => Parameter(
                !Spans.Is(((ParameterDefinition)i.Operand).ParameterType)
                    ? index => new LocalAddress(index) : index => new Local(index, null)),
            Code.Conv_I => new StackOperation(StackOpcode.ConvI8),
            Code.Ldind_I => new StackOperation(StackOpcode.Load64),
            Code.Stind_I => new StackOperation(StackOpcode.Store64),
            Code.Conv_Ovf_I1 => Checked(8, true, false),
            Code.Conv_Ovf_I1_Un => Checked(8, true, true),
            Code.Conv_Ovf_U1 => Checked(8, false, false),
            Code.Conv_Ovf_U1_Un => Checked(8, false, true),
            Code.Conv_Ovf_I2 => Checked(16, true, false),
            Code.Conv_Ovf_I2_Un => Checked(16, true, true),
            Code.Conv_Ovf_U2 => Checked(16, false, false),
            Code.Conv_Ovf_U2_Un => Checked(16, false, true),
            Code.Conv_Ovf_I4 => Checked(32, true, false),
            Code.Conv_Ovf_I4_Un => Checked(32, true, true),
            Code.Conv_Ovf_U4 => Checked(32, false, false),
            Code.Conv_Ovf_U4_Un => Checked(32, false, true),
            Code.Conv_Ovf_I8 => Checked(64, true, false),
            Code.Conv_Ovf_I8_Un => Checked(64, true, true),
            Code.Conv_Ovf_U8 => Checked(64, false, false),
            Code.Conv_Ovf_U8_Un => Checked(64, false, true),
            Code.Conv_Ovf_I => Checked(profile.NativeWidth, true, false),
            Code.Conv_Ovf_I_Un => Checked(profile.NativeWidth, true, true),
            Code.Conv_Ovf_U => Checked(profile.NativeWidth, false, false),
            Code.Conv_Ovf_U_Un => Checked(profile.NativeWidth, false, true),
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
            Code.Sizeof => new Constant(32,
                TypeWidth((TypeReference)i.Operand, m.Module, profile.Architecture, layouts), true),
            Code.Cpobj => new AggregateTransfer(AggregateAccess.Copy,
                TypeWidth((TypeReference)i.Operand, m.Module, profile.Architecture, layouts)),
            Code.Ldind_I1 => new LoadScalar(1, true),
            Code.Ldind_U1 => new LoadScalar(1, false),
            Code.Ldind_I2 => new LoadScalar(2, true),
            Code.Ldind_U2 => new LoadScalar(2, false),
            Code.Ldind_I4 or Code.Ldind_U4 => new LoadScalar(4, false),
            Code.Stind_I1 => new StoreScalar(1),
            Code.Stind_I2 => new StoreScalar(2),
            Code.Stind_I4 => new StoreScalar(4),
            Code.Conv_I1 => new StackOperation(StackOpcode.ConvI1),
            Code.Conv_I2 => new StackOperation(StackOpcode.ConvI2),
            Code.Conv_U2 => new StackOperation(StackOpcode.ConvU2),
            Code.Neg => new StackOperation(StackOpcode.Neg),
            Code.Ldnull => MemoryOperation.Of(new NullObject()),
            Code.Castclass or Code.Isinst => ObjectTypes.Test(i),
            Code.Ldstr => StringOperation((string)i.Operand),
            Code.Cgt => new StackOperation(StackOpcode.Cgt),
            Code.Bgt or Code.Bgt_S => JumpTo(JumpKind.Greater),
            Code.Ble or Code.Ble_S => JumpTo(JumpKind.LessOrEqual),
            Code.Ble_Un or Code.Ble_Un_S => JumpTo(JumpKind.LessOrEqualUnsigned),
            Code.Ldsfld when FeatureProfile.PlatformField((FieldReference)i.Operand) is int constant =>
                new Constant(32, constant, true),
            Code.Ldsfld or Code.Ldsflda when StaticValues.IsLoad(i) =>
                StaticLoad(i, m.Module, profile.Architecture),
            Code.Stsfld => throw new InvalidDataException($"Unsupported static field store: {i}\n  Static fields are written only by their static constructor, which is never extracted."),
            Code.Ldsflda or Code.Ldtoken when i.Operand is FieldReference =>
                MemoryOperation.Of(new StaticAddress(
                    StaticData.Validate((FieldReference)i.Operand, m.Module).InitialValue)),
            Code.Ldobj when MetadataValidation.IsAggregate((TypeReference)i.Operand, m.Module) =>
                new AggregateTransfer(AggregateAccess.Load, Layout((TypeReference)i.Operand)),
            Code.Initobj when MetadataValidation.IsAggregate((TypeReference)i.Operand, m.Module) =>
                new AggregateTransfer(AggregateAccess.Initialize, Layout((TypeReference)i.Operand)),
            Code.Stobj when MetadataValidation.IsAggregate((TypeReference)i.Operand, m.Module) =>
                new AggregateTransfer(AggregateAccess.Store, Layout((TypeReference)i.Operand)),
            Code.Ldobj when MetadataValidation.IntegerVectorWidth((TypeReference)i.Operand) is int width =>
                MemoryOperation.Other($".load{width * 8}"),
            Code.Stobj when MetadataValidation.IntegerVectorWidth((TypeReference)i.Operand) is int width =>
                MemoryOperation.Other($".store{width * 8}"),
            Code.Initobj when MetadataValidation.IntegerVectorWidth((TypeReference)i.Operand) is int width =>
                new AggregateTransfer(AggregateAccess.Initialize, width),
            Code.Ldobj => ScalarLoad((TypeReference)i.Operand),
            Code.Stobj => new StoreScalar(MetadataValidation.PrimitiveWidth((TypeReference)i.Operand)),
            Code.Initobj => new AggregateTransfer(AggregateAccess.Initialize,
                MetadataValidation.PrimitiveWidth((TypeReference)i.Operand)),
            Code.Ldarg_0 => LoadArgument(0),
            Code.Ldarg_1 => LoadArgument(1),
            Code.Ldarg_2 => LoadArgument(2),
            Code.Ldarg_3 => LoadArgument(3),
            Code.Ldarg or Code.Ldarg_S => LoadArgument(MethodArguments.Index(m, (ParameterDefinition)i.Operand)),
            Code.Ldloc_0 => LoadLocal(0),
            Code.Ldloc_1 => LoadLocal(1),
            Code.Ldloc_2 => LoadLocal(2),
            Code.Ldloc_3 => LoadLocal(3),
            Code.Ldloc or Code.Ldloc_S => LoadLocal(LocalIndex()),
            Code.Ldloca or Code.Ldloca_S when ObjectTypes.Rooted(((VariableDefinition)i.Operand).VariableType) ||
                ReferenceArrays.Is(((VariableDefinition)i.Operand).VariableType) =>
                throw new InvalidDataException("Unsupported address of a class instance local: " + m.FullName),
            Code.Ldloca or Code.Ldloca_S => !Spans.Is(((VariableDefinition)i.Operand).VariableType)
                ? AddressLocal(LocalIndex()) : LoadLocal(LocalIndex()),
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
            Code.Ldind_I8 => new StackOperation(StackOpcode.Load64),
            Code.Stind_I8 => new StackOperation(StackOpcode.Store64),
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
            Code.Ret => new Return(NarrowOf(m.ReturnType)),
            _ => throw new InvalidDataException($"Unsupported instruction: {i}")
        };
    }

    static Operation StaticLoad(Instruction i, ModuleDefinition module, string architecture)
    {
        var bytes = StaticValues.Resolve((FieldReference)i.Operand, module, architecture).Bytes;
        return MemoryOperation.Of(i.OpCode.Code == Code.Ldsfld ? new StaticValue(bytes) : new StaticAddress(bytes));
    }

    // An enumeration loads through its storage type, which is signed for the two narrow signed integers.
    static Operation ScalarLoad(TypeReference type)
    {
        var width = MetadataValidation.PrimitiveWidth(type);
        var signed = EnumTypes.Storage(type).FullName is "System.SByte" or "System.Int16";
        return new LoadScalar(width, signed);
    }

    static int TypeWidth(TypeReference type, ModuleDefinition module, string architecture,
        MetadataValidation.LayoutContext? layouts) => MetadataValidation.IsAggregate(type, module)
        ? layouts?.Size(type) ?? MetadataValidation.Layout(type, module, architecture)
        : MetadataValidation.IntegerVectorWidth(type) ?? MetadataValidation.PrimitiveWidth(type);

    // Lean reads a surrogate escape as NUL, which would give distinct literals one key, and has no \b or \f.
    static Operation StringOperation(string text)
    {
        var unrepresentable = text.Any(c => char.IsSurrogate(c) || c is '\b' or '\f');
        if (unrepresentable)
            throw new InvalidDataException("Unsupported string literal: a surrogate, backspace or form feed");
        return MemoryOperation.Of(new StringLiteral(text));
    }
}
