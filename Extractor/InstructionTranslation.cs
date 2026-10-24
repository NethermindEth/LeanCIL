using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

internal static class InstructionTranslation
{
    internal static string? RuntimeModel(MethodReference reference, FeatureProfile? profile = null)
    {
        if (FeatureProfile.Getter(reference) is Feature feature)
            return ".feature " + FeatureProfile.LeanFeature(feature);
        return RuntimeModels.Translate(reference, profile ?? FeatureProfile.Scalar);
    }
    internal static string Translate(Instruction i, MethodDefinition m, MethodDefinition[] methods, int methodIndex,
        FeatureProfile? profile = null, HashSet<Instruction>? nativeOperands = null, int[]? parameterHomes = null, ImportResolution? imports = null)
    {
        if (imports is not null && imports.TryTranslate(i, methods.Length, out string imported)) return imported;
        profile ??= FeatureProfile.Scalar;
        var translated = TranslateCore(i, m, methods, methodIndex, profile, parameterHomes ?? ParameterStorage.Analyze(m, profile));
        return (nativeOperands ?? NativeOperands.Analyze(m, profile)).Contains(i) ? $".nativeBinary ({translated})" : translated;
    }

    static string TranslateCore(Instruction i, MethodDefinition m, MethodDefinition[] methods, int methodIndex,
        FeatureProfile profile, int[] parameterHomes)
    {
        profile ??= FeatureProfile.Scalar;
        var typeTests = TypeTests.Analyze(m);
        if (typeTests.Results.TryGetValue(i, out bool same)) return same ? ".const32 1" : ".const32 0";
        if (typeTests.Operands.Contains(i)) return ".nop";
        var throws = Throws.Analyze(m);
        if (throws.Raises.TryGetValue(i, out string? raised)) return $".throw \"{raised}\"";
        if (throws.Operands.Contains(i) || Spans.Analyze(m).Operands.Contains(i)) return ".nop";
        int Target() => m.Body.Instructions.IndexOf((Instruction)i.Operand);
        int Local() => ((VariableDefinition)i.Operand).Index;
        string Narrow(TypeReference type) => LeanEmitter.Narrow(type) is { } kind ? $" (some .{kind})" : "";
        string LocalOp(string op, int index) => $".{op} {index}" +
            (op is "local" or "setLocal" ? Narrow(m.Body.Variables[index].VariableType) : "");
        string Arg(int index)
        {
            var home = Array.IndexOf(parameterHomes, index);
            return home < 0 ? $".arg {index}" + Narrow(MethodArguments.Type(m, index)) :
                $".local {m.Body.Variables.Count + home}";
        }
        string Parameter(string op)
        {
            var home = Array.IndexOf(parameterHomes, MethodArguments.Index(m, (ParameterDefinition)i.Operand));
            if (home < 0) throw new InvalidDataException("Missing parameter storage");
            return $".{op} {m.Body.Variables.Count + home}";
        }
        string Field(string op)
        {
            var f = (FieldReference)i.Operand;
            FieldDefinition resolved = f.Resolve() ?? throw new InvalidDataException("Unresolved field");
            MetadataValidation.Layout(f.DeclaringType, m.Module, profile.Architecture);
            RuntimeModels.ValidateTypeIdentity(f.FieldType, m.Module, profile.Architecture);
            var tuple = ValueTuples.Is(f.DeclaringType);
            var field = tuple ? MetadataValidation.Fields(f.DeclaringType).SingleOrDefault(candidate =>
                candidate.Definition == resolved && f.FieldType is GenericParameter parameter &&
                resolved.FieldType is GenericParameter definition && parameter.Position == definition.Position) : null;
            if (resolved.IsStatic || (tuple ? field is null : resolved.Module != m.Module || resolved.FullName != f.FullName))
                throw new InvalidDataException($"Unsupported field {f.FullName}");
            var fieldType = field?.Type ?? resolved.FieldType;
            var aggregate = MetadataValidation.IsAggregate(fieldType, m.Module);
            int width = MetadataValidation.FieldSize(fieldType, m.Module, profile.Architecture);
            int offset = MetadataValidation.FieldOffset(tuple ? f.DeclaringType : resolved.DeclaringType, resolved, m.Module, profile.Architecture);
            if (aggregate && op != "fieldAddr")
                return $".{(op == "field" ? "aggregateFieldAt" : "setAggregateFieldAt")} {offset} {width}";
            return op == "fieldAddr" ? $".fieldAddress {offset}" :
                $".{(op == "field" ? "fieldAt" : "setFieldAt")} {offset} {width}" +
                (op == "field" && EnumTypes.Storage(fieldType).FullName is "System.SByte" or "System.Int16" ? " true" : "");
        }
        if (i.OpCode.Code is Code.Ldobj or Code.Stobj or Code.Initobj or Code.Sizeof or Code.Cpobj && i.Operand is TypeReference operandType)
            RuntimeModels.ValidateTypeIdentity(operandType, m.Module, profile.Architecture);
        if (i.OpCode.Code is Code.Call or Code.Newobj)
        {
            var r = (MethodReference)i.Operand;
            if (RuntimeModel(r, profile) is string modeled) return modeled;
            MethodDefinition resolved = r.Resolve() ?? throw new InvalidDataException($"Unresolved method: {r.FullName}");
            int index = Array.IndexOf(methods, resolved);
            if (index > methodIndex)
            {
                if (i.OpCode.Code == Code.Newobj)
                    return $".newAggregate {index} {resolved.Parameters.Count} {MetadataValidation.Layout(resolved.DeclaringType, m.Module, profile.Architecture)}";
                return $".call {index} {resolved.Parameters.Count + (resolved.HasThis ? 1 : 0)}";
            }
            throw new InvalidDataException($"Unsupported or unresolved call: {r.FullName} [{r.DeclaringType.Scope.Name}]");
        }
        return i.OpCode.Code switch
        {
            Code.Nop => ".nop",
            // Ordinary accesses already use the documented byte-aligned runtime model.
            // For block instructions the validated prefix selects the required alignment.
            Code.Unaligned => ".nop",
            Code.Cpblk => $".memory (.copyBlock {MemoryPrefixes.BlockAlignment(i)})",
            Code.Initblk => $".memory (.initBlock {MemoryPrefixes.BlockAlignment(i)})",
            Code.Starg or Code.Starg_S => Parameter("setLocal"),
            Code.Ldarga or Code.Ldarga_S => Parameter("localAddr"),
            Code.Conv_I => ".convI8",
            Code.Ldind_I => ".load64", Code.Stind_I => ".store64",
            Code.Conv_Ovf_I1 => ".checkedConvert 8 true false", Code.Conv_Ovf_I1_Un => ".checkedConvert 8 true true",
            Code.Conv_Ovf_U1 => ".checkedConvert 8 false false", Code.Conv_Ovf_U1_Un => ".checkedConvert 8 false true",
            Code.Conv_Ovf_I2 => ".checkedConvert 16 true false", Code.Conv_Ovf_I2_Un => ".checkedConvert 16 true true",
            Code.Conv_Ovf_U2 => ".checkedConvert 16 false false", Code.Conv_Ovf_U2_Un => ".checkedConvert 16 false true",
            Code.Conv_Ovf_I4 => ".checkedConvert 32 true false", Code.Conv_Ovf_I4_Un => ".checkedConvert 32 true true",
            Code.Conv_Ovf_U4 => ".checkedConvert 32 false false", Code.Conv_Ovf_U4_Un => ".checkedConvert 32 false true",
            Code.Conv_Ovf_I8 => ".checkedConvert 64 true false", Code.Conv_Ovf_I8_Un => ".checkedConvert 64 true true",
            Code.Conv_Ovf_U8 => ".checkedConvert 64 false false", Code.Conv_Ovf_U8_Un => ".checkedConvert 64 false true",
            Code.Conv_Ovf_I => $".checkedConvert {profile.NativeWidth} true false", Code.Conv_Ovf_I_Un => $".checkedConvert {profile.NativeWidth} true true",
            Code.Conv_Ovf_U => $".checkedConvert {profile.NativeWidth} false false", Code.Conv_Ovf_U_Un => $".checkedConvert {profile.NativeWidth} false true",
            Code.Add_Ovf => ".checkedArithmetic .add true", Code.Add_Ovf_Un => ".checkedArithmetic .add false",
            Code.Sub_Ovf => ".checkedArithmetic .sub true", Code.Sub_Ovf_Un => ".checkedArithmetic .sub false",
            Code.Mul_Ovf => ".checkedArithmetic .mul true", Code.Mul_Ovf_Un => ".checkedArithmetic .mul false",
            Code.Div => ".divide true false", Code.Div_Un => ".divide false false",
            Code.Rem => ".divide true true", Code.Rem_Un => ".divide false true",
            Code.Switch => ".switch [" + string.Join(", ", ((Instruction[])i.Operand).Select(m.Body.Instructions.IndexOf)) + "]",
            Code.Sizeof => $".const32 {TypeWidth((TypeReference)i.Operand, m.Module, profile.Architecture)}",
            Code.Cpobj => $".copyObject {CopyWidth((TypeReference)i.Operand, m.Module, profile.Architecture)}",
            Code.Ldind_I1 => ".loadScalar 1 true", Code.Ldind_U1 => ".loadScalar 1",
            Code.Ldind_I2 => ".loadScalar 2 true", Code.Ldind_U2 => ".loadScalar 2",
            Code.Ldind_I4 or Code.Ldind_U4 => ".loadScalar 4",
            Code.Stind_I1 => ".storeScalar 1", Code.Stind_I2 => ".storeScalar 2", Code.Stind_I4 => ".storeScalar 4",
            Code.Conv_I1 => ".convI1", Code.Conv_I2 => ".convI2", Code.Conv_U2 => ".convU2",
            Code.Neg => ".neg",
            Code.Cgt => ".gt",
            Code.Bgt or Code.Bgt_S => $".bgt {Target()}",
            Code.Ble or Code.Ble_S => $".ble {Target()}",
            Code.Ble_Un or Code.Ble_Un_S => $".bleu {Target()}",
            Code.Ldsfld => $".memory (.staticValue {StaticData.LeanBytes(StaticValues.Resolve((FieldReference)i.Operand, m.Module, profile.Architecture).Bytes)})",
            Code.Stsfld => throw new InvalidDataException($"Unsupported static field store: {i}\n  Static fields are written only by their static constructor, which is never extracted."),
            Code.Ldsflda or Code.Ldtoken when i.Operand is FieldReference => $".memory (.staticAddress {StaticData.LeanBytes(StaticData.Validate((FieldReference)i.Operand, m.Module))})",
            Code.Ldobj when MetadataValidation.IsAggregate((TypeReference)i.Operand, m.Module) => $".loadAggregate {MetadataValidation.Layout((TypeReference)i.Operand, m.Module, profile.Architecture)}",
            Code.Initobj when MetadataValidation.IsAggregate((TypeReference)i.Operand, m.Module) => $".initAggregate {MetadataValidation.Layout((TypeReference)i.Operand, m.Module, profile.Architecture)}",
            Code.Stobj when MetadataValidation.IsAggregate((TypeReference)i.Operand, m.Module) => $".storeAggregate {MetadataValidation.Layout((TypeReference)i.Operand, m.Module, profile.Architecture)}",
            Code.Ldobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector128`1<System.UInt64>" => ".memory .load128",
            Code.Ldobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector256`1<System.UInt64>" => ".memory .load256",
            Code.Ldobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector512`1<System.UInt64>" => ".memory .load512",
            Code.Stobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector512`1<System.UInt64>" => ".memory .store512",
            Code.Initobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector128`1<System.UInt64>" => ".initAggregate 16",
            Code.Initobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector256`1<System.UInt64>" => ".initAggregate 32",
            Code.Initobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector512`1<System.UInt64>" => ".initAggregate 64",
            Code.Stobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector128`1<System.UInt64>" => ".memory .store128",
            Code.Stobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector256`1<System.UInt64>" => ".memory .store256",
            Code.Ldobj => $".loadScalar {MetadataValidation.PrimitiveWidth((TypeReference)i.Operand)}" +
                (EnumTypes.Storage((TypeReference)i.Operand).FullName is "System.SByte" or "System.Int16" ? " true" : ""),
            Code.Stobj => $".storeScalar {MetadataValidation.PrimitiveWidth((TypeReference)i.Operand)}",
            Code.Initobj => $".initAggregate {MetadataValidation.PrimitiveWidth((TypeReference)i.Operand)}",
            Code.Ldarg_0 => Arg(0), Code.Ldarg_1 => Arg(1), Code.Ldarg_2 => Arg(2), Code.Ldarg_3 => Arg(3),
            Code.Ldarg or Code.Ldarg_S => Arg(MethodArguments.Index(m, (ParameterDefinition)i.Operand)),
            Code.Ldloc_0 => LocalOp("local", 0), Code.Ldloc_1 => LocalOp("local", 1), Code.Ldloc_2 => LocalOp("local", 2), Code.Ldloc_3 => LocalOp("local", 3),
            Code.Ldloc or Code.Ldloc_S => LocalOp("local", Local()),
            Code.Ldloca or Code.Ldloca_S => LocalOp("localAddr", Local()),
            Code.Stloc_0 => LocalOp("setLocal", 0), Code.Stloc_1 => LocalOp("setLocal", 1), Code.Stloc_2 => LocalOp("setLocal", 2), Code.Stloc_3 => LocalOp("setLocal", 3),
            Code.Stloc or Code.Stloc_S => LocalOp("setLocal", Local()),
            Code.Ldfld => Field("field"), Code.Ldflda => Field("fieldAddr"), Code.Stfld => Field("setField"),
            Code.Ldc_I4_M1 => ".const32 (BitVec.ofInt 32 (-1))",
            Code.Ldc_I4_0 => ".const32 0", Code.Ldc_I4_1 => ".const32 1",
            Code.Ldc_I4_2 => ".const32 2", Code.Ldc_I4_3 => ".const32 3", Code.Ldc_I4_4 => ".const32 4",
            Code.Ldc_I4_5 => ".const32 5", Code.Ldc_I4_6 => ".const32 6", Code.Ldc_I4_7 => ".const32 7", Code.Ldc_I4_8 => ".const32 8",
            Code.Ldc_I4 or Code.Ldc_I4_S => $".const32 (BitVec.ofInt 32 ({i.Operand}))",
            Code.Ldc_I8 => $".const64 (BitVec.ofInt 64 ({i.Operand}))",
            Code.Conv_I8 => ".convI8", Code.Conv_U => ".convU", Code.Conv_U1 => ".convU1", Code.Add => ".add",
            Code.Conv_U4 => ".convU4", Code.Conv_U8 => ".convU8", Code.Not => ".bnot",
            Code.Sub => ".sub",
            Code.And => ".band", Code.Or => ".bor", Code.Xor => ".bxor", Code.Mul => ".mul",
            Code.Shl => ".shl", Code.Shr => ".shr", Code.Shr_Un => ".shrUn", Code.Conv_I4 => ".convI4",
            Code.Clt => ".lt", Code.Clt_Un => ".ltu", Code.Cgt_Un => ".gtu", Code.Ceq => ".eq",
            Code.Ldind_I8 => ".load64", Code.Stind_I8 => ".store64", Code.Dup => ".dup", Code.Pop => ".pop",
            Code.Br or Code.Br_S => $".branch {Target()}",
            Code.Brfalse or Code.Brfalse_S => $".brzero {Target()}",
            Code.Brtrue or Code.Brtrue_S => $".brnonzero {Target()}",
            Code.Blt_Un or Code.Blt_Un_S => $".bltu {Target()}",
            Code.Bge_Un or Code.Bge_Un_S => $".bgeu {Target()}",
            Code.Bgt_Un or Code.Bgt_Un_S => $".bgtu {Target()}",
            Code.Bge or Code.Bge_S => $".bge {Target()}",
            Code.Blt or Code.Blt_S => $".blt {Target()}",
            Code.Beq or Code.Beq_S => $".beq {Target()}",
            Code.Bne_Un or Code.Bne_Un_S => $".bne {Target()}",
            Code.Ret => ".ret" + Narrow(m.ReturnType),
            _ => throw new InvalidDataException($"Unsupported instruction: {i}")
        };
    }

    static int TypeWidth(TypeReference type, ModuleDefinition module, string architecture) => MetadataValidation.IsAggregate(type, module)
        ? MetadataValidation.Layout(type, module, architecture)
        : MetadataValidation.PrimitiveWidth(type);

    static int CopyWidth(TypeReference type, ModuleDefinition module, string architecture) => type.FullName switch
    {
        "System.Runtime.Intrinsics.Vector128`1<System.UInt64>" => 16,
        "System.Runtime.Intrinsics.Vector256`1<System.UInt64>" => 32,
        "System.Runtime.Intrinsics.Vector512`1<System.UInt64>" => 64,
        _ => TypeWidth(type, module, architecture)
    };
}
