using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Track evaluation-stack widths across the admitted control-flow graph. Native values
// share 64-bit storage, but only metadata-proven native/int32 mixtures may widen.
internal static class NativeOperands
{
    internal enum Kind
    {
        Other, Word32, Word64, Native, Reference, NullObject, MethodPointer, MethodTable,
        ArraySigned8, ArrayUnsigned8, ArraySigned16, ArrayUnsigned16, ArraySigned32, ArrayUnsigned32,
        ArraySigned64, ArrayUnsigned64, ArrayNativeInt, ArrayNativeUInt, ArrayBoolean, ArrayCharacter
    }

    internal sealed record Certificate(HashSet<Instruction> Mixed, Dictionary<Instruction, StackType[]> Incoming);

    internal readonly record struct StackType(Kind Kind, string? Metadata = null)
    {
        public static implicit operator StackType(Kind kind) => new(kind);
    }

    static StackType Type(TypeReference type)
    {
        if (ManagedPointers.Signature(type) is { } pointer)
            return CallableType(pointer, type is ArrayType);
        if (Arrays.Of(type) is { } array)
            return type is ArrayType buffer && EnumTypes.IsEnum(buffer.ElementType)
                ? new StackType(array.Kind, $".array {array.Expression}") : array.Kind;
        var reference = type is ByReferenceType;
        var value = reference ? ((ByReferenceType)type).ElementType : type;
        if (Spans.Width(value) is not null && value is GenericInstanceType span &&
            EnumTypes.IsEnum(span.GenericArguments[0]))
        {
            var element = Arrays.Storage(span.GenericArguments[0])!;
            return new(reference ? Kind.Reference : Kind.Other,
                $".enumSpan {element.Expression} {Spans.Writable(value).ToString().ToLowerInvariant()} " +
                reference.ToString().ToLowerInvariant());
        }
        return PrimitiveType(type);
    }

    static StackType CallableType(IMethodSignature signature, bool table = false) =>
        new(table ? Kind.MethodTable : Kind.MethodPointer,
            $".{(table ? "methodTable" : "methodPointer")} {ManagedPointers.SignatureEvidence(signature)}");

    static StackType PrimitiveType(TypeReference type) => type is ByReferenceType or PointerType
        ? Kind.Reference : Arrays.Of(type)?.Kind ?? EnumTypes.Storage(type).MetadataType switch
    {
        MetadataType.IntPtr or MetadataType.UIntPtr => Kind.Native,
        MetadataType.Int64 or MetadataType.UInt64 => Kind.Word64,
        MetadataType.Boolean or MetadataType.Char or MetadataType.SByte or MetadataType.Byte or
            MetadataType.Int16 or MetadataType.UInt16 or MetadataType.Int32 or MetadataType.UInt32 => Kind.Word32,
        _ => Kind.Other
    };

    static TypeReference FieldType(FieldReference field)
    {
        if (!ValueTuples.Is(field.DeclaringType)) return field.FieldType;
        FieldDefinition definition = field.Resolve();
        MetadataValidation.InstanceField? actual = MetadataValidation.Fields(field.DeclaringType)
            .FirstOrDefault(candidate => candidate.Definition == definition);
        return actual?.Type ?? throw new InvalidDataException("Unresolved tuple field: " + field.FullName);
    }

    static bool Binary(Code code) => code is Code.Add or Code.Sub or Code.Mul or Code.Div or Code.Div_Un or
        Code.Rem or Code.Rem_Un or Code.And or Code.Or or Code.Xor or Code.Ceq or Code.Clt or Code.Clt_Un or
        Code.Cgt or Code.Cgt_Un or Code.Add_Ovf or Code.Add_Ovf_Un or Code.Sub_Ovf or Code.Sub_Ovf_Un or
        Code.Mul_Ovf or Code.Mul_Ovf_Un or Code.Beq or Code.Beq_S or Code.Bne_Un or Code.Bne_Un_S or
        Code.Bgt or Code.Bgt_S or Code.Bgt_Un or Code.Bgt_Un_S or Code.Bge or Code.Bge_S or Code.Bge_Un or Code.Bge_Un_S or
        Code.Blt or Code.Blt_S or Code.Blt_Un or Code.Blt_Un_S or Code.Ble or Code.Ble_S or Code.Ble_Un or Code.Ble_Un_S;

    internal static Certificate Certify(MethodDefinition method, IReadOnlySet<Instruction> reachable)
    {
        var incoming = new Dictionary<Instruction, StackType[]> { [method.Body.Instructions[0]] = [] };
        var mixed = new HashSet<Instruction>();
        var pending = new Queue<Instruction>();
        pending.Enqueue(method.Body.Instructions[0]);
        while (pending.TryDequeue(out var instruction))
        {
            if (!reachable.Contains(instruction) || !incoming.TryGetValue(instruction, out var before)) continue;
            var stack = before.ToList();
            StackType Pop()
            {
                if (stack.Count == 0) throw new InvalidDataException("Invalid evaluation stack during native type analysis");
                var result = stack[^1];
                stack.RemoveAt(stack.Count - 1);
                return result;
            }

            var code = instruction.OpCode.Code;
            if (code == Code.Localloc)
            {
                if (stack.Count != 1 || Pop().Kind is not (Kind.Word32 or Kind.Native))
                    throw new InvalidDataException("localloc requires only an int32 or native byte count");
                stack.Add(Kind.Reference);
            }
            else if (code == Code.Add && stack.Count >= 2 && stack[^2] == Kind.Reference &&
                     stack[^1].Kind is Kind.Word32 or Kind.Native)
            {
                Pop();
            }
            else if (code is Code.Cpblk or Code.Initblk)
            {
                var count = Pop();
                var source = Pop();
                var destination = Pop();
                if (count != Kind.Word32 || destination != Kind.Reference ||
                    source != (code == Code.Cpblk ? Kind.Reference : Kind.Word32))
                    throw new InvalidDataException($"Unsupported block memory operand types: {instruction}");
            }
            else if (code is Code.Shl or Code.Shr or Code.Shr_Un)
            {
                var count = Pop();
                var value = Pop();
                if (count.Kind is not (Kind.Word32 or Kind.Native) ||
                    value.Kind is not (Kind.Word32 or Kind.Word64 or Kind.Native))
                    throw new InvalidDataException($"Unsupported shift operand types: {instruction}");
                stack.Add(value);
            }
            else if (Binary(code))
            {
                var right = Pop();
                var left = Pop();
                var referenceOffset = code is Code.Add or Code.Sub && left == Kind.Reference &&
                    right.Kind is Kind.Word32 or Kind.Native;
                var referenceDifference = code == Code.Sub && left == Kind.Reference && right == Kind.Reference;
                var native = !referenceOffset && (left == Kind.Native || right == Kind.Native);
                if (native && (left.Kind is not (Kind.Native or Kind.Word32) || right.Kind is not (Kind.Native or Kind.Word32)))
                    throw new InvalidDataException($"Unsupported native operand mixture: {instruction}");
                if (native && left != right)
                {
                    // CoreCLR widens an int32 constant differently from an argument
                    // here; inlining can change that provenance. Require explicit
                    // conversion instead of encoding a JIT-context-dependent rule.
                    if (code is Code.Bne_Un or Code.Bne_Un_S or Code.Bgt_Un or Code.Bgt_Un_S or
                        Code.Bge_Un or Code.Bge_Un_S or Code.Blt_Un or Code.Blt_Un_S or Code.Ble_Un or Code.Ble_Un_S)
                        throw new InvalidDataException($"Unsupported mixed native/int32 unsigned branch; insert explicit conv.i or conv.u: {instruction}");
                    mixed.Add(instruction);
                }
                if (instruction.OpCode.FlowControl != FlowControl.Cond_Branch)
                    stack.Add(code is Code.Ceq or Code.Clt or Code.Clt_Un or Code.Cgt or Code.Cgt_Un ? Kind.Word32 :
                        referenceOffset ? Kind.Reference : referenceDifference || native ? Kind.Native :
                        left == right ? left : Kind.Other);
            }
            else if (code == Code.Dup)
            {
                var value = Pop();
                stack.Add(value);
                stack.Add(value);
            }
            else if (code == Code.Ldftn)
                stack.Add(CallableType((MethodReference)instruction.Operand));
            else if (code == Code.Calli)
            {
                var signature = (Mono.Cecil.CallSite)instruction.Operand;
                if (Pop() != CallableType(signature))
                    throw new InvalidDataException("Indirect call requires an exact-signature managed pointer");
                for (var index = 0; index < signature.Parameters.Count; index++) Pop();
                if (instruction.Previous?.OpCode.Code == Code.Tail && stack.Count != 0)
                    throw new InvalidDataException("Tail call requires exactly its arguments on the evaluation stack");
                if (signature.ReturnType.MetadataType != MetadataType.Void) stack.Add(Type(signature.ReturnType));
            }
            else if (code == Code.Ldelem_I && stack.Count >= 2 && stack[^2].Kind == Kind.MethodTable)
            {
                if (Pop().Kind is not (Kind.Word32 or Kind.Native))
                    throw new InvalidDataException("Managed table index must be an integer");
                var table = Pop();
                stack.Add(new(Kind.MethodPointer,
                    table.Metadata!.Replace(".methodTable ", ".methodPointer ", StringComparison.Ordinal)));
            }
            else if (code is Code.Call or Code.Callvirt or Code.Newobj)
            {
                var callee = (MethodReference)instruction.Operand;
                for (var index = 0; index < callee.Parameters.Count + (code != Code.Newobj && callee.HasThis ? 1 : 0); index++) Pop();
                if (code == Code.Newobj || callee.ReturnType.MetadataType != MetadataType.Void)
                    stack.Add(code == Code.Newobj ? Type(callee.DeclaringType) : Type(CallReturnType.Resolve(callee)));
            }
            else if (code == Code.Ret)
            {
                var actual = method.ReturnType.MetadataType != MetadataType.Void ? Pop() : Kind.Other;
                if (MethodSpecialization.Source(method) is not null &&
                    (stack.Count != 0 || (method.ReturnType.MetadataType != MetadataType.Void && actual != Type(method.ReturnType))))
                    throw new InvalidDataException($"Unsupported generic return stack type: {method.FullName}");
            }
            else
            {
                var pops = instruction.OpCode.StackBehaviourPop switch
                {
                    StackBehaviour.Pop0 => 0,
                    StackBehaviour.Pop1 or StackBehaviour.Popi or StackBehaviour.Popref => 1,
                    StackBehaviour.Pop1_pop1 or StackBehaviour.Popi_pop1 or StackBehaviour.Popi_popi or
                        StackBehaviour.Popi_popi8 or StackBehaviour.Popi_popr4 or StackBehaviour.Popi_popr8 or
                        StackBehaviour.Popref_pop1 or StackBehaviour.Popref_popi => 2,
                    StackBehaviour.Popi_popi_popi or StackBehaviour.Popref_popi_popi or
                        StackBehaviour.Popref_popi_popi8 or StackBehaviour.Popref_popi_popr4 or
                        StackBehaviour.Popref_popi_popr8 or StackBehaviour.Popref_popi_popref => 3,
                    _ => throw new InvalidDataException($"Unsupported native stack effect: {instruction}")
                };
                var popped = new List<StackType>();
                for (var index = 0; index < pops; index++) popped.Add(Pop());
                var pushes = instruction.OpCode.StackBehaviourPush;
                if (pushes != StackBehaviour.Push0)
                {
                    if (pushes is not (StackBehaviour.Push1 or StackBehaviour.Pushi or StackBehaviour.Pushi8 or
                        StackBehaviour.Pushr4 or StackBehaviour.Pushr8 or StackBehaviour.Pushref))
                        throw new InvalidDataException($"Unsupported native stack effect: {instruction}");
                    StackType result = code switch
                    {
                        Code.Ldarg_0 => Type(MethodArguments.Type(method, 0)),
                        Code.Ldarg_1 => Type(MethodArguments.Type(method, 1)),
                        Code.Ldarg_2 => Type(MethodArguments.Type(method, 2)),
                        Code.Ldarg_3 => Type(MethodArguments.Type(method, 3)),
                        Code.Ldarg or Code.Ldarg_S => Type(MethodArguments.Type(method,
                            MethodArguments.Index(method, (ParameterDefinition)instruction.Operand))),
                        Code.Ldloc or Code.Ldloc_S or Code.Ldloc_0 or Code.Ldloc_1 or Code.Ldloc_2 or Code.Ldloc_3 =>
                            Type(method.Body.Variables[FeatureConstants.Local(instruction)].VariableType),
                        Code.Ldfld or Code.Ldsfld => Type(FieldType((FieldReference)instruction.Operand)),
                        Code.Ldobj or Code.Ldelem_Any => Type((TypeReference)instruction.Operand),
                        Code.Ldloca or Code.Ldloca_S =>
                            Type(new ByReferenceType(method.Body.Variables[
                                FeatureConstants.Local(instruction)].VariableType)),
                        Code.Ldarga or Code.Ldarga_S => Type(new ByReferenceType(MethodArguments.Type(method,
                            MethodArguments.Index(method, (ParameterDefinition)instruction.Operand)))),
                        Code.Ldflda or Code.Ldsflda or Code.Localloc or Code.Ldelema => Kind.Reference,
                        Code.Ldlen or Code.Ldelem_I or Code.Ldind_I or Code.Conv_I or Code.Conv_U or Code.Conv_Ovf_I or Code.Conv_Ovf_I_Un or
                            Code.Conv_Ovf_U or Code.Conv_Ovf_U_Un => Kind.Native,
                        Code.Ldc_I8 or Code.Ldelem_I8 or Code.Ldind_I8 or Code.Conv_I8 or Code.Conv_U8 or Code.Conv_Ovf_I8 or
                            Code.Conv_Ovf_I8_Un or Code.Conv_Ovf_U8 or Code.Conv_Ovf_U8_Un => Kind.Word64,
                        Code.Ldtoken => Kind.Other,
                        Code.Ldnull => Kind.NullObject,
                        Code.Neg or Code.Not => popped[0],
                        // All remaining supported pushi encodings produce int32 (constants,
                        // narrow conversions, sizeof and narrow indirect loads).
                        _ => pushes == StackBehaviour.Pushi ? Kind.Word32 : Kind.Other
                    };
                    stack.Add(result);
                }
            }

            void Successor(Instruction? target)
            {
                if (target is null || !reachable.Contains(target)) return;
                if (incoming.TryGetValue(target, out var previous))
                {
                    if (!previous.SequenceEqual(stack))
                        throw new InvalidDataException($"Incompatible native stack types at {target}");
                }
                else
                {
                    incoming[target] = [.. stack];
                    pending.Enqueue(target);
                }
            }

            if (instruction.Operand is Instruction target) Successor(target);
            if (instruction.Operand is Instruction[] targets)
                foreach (var destination in targets) Successor(destination);
            if (instruction.OpCode.FlowControl is not (FlowControl.Return or FlowControl.Branch or FlowControl.Throw))
                Successor(instruction.Next);
        }
        return new Certificate(mixed, incoming);
    }
}
