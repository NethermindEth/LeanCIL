using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Track evaluation-stack widths across the admitted forward graph. Native values
// share 64-bit storage, but only metadata-proven native/int32 mixtures may widen.
internal static class NativeOperands
{
    enum Kind { Other, Word32, Word64, Native, Reference }

    static Kind Type(TypeReference type) => type is ByReferenceType ? Kind.Reference : EnumTypes.Storage(type).MetadataType switch
    {
        MetadataType.IntPtr or MetadataType.UIntPtr => Kind.Native,
        MetadataType.Int64 or MetadataType.UInt64 => Kind.Word64,
        MetadataType.Boolean or MetadataType.Char or MetadataType.SByte or MetadataType.Byte or
            MetadataType.Int16 or MetadataType.UInt16 or MetadataType.Int32 or MetadataType.UInt32 => Kind.Word32,
        _ => Kind.Other
    };

    static bool Binary(Code code) => code is Code.Add or Code.Sub or Code.Mul or Code.Div or Code.Div_Un or
        Code.Rem or Code.Rem_Un or Code.And or Code.Or or Code.Xor or Code.Ceq or Code.Clt or Code.Clt_Un or
        Code.Cgt or Code.Cgt_Un or Code.Add_Ovf or Code.Add_Ovf_Un or Code.Sub_Ovf or Code.Sub_Ovf_Un or
        Code.Mul_Ovf or Code.Mul_Ovf_Un or Code.Beq or Code.Beq_S or Code.Bne_Un or Code.Bne_Un_S or
        Code.Bgt or Code.Bgt_S or Code.Bgt_Un or Code.Bgt_Un_S or Code.Bge or Code.Bge_S or Code.Bge_Un or Code.Bge_Un_S or
        Code.Blt or Code.Blt_S or Code.Blt_Un or Code.Blt_Un_S or Code.Ble or Code.Ble_S or Code.Ble_Un or Code.Ble_Un_S;

    internal static HashSet<Instruction> Analyze(MethodDefinition method, FeatureProfile profile)
    {
        var reachable = Reachability.Analyze(method, profile);
        var incoming = new Dictionary<Instruction, Kind[]> { [method.Body.Instructions[0]] = [] };
        var mixed = new HashSet<Instruction>();
        foreach (var instruction in method.Body.Instructions)
        {
            if (!reachable.Contains(instruction) || !incoming.TryGetValue(instruction, out var before)) continue;
            var stack = before.ToList();
            Kind Pop()
            {
                if (stack.Count == 0) throw new InvalidDataException("Invalid evaluation stack during native type analysis");
                var result = stack[^1];
                stack.RemoveAt(stack.Count - 1);
                return result;
            }

            var code = instruction.OpCode.Code;
            if (code is Code.Cpblk or Code.Initblk)
            {
                var count = Pop();
                var source = Pop();
                var destination = Pop();
                if (count != Kind.Word32 || destination != Kind.Reference ||
                    source != (code == Code.Cpblk ? Kind.Reference : Kind.Word32))
                    throw new InvalidDataException($"Unsupported block memory operand types: {instruction}");
            }
            else if (Binary(code))
            {
                var right = Pop();
                var left = Pop();
                var native = left == Kind.Native || right == Kind.Native;
                if (native && (left is not (Kind.Native or Kind.Word32) || right is not (Kind.Native or Kind.Word32)))
                    throw new InvalidDataException($"Unsupported native operand mixture: {instruction}");
                if (native && left != right) mixed.Add(instruction);
                if (instruction.OpCode.FlowControl != FlowControl.Cond_Branch)
                    stack.Add(code is Code.Ceq or Code.Clt or Code.Clt_Un or Code.Cgt or Code.Cgt_Un ? Kind.Word32 :
                        native ? Kind.Native : left == right ? left : Kind.Other);
            }
            else if (code == Code.Dup)
            {
                var value = Pop();
                stack.Add(value);
                stack.Add(value);
            }
            else if (code is Code.Call or Code.Newobj)
            {
                var callee = (MethodReference)instruction.Operand;
                for (var index = 0; index < callee.Parameters.Count + (code == Code.Call && callee.HasThis ? 1 : 0); index++) Pop();
                if (code == Code.Newobj || callee.ReturnType.MetadataType != MetadataType.Void)
                    stack.Add(code == Code.Newobj ? Kind.Other : Type(callee.ReturnType));
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
                var popped = new List<Kind>();
                for (var index = 0; index < pops; index++) popped.Add(Pop());
                var pushes = instruction.OpCode.StackBehaviourPush;
                if (pushes != StackBehaviour.Push0)
                {
                    if (pushes is not (StackBehaviour.Push1 or StackBehaviour.Pushi or StackBehaviour.Pushi8 or
                        StackBehaviour.Pushr4 or StackBehaviour.Pushr8 or StackBehaviour.Pushref))
                        throw new InvalidDataException($"Unsupported native stack effect: {instruction}");
                    var result = code switch
                    {
                        Code.Ldarg_0 => Type(MethodArguments.Type(method, 0)),
                        Code.Ldarg_1 => Type(MethodArguments.Type(method, 1)),
                        Code.Ldarg_2 => Type(MethodArguments.Type(method, 2)),
                        Code.Ldarg_3 => Type(MethodArguments.Type(method, 3)),
                        Code.Ldarg or Code.Ldarg_S => Type(MethodArguments.Type(method,
                            MethodArguments.Index(method, (ParameterDefinition)instruction.Operand))),
                        Code.Ldloc or Code.Ldloc_S or Code.Ldloc_0 or Code.Ldloc_1 or Code.Ldloc_2 or Code.Ldloc_3 =>
                            Type(method.Body.Variables[FeatureConstants.Local(instruction)].VariableType),
                        Code.Ldfld or Code.Ldsfld => Type(((FieldReference)instruction.Operand).FieldType),
                        Code.Ldobj => Type((TypeReference)instruction.Operand),
                        Code.Ldloca or Code.Ldloca_S or Code.Ldarga or Code.Ldarga_S or
                            Code.Ldflda or Code.Ldsflda => Kind.Reference,
                        Code.Ldind_I or Code.Conv_I or Code.Conv_U or Code.Conv_Ovf_I or Code.Conv_Ovf_I_Un or
                            Code.Conv_Ovf_U or Code.Conv_Ovf_U_Un => Kind.Native,
                        Code.Ldc_I8 or Code.Ldind_I8 or Code.Conv_I8 or Code.Conv_U8 or Code.Conv_Ovf_I8 or
                            Code.Conv_Ovf_I8_Un or Code.Conv_Ovf_U8 or Code.Conv_Ovf_U8_Un => Kind.Word64,
                        Code.Neg or Code.Not => popped[0],
                        Code.Shl or Code.Shr or Code.Shr_Un => popped[1],
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
                else incoming[target] = [.. stack];
            }

            if (instruction.Operand is Instruction target) Successor(target);
            if (instruction.Operand is Instruction[] targets)
                foreach (var destination in targets) Successor(destination);
            if (instruction.OpCode.FlowControl is not (FlowControl.Return or FlowControl.Branch or FlowControl.Throw))
                Successor(instruction.Next);
        }
        return mixed;
    }
}
