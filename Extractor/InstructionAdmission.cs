using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

/// <summary>The operand and target checks for each live instruction in a method's admitted call graph.</summary>
internal sealed class InstructionAdmission(MethodDefinition method, FeatureProfile profile,
    IReadOnlyDictionary<MethodDefinition, int> methods, ConstrainedCalls.TargetIndex constrainedTargets,
    MetadataValidation.LayoutContext layouts, ImportResolution? imports, NativeOperands.Certificate native,
    IReadOnlyDictionary<int, int> homes)
{
    readonly InstructionIndex instructions = new(method);

    internal void Check(Instruction site)
    {
        InstructionPrefixes.ValidatePrefix(method, site);
        if (site.Previous is { } previous) InstructionPrefixes.ValidatePrefix(method, previous);
        if (imports?.Slot(site) is not null) return;
        layouts.Require(method.Module, profile.Architecture);
        var code = site.OpCode.Code;
        if (code == Code.Calli && site.Operand is CallSite signature)
        {
            ManagedPointers.Catalog(signature, methods, methods[method], site.Previous?.OpCode.Code == Code.Tail);
            return;
        }
        if (code == Code.Ldftn && site.Operand is MethodReference address)
        {
            var (target, index) = InstructionOperands.AddressTarget(address, methods);
            ManagedPointers.Target(target, index);
            ManagedPointers.SignatureEvidence(target);
            return;
        }
        InstructionOperands.ValidateTailStack(site, native);
        if (CheckArray(site)) return;
        var typeTests = TypeTests.Analyze(method);
        if (code == Code.Tail)
        {
            TailCalls.ValidateReachable(method, site, profile.Architecture);
            return;
        }
        if (typeTests.Results.ContainsKey(site) || typeTests.Operands.Contains(site)) return;
        var throws = Throws.Analyze(method);
        if (code == Code.Constrained)
        {
            var next = site.Next ?? throw new InvalidDataException("Constrained prefix has no call");
            ConstrainedCalls.Resolve(method, next, instructions, profile.Architecture);
            return;
        }
        if (!ObjectTypes.ReceiverCall(site) &&
            (code == Code.Callvirt || code == Code.Call && site.Previous?.OpCode.Code == Code.Constrained))
        {
            InstructionOperands.ConstrainedTarget(method, site, instructions, profile, constrainedTargets, methods);
            return;
        }
        if (throws.Raises.ContainsKey(site)) return;
        if (throws.Operands.Contains(site)) return;
        switch (code)
        {
            case Code.Call or Code.Callvirt or Code.Newobj:
                CheckCall(site);
                return;
            case Code.Ldobj or Code.Stobj or Code.Initobj or Code.Sizeof or Code.Cpobj
                when site.Operand is TypeReference operand:
                InstructionOperands.ObjectStorage(method, site, operand, instructions, layouts, profile);
                return;
            case Code.Castclass or Code.Isinst:
                ObjectTypes.ValidateTestOperand(site);
                return;
            case Code.Ldfld or Code.Stfld or Code.Ldflda:
                CheckField(site);
                return;
            case Code.Ldsfld when FeatureProfile.PlatformField((FieldReference)site.Operand) is not null:
                return;
            case Code.Ldsfld or Code.Ldsflda or Code.Ldtoken when site.Operand is FieldReference:
                StaticData.FieldOf(site, method.Module, profile.Architecture);
                return;
            case Code.Stsfld:
                throw new InvalidDataException($"""
                    Unsupported static field store: {site}
                      Static fields are written only by their static constructor, which is never extracted.
                    """.ReplaceLineEndings("\n"));
            case Code.Throw:
                return;
            case Code.Ldstr:
                InstructionOperands.ValidateLiteral((string)site.Operand);
                return;
            case Code.Starg or Code.Starg_S or Code.Ldarga or Code.Ldarga_S:
                InstructionOperands.ArgumentHomeSlot(method, site, homes);
                return;
            case Code.Ldarg or Code.Ldarg_S:
                MethodArguments.Index(method, (ParameterDefinition)site.Operand);
                return;
            case Code.Ldloca or Code.Ldloca_S:
                InstructionOperands.AddressedLocal(method, site);
                return;
            case Code.Ldloc or Code.Ldloc_S or Code.Stloc or Code.Stloc_S:
                _ = ((VariableDefinition)site.Operand).Index;
                return;
            case Code.Switch:
                foreach (var target in (Instruction[])site.Operand) instructions.Position(target);
                return;
            case Code.Ldc_I4 or Code.Ldc_I4_S:
                Convert.ToInt64(site.Operand);
                return;
            case Code.Ldc_I8:
                _ = (long)site.Operand;
                return;
            case Code.Cpblk or Code.Initblk:
                MemoryPrefixes.BlockAlignment(site);
                return;
            case Code.Unaligned:
                return;
            default:
                if (GenericEvidence.SimpleOpcodes.Contains(code))
                {
                    if (site.OpCode.OperandType is OperandType.InlineBrTarget or OperandType.ShortInlineBrTarget)
                        instructions.Position((Instruction)site.Operand);
                    return;
                }
                break;
        }
        throw new InvalidDataException($"Unsupported instruction: {site}");
    }

    void CheckField(Instruction site)
    {
        var operand = (FieldReference)site.Operand;
        var field = operand.Resolve() ?? throw new InvalidDataException("Unresolved field");
        var code = site.OpCode.Code;
        if (ObjectTypes.Candidate(operand.DeclaringType))
            ObjectTypes.FieldOperation(operand, field, code == Code.Stfld, code == Code.Ldflda, profile.Architecture);
        else
            InstructionOperands.StructField(operand, field, code, method, profile, layouts);
    }

    bool CheckArray(Instruction site)
    {
        switch (site.OpCode.Code)
        {
            case Code.Newarr:
                var element = (TypeReference)site.Operand;
                if (ReferenceArrays.Element(element))
                {
                    LayoutEvidence.Scope(element);
                    return true;
                }
                return Arrays.Storage(element, profile.Architecture) is { Width: > 0 and <= ushort.MaxValue };
            case Code.Ldelem_Any when InstructionOperands.MethodTableLoad(site, native):
                return true;
            case Code.Ldelema or Code.Ldelem_Any or Code.Stelem_Any:
                Arrays.ElementStorage(site, profile.Architecture);
                return true;
            case Code.Ldlen or Code.Ldelem_Ref or Code.Stelem_Ref or
                Code.Ldelem_I1 or Code.Ldelem_U1 or Code.Ldelem_I2 or Code.Ldelem_U2 or
                Code.Ldelem_I4 or Code.Ldelem_U4 or Code.Ldelem_I8 or Code.Ldelem_I or
                Code.Stelem_I1 or Code.Stelem_I2 or Code.Stelem_I4 or Code.Stelem_I8 or Code.Stelem_I:
                return true;
            default:
                return false;
        }
    }

    void CheckCall(Instruction site)
    {
        var code = site.OpCode.Code;
        var reference = (MethodReference)site.Operand;
        if (VirtualDispatch.Is(site))
        {
            foreach (var entry in VirtualDispatch.Table(reference))
                InstructionOperands.ValidateVirtualTarget(entry, methods, methods[method]);
            return;
        }
        if (code == Code.Call && RuntimeModels.CallModel(reference, profile) ||
            code == Code.Newobj && Spans.ConstructorOperation(reference, profile.Architecture)) return;
        RuntimeModels.ValidateCallScope(reference);
        var (target, _) = InstructionOperands.DirectTarget(reference, TailCalls.IsCall(site),
            methods[method], methods);
        if (code != Code.Newobj) return;
        if (ObjectTypes.Candidate(target.DeclaringType)) ObjectTypes.AllocationOf(target);
        else layouts.Size(MethodSpecialization.DeclaringType(target));
    }
}
