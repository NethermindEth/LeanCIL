using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

/// <summary>The managed targets of reachable raw sites in one extraction.</summary>
internal sealed class ResolvedCallSites
{
    readonly Dictionary<Instruction, MethodDefinition> direct = [];
    readonly Dictionary<Instruction, VirtualDispatch.Entry[]> virtualSlots = [];
    readonly Dictionary<MethodDefinition, string> instanceLinks = [];
    readonly HashSet<Instruction> modelCalls = [];

    internal void Add(Instruction site, MethodDefinition target)
    {
        if (site.OpCode.Code is Code.Call or Code.Callvirt or Code.Newobj or Code.Ldftn)
            direct.Add(site, target);
    }

    internal void AddVirtual(Instruction site, VirtualDispatch.Entry[] targets) => virtualSlots.Add(site, targets);

    internal void AddModel(Instruction site) => modelCalls.Add(site);

    internal bool IsModel(Instruction site) => modelCalls.Contains(site);

    /// <summary>The closed managed target selected for this site and its extraction index.</summary>
    internal (MethodDefinition Method, int Index) Target(Instruction site,
        IReadOnlyDictionary<MethodDefinition, int> indices) =>
        direct.TryGetValue(site, out var target) && indices.TryGetValue(target, out var index)
            ? (target, index) : throw new InvalidDataException($"Unsupported or unresolved call: {site.Operand}");

    /// <summary>The validated receiver cases of a virtual slot, in dispatch order.</summary>
    internal VirtualDispatch.Entry[]? VirtualTargets(Instruction site) => virtualSlots.GetValueOrDefault(site);

    /// <summary>The admitted target kind for this raw call, address or constructor, including its prefixes.</summary>
    internal bool BindsOperand(Instruction site, ImportResolution? imports)
    {
        var code = site.OpCode.Code;
        if (imports?.Slot(site) is not null)
            return code == Code.Call && site.Previous?.OpCode.Code != Code.Constrained && !TailCalls.IsCall(site);
        return code switch
        {
            Code.Call or Code.Callvirt when site.Previous?.OpCode.Code == Code.Constrained => direct.ContainsKey(site),
            Code.Call when TailCalls.IsCall(site) => direct.ContainsKey(site),
            Code.Call or Code.Newobj => direct.ContainsKey(site) || IsModel(site),
            Code.Callvirt => site.Previous?.OpCode.OpCodeType != OpCodeType.Prefix && ObjectTypes.ReceiverCall(site) &&
                (direct.ContainsKey(site) || virtualSlots.ContainsKey(site)),
            Code.Ldftn => direct.ContainsKey(site),
            Code.Calli => site.Operand is CallSite,
            _ => true
        };
    }

    /// <summary>Each occupied pc names its managed targets in program order. Model calls have no link.</summary>
    internal List<(int Pc, string Link)> Links(MethodDefinition method, IReadOnlySet<Instruction> reachable,
        IReadOnlyDictionary<MethodDefinition, int> indices, ImportResolution? imports,
        MetadataValidation.LayoutContext layouts, SortedSet<int>? linkedMethods)
    {
        int Callee(int index)
        {
            linkedMethods?.Add(index);
            return index;
        }

        List<(int, string)> entries = [];
        for (var pc = 0; pc < method.Body.Instructions.Count; pc++)
        {
            var site = method.Body.Instructions[pc];
            if (!reachable.Contains(site)) continue;
            if (imports?.Slot(site) is int slot)
                entries.Add((pc, $".direct {Callee(indices.Count + slot)}"));
            else if (site.OpCode.Code == Code.Calli && site.Operand is CallSite signature)
            {
                var catalog = ManagedPointers.Catalog(signature, indices, indices[method],
                    site.Previous?.OpCode.Code == Code.Tail);
                string Name(int index) => LeanText.MethodNumber(Callee(index));
                var table = string.Join(", ", catalog.Select(target => target.Lean(Name)));
                entries.Add((pc, $".indirect [{table}]"));
            }
            else if (virtualSlots.TryGetValue(site, out var targets))
            {
                var cases = new string[targets.Length];
                for (var position = 0; position < targets.Length; position++)
                {
                    var entry = targets[position];
                    cases[position] = $"({GenericEvidence.ObjectType(entry.Class)}, {Callee(indices[entry.Body])})";
                }
                entries.Add((pc, $".virtual [{string.Join(", ", cases)}]"));
            }
            else if (direct.TryGetValue(site, out var target))
            {
                var index = Callee(indices[target]);
                var link = site.OpCode.Code switch
                {
                    Code.Ldftn => $".address {index}",
                    Code.Newobj when ObjectTypes.Candidate(target.DeclaringType) =>
                        InstanceLink(target, index),
                    Code.Newobj => $".aggregate {index} {layouts.Size(MethodSpecialization.DeclaringType(target))}",
                    _ => $".direct {index}"
                };
                entries.Add((pc, link));
            }
        }
        return entries;
    }

    string InstanceLink(MethodDefinition constructor, int index)
    {
        if (instanceLinks.TryGetValue(constructor, out var link)) return link;
        var allocation = ObjectTypes.AllocationOf(constructor);
        link = $".object {index} {LeanText.ClassList(allocation.Bases)} {allocation.Size}";
        instanceLinks.Add(constructor, link);
        return link;
    }
}
