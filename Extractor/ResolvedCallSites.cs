using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

/// <summary>The managed targets of reachable raw sites in one extraction.</summary>
internal sealed class ResolvedCallSites
{
    readonly Dictionary<Instruction, MethodDefinition> direct = [];
    readonly Dictionary<Instruction, VirtualDispatch.Entry[]> virtualSlots = [];
    readonly Dictionary<MethodDefinition, string> instanceLinks = [];

    internal void Add(Instruction site, MethodDefinition target)
    {
        if (site.OpCode.Code is Code.Call or Code.Callvirt or Code.Newobj or Code.Ldftn)
            direct.Add(site, target);
    }

    internal void AddVirtual(Instruction site, VirtualDispatch.Entry[] targets) => virtualSlots.Add(site, targets);

    /// <summary>Each occupied pc names its managed targets in program order. Model calls have no link.</summary>
    internal List<(int Pc, string Link)> Links(MethodDefinition method, IReadOnlySet<Instruction> reachable,
        IReadOnlyDictionary<MethodDefinition, int> indices, ImportResolution? imports,
        MetadataValidation.LayoutContext layouts)
    {
        List<(int, string)> entries = [];
        for (var pc = 0; pc < method.Body.Instructions.Count; pc++)
        {
            var site = method.Body.Instructions[pc];
            if (!reachable.Contains(site)) continue;
            if (imports?.Slot(site) is int slot)
                entries.Add((pc, $".direct {indices.Count + slot}"));
            else if (site.OpCode.Code == Code.Calli && site.Operand is CallSite signature)
            {
                var catalog = ManagedPointers.Catalog(signature, indices, indices[method],
                    site.Previous?.OpCode.Code == Code.Tail);
                var table = string.Join(", ", catalog.Select(target => target.Lean(LeanText.MethodNumber)));
                entries.Add((pc, $".indirect [{table}]"));
            }
            else if (virtualSlots.TryGetValue(site, out var targets))
            {
                var cases = new string[targets.Length];
                for (var position = 0; position < targets.Length; position++)
                {
                    var entry = targets[position];
                    cases[position] = $"({GenericEvidence.ObjectType(entry.Class)}, {indices[entry.Body]})";
                }
                entries.Add((pc, $".virtual [{string.Join(", ", cases)}]"));
            }
            else if (direct.TryGetValue(site, out var target))
            {
                var index = indices[target];
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
