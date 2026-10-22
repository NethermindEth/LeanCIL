namespace Nethermind.LeanCIL;

internal static class ContractDependencyGraph
{
    internal static void Validate(IEnumerable<ContractInterface> interfaces)
    {
        Dictionary<string, ContractInterface> nodes = new(StringComparer.Ordinal);
        foreach (ContractInterface contract in interfaces)
        {
            if (nodes.TryGetValue(contract.AssemblyIdentity, out ContractInterface? existing))
            {
                if (existing.ImplementationSha256 != contract.ImplementationSha256)
                    throw new InvalidDataException("Conflicting contract dependency implementation hashes: " + contract.AssemblyIdentity);
                if (existing.InterfaceDigest != contract.InterfaceDigest)
                    throw new InvalidDataException("Conflicting contract dependency interface digests: " + contract.AssemblyIdentity);
            }
            else nodes.Add(contract.AssemblyIdentity, contract);
        }
        foreach (ContractInterface contract in nodes.Values)
            foreach (ContractDependency dependency in contract.Dependencies)
                if (!nodes.ContainsKey(dependency.AssemblyIdentity))
                    throw new InvalidDataException("Missing independently pinned contract dependency: " + contract.AssemblyIdentity +
                        " required by " + contract.AssemblyIdentity);
        Dictionary<string, int> state = new(StringComparer.Ordinal);
        foreach (string identity in nodes.Keys.Order(StringComparer.Ordinal))
        {
            if (state.GetValueOrDefault(identity) != 0) continue;
            Stack<(string Identity, int Next)> pending = new();
            List<string> path = [identity];
            state[identity] = 1;
            pending.Push((identity, 0));
            while (pending.TryPop(out (string Identity, int Next) frame))
            {
                ContractDependency[] dependencies = nodes[frame.Identity].Dependencies;
                if (frame.Next == dependencies.Length)
                {
                    state[frame.Identity] = 2;
                    path.RemoveAt(path.Count - 1);
                    continue;
                }
                pending.Push((frame.Identity, frame.Next + 1));
                string child = dependencies[frame.Next].AssemblyIdentity;
                if (state.GetValueOrDefault(child) == 1)
                    throw new InvalidDataException("Contract dependency cycle: " +
                        string.Join(" -> ", path.Skip(path.IndexOf(child)).Append(child)));
                if (state.GetValueOrDefault(child) != 0) continue;
                state[child] = 1;
                path.Add(child);
                pending.Push((child, 0));
            }
        }
        foreach (ContractInterface contract in nodes.Values)
            foreach (ContractDependency dependency in contract.Dependencies)
            {
                ContractInterface selected = nodes[dependency.AssemblyIdentity];
                if (selected.ImplementationSha256 != dependency.ImplementationSha256)
                    throw new InvalidDataException("Contract dependency implementation hash mismatch: " + dependency.AssemblyIdentity +
                        "; required " + dependency.ImplementationSha256 + ", actual " + selected.ImplementationSha256);
                if (selected.InterfaceDigest != dependency.InterfaceDigest)
                    throw new InvalidDataException("Contract dependency interface digest mismatch: " + dependency.AssemblyIdentity);
            }
    }
}
