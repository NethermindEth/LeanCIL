using Mono.Cecil;

namespace Nethermind.LeanCIL;

/// <summary>
/// The typed contract imports an extraction names, shared by `extract`, `check` and `blockers` so that
/// each finds the same sidecars and binds them to the same implementations.
/// </summary>
internal sealed class ImportOptions
{
    /// <summary>Sidecars named by `--import`, as full paths.</summary>
    internal List<string> Paths { get; } = [];
    /// <summary>Implementation paths by assembly simple name, from `--import-implementation`.</summary>
    internal Dictionary<string, string> Implementations { get; } = new(StringComparer.Ordinal);
    /// <summary>Expected implementation SHA-256 by assembly simple name, from `--import-sha256`.</summary>
    internal Dictionary<string, string> Sha256 { get; } = new(StringComparer.Ordinal);
    /// <summary>Expected interface digests by assembly simple name, from `--import-interface-sha256`.</summary>
    internal Dictionary<string, string> InterfaceSha256 { get; } = new(StringComparer.Ordinal);

    /// <summary>Whether <paramref name="option"/> is one of the import options this class reads.</summary>
    internal static bool Names(string option) =>
        option is "--import" or "--import-implementation" or "--import-sha256" or "--import-interface-sha256";

    /// <summary>Records one import option and its value; relative paths resolve against <paramref name="directory"/>.</summary>
    internal void Add(string option, string value, string? directory = null)
    {
        if (string.IsNullOrWhiteSpace(value) || value.StartsWith("--", StringComparison.Ordinal))
            throw new ArgumentException(option + " requires a value.");
        if (option == "--import")
        {
            Paths.Add(Path.GetFullPath(value, directory ?? Directory.GetCurrentDirectory()));
            return;
        }
        int separator = value.IndexOf('=');
        if (separator < 1 || separator == value.Length - 1)
            throw new ArgumentException(option + " requires Lib=<value>.");
        Dictionary<string, string> selected = option == "--import-sha256" ? Sha256 :
            option == "--import-interface-sha256" ? InterfaceSha256 : Implementations;
        string named = value[(separator + 1)..];
        if (selected == Implementations) named = Path.GetFullPath(named, directory ?? Directory.GetCurrentDirectory());
        if (!selected.TryAdd(value[..separator], selected == Implementations ? named : named.ToLowerInvariant()))
            throw new ArgumentException("Duplicate " + option + " assembly.");
    }

    /// <summary>
    /// Adds the named sidecars, then, when <paramref name="discover"/> holds, every sidecar beside the assembly
    /// for an unpinned assembly reference. Sources already present are kept as they are.
    /// </summary>
    internal void AddSources(List<ImportResolution.Source> sources, PinnedAssemblies pinned, string assemblyPath,
        ModuleDefinition module, bool discover)
    {
        string assemblyDirectory = Path.GetDirectoryName(Path.GetFullPath(assemblyPath))!;
        foreach (string sidecar in Paths.Distinct(StringComparer.Ordinal))
        {
            if (sources.Any(source => source.SidecarPath == sidecar)) continue;
            ContractInterface contract = ContractInterface.Read(File.ReadAllBytes(sidecar));
            // Rejected before import validation, so a pinned reference never silently loses its contract.
            // The selected assembly is not a reference; importing its own sidecar keeps its usual checks.
            if (pinned.References.Any(reference => reference.Pin.Identity == contract.AssemblyIdentity))
                throw new InvalidDataException(
                    "An assembly cannot be both a typed import and an extracted reference: " +
                    contract.AssemblyIdentity);
            string name = AssemblyNameReference.Parse(contract.AssemblyIdentity).Name;
            string adjacent = Path.Combine(Path.GetDirectoryName(sidecar)!, name + ".dll");
            string implementation = Implementations.GetValueOrDefault(name) ?? (File.Exists(adjacent) ? adjacent :
                Path.Combine(assemblyDirectory, name + ".dll"));
            sources.Add(new(sidecar, Path.GetFullPath(implementation), Sha256.GetValueOrDefault(name) ?? "",
                InterfaceSha256.GetValueOrDefault(name) ?? ""));
        }
        foreach (AssemblyNameReference reference in discover ? module.AssemblyReferences : [])
        {
            if (pinned.References.Any(pin => pin.Module.Assembly.Name.Name == reference.Name)) continue;
            string discovered = Path.Combine(assemblyDirectory, reference.Name + ".leancil.contracts");
            if (File.Exists(discovered) && !sources.Any(source => source.SidecarPath == discovered))
                sources.Add(new(discovered, Path.GetFullPath(Implementations.GetValueOrDefault(reference.Name) ??
                    Path.Combine(Path.GetDirectoryName(discovered)!, reference.Name + ".dll")),
                    Sha256.GetValueOrDefault(reference.Name) ?? "",
                    InterfaceSha256.GetValueOrDefault(reference.Name) ?? "", Discovered: true));
        }
    }

    /// <summary>The options as `extract` arguments, so a confirming extraction sees the same imports.</summary>
    internal IEnumerable<string> Arguments() =>
        Paths.SelectMany(path => new[] { "--import", path })
            .Concat(Implementations.SelectMany(pair => new[] { "--import-implementation", pair.Key + "=" + pair.Value }))
            .Concat(Sha256.SelectMany(pair => new[] { "--import-sha256", pair.Key + "=" + pair.Value }))
            .Concat(InterfaceSha256.SelectMany(pair => new[] { "--import-interface-sha256", pair.Key + "=" + pair.Value }));
}
