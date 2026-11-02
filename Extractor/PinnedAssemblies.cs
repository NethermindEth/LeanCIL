using System.Security.Cryptography;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

/// <summary>
/// The assemblies one extraction may read bodies and layouts from: the selected assembly and each
/// <c>--reference</c>, every one pinned by SHA-256. Non-platform references resolve only here; the
/// shared runtime is resolved from the extractor's own platform assemblies.
/// </summary>
internal sealed class PinnedAssemblies : IAssemblyResolver
{
    /// <summary>A path-independent assembly pin, recorded in the manifest and the certificate.</summary>
    internal sealed record Pin(string Identity, Guid Mvid, string Sha256);

    /// <summary>A referenced assembly on disk with the hash it must still have, if one was recorded.</summary>
    internal sealed record Source(string Path, string? ExpectedSha256 = null);

    // Platform keys: only the extractor's trusted platform assemblies can answer these names.
    static readonly string[] PlatformKeyTokens =
        ["b03f5f7f11d50a3a", "cc7b13ffcd2ddd51", "7cec85d7bea7798e", "b77a5c561934e089"];

    [ThreadStatic]
    static PinnedAssemblies? active;

    readonly PinnedAssemblies? previous;
    readonly DefaultAssemblyResolver platform = new();
    readonly Dictionary<string, ModuleDefinition> modules = new(StringComparer.Ordinal);
    readonly Dictionary<ModuleDefinition, ModuleDefinition> originals = [];
    readonly List<(Pin Pin, string Path, ModuleDefinition Module)> references = [];

    internal ModuleDefinition Selected { get; }

    internal Pin SelectedPin { get; }

    /// <summary>The referenced pins in command-line order; the selected assembly is not included.</summary>
    internal IReadOnlyList<(Pin Pin, string Path, ModuleDefinition Module)> References => references;

    /// <summary>Every pin, the selected assembly first; certificate assembly indices refer to this order.</summary>
    internal IEnumerable<Pin> Pins => [SelectedPin, .. references.Select(reference => reference.Pin)];

    internal PinnedAssemblies(byte[] selected, string selectedHash, IEnumerable<Source> sources)
    {
        previous = active;
        // Only the runtime's trusted platform list may answer; no directory is searched.
        foreach (string directory in platform.GetSearchDirectories()) platform.RemoveSearchDirectory(directory);
        Selected = Read(selected);
        SelectedPin = new(Selected.Assembly.Name.FullName, Selected.Mvid, selectedHash);
        modules.Add(SelectedPin.Identity, Selected);
        originals.Add(Selected, StaticData.ReadModule(selected, this));
        foreach (Source source in sources)
        {
            byte[] bytes = File.ReadAllBytes(source.Path);
            string hash = Convert.ToHexStringLower(SHA256.HashData(bytes));
            if (source.ExpectedSha256 is { } expected && !string.Equals(expected, hash, StringComparison.Ordinal))
                throw new InvalidDataException($"Referenced assembly hash mismatch: {CliPaths.Display(source.Path)}\n" +
                    $"  Expected SHA-256: {expected}\n  Actual SHA-256: {hash}");
            ModuleDefinition module = Read(bytes);
            string identity = module.Assembly?.Name.FullName ??
                throw new InvalidDataException(
                    "Referenced module has no assembly metadata: " + CliPaths.Display(source.Path));
            if (Platform(module.Assembly.Name))
                throw new InvalidDataException("Platform assemblies are runtime models, not references: " + identity);
            if (!modules.TryAdd(identity, module))
                throw new InvalidDataException("Duplicate pinned assembly identity: " + identity);
            originals.Add(module, StaticData.ReadModule(bytes, this));
            references.Add((new(identity, module.Mvid, hash), Path.GetFullPath(source.Path), module));
        }
        active = this;
    }

    ModuleDefinition Read(byte[] bytes) => StaticData.ReadModule(bytes, this);

    /// <summary>The pinned set of the current extraction, or none outside one.</summary>
    internal static PinnedAssemblies? Active => active;

    static bool Platform(AssemblyNameReference name) => name.PublicKeyToken is { Length: 8 } token &&
        PlatformKeyTokens.Contains(Convert.ToHexStringLower(token));

    /// <summary>Whether <paramref name="module"/> is one of the pinned modules.</summary>
    internal bool Contains(ModuleDefinition module) =>
        modules.TryGetValue(module.Assembly.Name.FullName, out var pinned) && pinned == module;

    /// <summary>The pinned module a type's scope names, if any.</summary>
    internal ModuleDefinition? ModuleOf(TypeReference type) => type.Scope switch
    {
        ModuleDefinition module when Contains(module) => module,
        AssemblyNameReference name when modules.TryGetValue(name.FullName, out var module) => module,
        _ => null
    };

    /// <summary>Whether <paramref name="type"/> is declared, not merely referenced, by a pinned
    /// module of the active extraction, or by <paramref name="module"/> itself.</summary>
    internal static bool Declares(TypeReference type, ModuleDefinition module) =>
        type.Scope == module || active?.ModuleOf(type) is not null;

    /// <summary>The untouched copy of a pinned module; extraction rewrites call operands in the
    /// working one. An untouched copy maps to itself.</summary>
    internal ModuleDefinition Original(ModuleDefinition module) => originals.TryGetValue(module, out var original)
        ? original : originals.ContainsValue(module) ? module : throw Outside(module);

    static InvalidDataException Outside(ModuleDefinition module) =>
        new("Method body outside the pinned assemblies: " + module.Assembly.Name.FullName);

    /// <summary>The index of a pinned module in <see cref="Pins"/>.</summary>
    internal int Index(ModuleDefinition module) => module == Selected ? 0 :
        references.FindIndex(reference => reference.Module == module) is >= 0 and var index ? index + 1 :
            throw Outside(module);

    /// <summary>Rejects a reference whose simple name is pinned under another identity, so a version
    /// mismatch never falls back to the typed-import path.</summary>
    internal void RejectMismatch(AssemblyNameReference name)
    {
        if (!modules.ContainsKey(name.FullName) && modules.Values.Any(pinned => pinned.Assembly.Name.Name == name.Name))
            Resolve(name);
    }

    public AssemblyDefinition Resolve(AssemblyNameReference name) => Resolve(name, new ReaderParameters());

    public AssemblyDefinition Resolve(AssemblyNameReference name, ReaderParameters parameters)
    {
        if (modules.TryGetValue(name.FullName, out var module)) return module.Assembly;
        if (Platform(name)) return platform.Resolve(name, parameters);
        var named = modules.Values.FirstOrDefault(candidate => candidate.Assembly.Name.Name == name.Name);
        throw new InvalidDataException(named is null
            ? $"Unpinned assembly reference: {name.FullName}\n" +
                $"  Pass --reference <path to {name.Name}.dll> to extract from it."
            : $"Pinned assembly does not match its reference: {name.FullName}\n" +
                $"  Pinned: {named.Assembly.Name.FullName}");
    }

    public void Dispose()
    {
        active = previous;
        platform.Dispose();
        foreach (ModuleDefinition module in modules.Values.Concat(originals.Values)) module.Dispose();
    }
}
