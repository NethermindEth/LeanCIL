using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Runtime.InteropServices;
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

    /// <summary>An immutable assembly row, decoded once when resolution first requests it.</summary>
    sealed class IdentityRow(MetadataImage image, uint token)
    {
        AssemblyName? identity;

        internal AssemblyName Read()
        {
            if (identity is not null) return identity;
            bool definition = token == 0x20000001;
            uint flags = definition ? (uint)image.Reader.GetAssemblyDefinition().Flags :
                (uint)image.Reader.GetAssemblyReference(
                    MetadataTokens.AssemblyReferenceHandle((int)(token & 0xffffff))).Flags;
            uint allowed = definition ? 0xc001u : 0x0001u;
            if ((flags & ~allowed) != 0)
                throw new InvalidDataException("Unsupported assembly identity flags in image row");
            return identity = image.AssemblyIdentity(token) ??
                throw new InvalidDataException("Invalid assembly identity in image row");
        }
    }

    [ThreadStatic]
    static PinnedAssemblies? active;

    readonly PinnedAssemblies? previous;
    readonly Dictionary<AssemblyName, ModuleDefinition> modules = [];
    // One platform assembly per identity, so two references to one platform type resolve to one definition.
    readonly Dictionary<AssemblyName, AssemblyDefinition> platformAssemblies = [];
    readonly Dictionary<MetadataName, AssemblyDefinition> platformByName = [];
    readonly Dictionary<MetadataName, string> platformPaths = PlatformPaths();
    readonly Dictionary<AssemblyNameReference, IdentityRow> identityRows = new(ReferenceEqualityComparer.Instance);
    readonly Dictionary<MetadataImage, Dictionary<uint, IdentityRow>> rowsByImage = [];
    sealed record Registration(AssemblyNameReference[] Names, StructuralSignatures.Primitive[] Primitives);
    readonly Dictionary<ModuleDefinition, Registration> registrations = [];
    readonly Dictionary<ModuleDefinition, MemoryStream> ownedModules = [];
    bool disposed;
    readonly Dictionary<ModuleDefinition, ModuleDefinition> originals = [];
    readonly Dictionary<ModuleDefinition, ModuleDefinition> working = [];
    readonly Dictionary<ModuleDefinition, int> indices = [];
    readonly Dictionary<TypeDefinition, TypeDefinition[]> dispatchHierarchies = [];
    readonly Dictionary<MetadataName, ModuleDefinition> byName = [];
    readonly Dictionary<ModuleDefinition, byte[]> images = [];
    readonly Dictionary<byte[], PEReader> readers = [];
    readonly Dictionary<PEReader, MetadataImage> metadata = [];
    readonly Dictionary<ModuleDefinition, (PEReader Reader, MetadataImage Metadata)> identityImages = [];
    readonly List<(Pin Pin, string Path, ModuleDefinition Module)> references = [];

    internal ModuleDefinition Selected { get; }

    internal StructuralSignatures Signatures { get; }

    internal Pin SelectedPin { get; }

    /// <summary>The referenced pins in command-line order; the selected assembly is not included.</summary>
    internal IReadOnlyList<(Pin Pin, string Path, ModuleDefinition Module)> References => references;

    /// <summary>Every pin, the selected assembly first; certificate assembly indices refer to this order.</summary>
    internal IEnumerable<Pin> Pins => [SelectedPin, .. references.Select(reference => reference.Pin)];

    /// <summary>Every pinned module, the selected assembly first, in the order of <see cref="Pins"/>.</summary>
    internal IEnumerable<ModuleDefinition> Modules => [Selected, .. references.Select(reference => reference.Module)];

    /// <summary>Classes deriving from the slot's declarer across this fixed set of pinned images.</summary>
    internal TypeDefinition[] DispatchHierarchy(TypeDefinition declaring)
    {
        if (!dispatchHierarchies.TryGetValue(declaring, out var classes))
            dispatchHierarchies.Add(declaring, classes = VirtualDispatch.DerivedClasses(Modules, declaring).ToArray());
        return classes;
    }

    /// <summary>Pins <paramref name="selected"/> and each source; <paramref name="readReference"/> reads a
    /// referenced assembly's bytes and hash, so a batch of extractions reads each reference once.</summary>
    internal PinnedAssemblies(byte[] selected, string selectedHash, IEnumerable<Source> sources,
        Func<string, Program.ExtractionBatch.AssemblySnapshot>? readReference = null)
        : this(new Program.ExtractionBatch.AssemblySnapshot(selected, selectedHash), sources, readReference) { }

    /// <summary>A batch shares each immutable image's signature check across extraction requests.</summary>
    internal PinnedAssemblies(Program.ExtractionBatch.AssemblySnapshot snapshot, IEnumerable<Source> sources,
        Func<string, Program.ExtractionBatch.AssemblySnapshot>? readReference)
    {
        Signatures = new(this);
        previous = active;
        try
        {
            snapshot.ValidateSignatures();
            byte[] selected = snapshot.Bytes;
            Selected = ReadPin(selected);
            SelectedPin = new(Selected.Assembly.Name.FullName, Selected.Mvid, snapshot.Hash);
            AssemblyName selectedIdentity = IdentityOf(Selected.Assembly.Name);
            modules.Add(selectedIdentity, Selected);
            byName.TryAdd(selectedIdentity.Name, Selected);
            AddOriginal(Selected, selected);
            foreach (Source source in sources)
            {
                var image = readReference?.Invoke(source.Path);
                byte[] bytes = image?.Bytes ?? File.ReadAllBytes(source.Path);
                string hash = image?.Hash ?? Convert.ToHexStringLower(SHA256.HashData(bytes));
                if (source.ExpectedSha256 is { } expected && !string.Equals(expected, hash, StringComparison.Ordinal))
                    throw new InvalidDataException(
                        $"Referenced assembly hash mismatch: {CliPaths.Display(source.Path)}\n" +
                        $"  Expected SHA-256: {expected}\n  Actual SHA-256: {hash}");
                if (image is null) PlatformSignatures.Validate(bytes);
                else image.ValidateSignatures();
                ModuleDefinition module = ReadPin(bytes);
                string identity = module.Assembly.Name.FullName;
                AssemblyName key = IdentityOf(module.Assembly.Name);
                if (Platform(key))
                    throw new InvalidDataException(
                        "Platform assemblies are runtime models, not references: " + identity);
                if (!modules.TryAdd(key, module))
                    throw new InvalidDataException("Duplicate pinned assembly identity: " + identity);
                byName.TryAdd(key.Name, module);
                AddOriginal(module, bytes);
                references.Add((new(identity, module.Mvid, hash), Path.GetFullPath(source.Path), module));
            }
            active = this;
        }
        catch { Dispose(); throw; }
    }

    ModuleDefinition Read(byte[] bytes)
    {
        MemoryStream? stream = null;
        ModuleDefinition? module = null;
        try
        {
            module = StaticData.ReadModule(bytes, this, retained => stream = retained);
            ownedModules.Add(module, stream!);
            return module;
        }
        catch { module?.Dispose(); stream?.Dispose(); throw; }
    }

    ModuleDefinition ReadPin(byte[] bytes)
    {
        ModuleDefinition module = Read(bytes);
        images.Add(module, bytes);
        RegisterRows(module, Metadata(module));
        return module;
    }

    // The working module and its untouched copy are two readings of the same image.
    void AddOriginal(ModuleDefinition module, byte[] image)
    {
        ModuleDefinition original = ReadPin(image);
        originals.Add(module, original);
        working.Add(original, module);
        indices.Add(module, indices.Count);
    }

    /// <summary>The pinned set of the current extraction, or none outside one.</summary>
    internal static PinnedAssemblies? Active => active;

    // Platform keys: only the extractor's trusted platform assemblies can answer these names.
    static bool Platform(AssemblyName name) => name.PublicKeyToken is { } token &&
        PlatformAssemblies.KeyTokens.Contains(token);

    /// <summary>Whether <paramref name="module"/> is one of the pinned modules.</summary>
    internal bool Contains(ModuleDefinition module) => indices.ContainsKey(module);

    /// <summary>The pinned module a type's scope names, if any.</summary>
    internal ModuleDefinition? ModuleOf(TypeReference type) => type.Scope switch
    {
        ModuleDefinition module when Contains(module) => module,
        AssemblyNameReference name when modules.TryGetValue(IdentityOf(name), out var module) => module,
        _ => null
    };

    /// <summary>Whether <paramref name="type"/> is declared, not merely referenced, by a pinned
    /// module of the active extraction, or by <paramref name="module"/> itself.</summary>
    internal static bool Declares(TypeReference type, ModuleDefinition module) =>
        type.Scope == module || active?.ModuleOf(type) is not null;

    /// <summary>The untouched copy of a pinned module; extraction rewrites call operands in the
    /// working one. An untouched copy maps to itself.</summary>
    internal ModuleDefinition Original(ModuleDefinition module) => originals.TryGetValue(module, out var original)
        ? original : working.ContainsKey(module) ? module : throw Outside(module);

    static InvalidDataException Outside(ModuleDefinition module) =>
        new("Method body outside the pinned assemblies: " + module.Assembly.Name.FullName);

    /// <summary>The header and code bytes of a method's body, read from the image of its module.</summary>
    internal MethodBodyBytes.Body Body(MethodDefinition method)
    {
        if (!method.HasBody || method.RVA == 0)
            throw new InvalidDataException("Method has no body in its image: " + method.FullName);
        return MethodBodyBytes.Read(Image(method.Module), (int)method.RVA);
    }

    PEReader Image(ModuleDefinition module)
    {
        if (!images.TryGetValue(module, out byte[]? image)) throw Outside(module);
        if (!readers.TryGetValue(image, out PEReader? reader))
            readers.Add(image, reader = new(ImmutableCollectionsMarshal.AsImmutableArray(image)));
        return reader;
    }

    /// <summary>The metadata tables and heaps of a pinned module's image, read once per image.</summary>
    internal MetadataImage Metadata(ModuleDefinition module)
    {
        var reader = Image(module);
        if (!metadata.TryGetValue(reader, out MetadataImage? image)) metadata.Add(reader, image = new(reader));
        return image;
    }

    /// <summary>Retains verified import metadata without admitting its bodies or resolution scope.</summary>
    internal void RegisterIdentityImage(ModuleDefinition module, byte[] bytes)
    {
        var reader = new PEReader(ImmutableCollectionsMarshal.AsImmutableArray(bytes));
        MetadataImage? image = null;
        bool registered = false;
        try
        {
            image = new MetadataImage(reader);
            RegisterRows(module, image);
            registered = true;
            identityImages.Add(module, (reader, image));
        }
        catch
        {
            if (registered) UnregisterRows(module);
            if (image is not null) rowsByImage.Remove(image);
            reader.Dispose();
            throw;
        }
    }

    /// <summary>Releases an import's metadata when its owning resolution ends.</summary>
    internal void UnregisterIdentityImage(ModuleDefinition module)
    {
        if (identityImages.Remove(module, out var image))
        {
            UnregisterRows(module);
            rowsByImage.Remove(image.Metadata);
            image.Reader.Dispose();
        }
    }

    /// <summary>The raw identity rows of an executable pin or a verified contract import.</summary>
    internal MetadataImage IdentityMetadata(ModuleDefinition module) =>
        RegisteredMetadata(module);

    internal void RequireRegistered(ModuleDefinition module)
    {
        if (disposed || !registrations.ContainsKey(module))
            throw new InvalidDataException("Module identity is not registered in this session");
    }

    MetadataImage RegisteredMetadata(ModuleDefinition module)
    {
        RequireRegistered(module);
        return identityImages.TryGetValue(module, out var image) ? image.Metadata : Metadata(module);
    }

    /// <summary>
    /// The working module that <paramref name="module"/> is the untouched copy of, or the module itself.
    /// </summary>
    internal ModuleDefinition Working(ModuleDefinition module) =>
        working.GetValueOrDefault(module, module);
    /// <summary>The index of a pinned module in <see cref="Pins"/>.</summary>
    internal int Index(ModuleDefinition module) => indices.TryGetValue(module, out var index)
        ? index : throw Outside(module);

    /// <summary>Rejects a reference whose simple name is pinned under another identity, so a version
    /// mismatch never falls back to the typed-import path.</summary>
    internal void RejectMismatch(AssemblyNameReference name)
    {
        AssemblyName identity = IdentityOf(name);
        if (!modules.ContainsKey(identity) && byName.ContainsKey(identity.Name))
            Resolve(name);
    }

    /// <summary>Whether <paramref name="name"/> resolves to a platform assembly and no pinned assembly has its simple
    /// name, which Lean reads from a carried slice or refuses, never as a platform type.</summary>
    internal bool IsPlatform(AssemblyNameReference name)
    {
        AssemblyName identity = IdentityOf(name);
        return Platform(identity) && !byName.ContainsKey(identity.Name);
    }

    /// <summary>Whether <see cref="Resolve(AssemblyNameReference)"/> answers the reference rather than rejecting it.
    /// </summary>
    internal bool Resolves(AssemblyNameReference name)
    {
        AssemblyName identity = IdentityOf(name);
        return modules.ContainsKey(identity) || Platform(identity);
    }

    public AssemblyDefinition Resolve(AssemblyNameReference name) => Resolve(name, new ReaderParameters());

    public AssemblyDefinition Resolve(AssemblyNameReference name, ReaderParameters parameters)
    {
        AssemblyName identity = IdentityOf(name);
        if (modules.TryGetValue(identity, out var module)) return module.Assembly;
        if (Platform(identity)) return PlatformAssembly(identity);
        var named = byName.GetValueOrDefault(identity.Name);
        throw new InvalidDataException(named is null
            ? $"Unpinned assembly reference: {name.FullName}\n" +
                $"  Pass --reference <path to {name.Name}.dll> to extract from it."
            : $"Pinned assembly does not match its reference: {name.FullName}\n" +
                $"  Pinned: {named.Assembly.Name.FullName}");
    }

    // Keyed by the requested identity and by the identity of the assembly read, since the runtime can answer a
    // reference of another version with an assembly already read.
    AssemblyDefinition PlatformAssembly(AssemblyName requested)
    {
        if (platformAssemblies.TryGetValue(requested, out AssemblyDefinition? assembly)) return assembly;
        if (platformByName.TryGetValue(requested.Name, out assembly))
        {
            RequirePlatformIdentity(requested, IdentityOf(assembly.Name));
            platformAssemblies.Add(requested, assembly);
            return assembly;
        }
        if (!platformPaths.TryGetValue(requested.Name, out string? path))
            throw new InvalidDataException("No exact trusted platform assembly: " + requested.ToDisplay());
        byte[] bytes = File.ReadAllBytes(path);
        ModuleDefinition module = Read(bytes);
        try
        {
            RegisterIdentityImage(module, bytes);
            AssemblyName loaded = IdentityOf(module.Assembly.Name);
            RequirePlatformIdentity(requested, loaded);
            if (platformAssemblies.TryGetValue(loaded, out assembly)) ReleaseModule(module);
            else platformAssemblies.Add(loaded, assembly = module.Assembly);
            platformByName.Add(loaded.Name, assembly);
            platformAssemblies.TryAdd(requested, assembly);
            return assembly;
        }
        catch { ReleaseModule(module); throw; }
    }

    static void RequirePlatformIdentity(AssemblyName requested, AssemblyName loaded)
    {
        if (loaded.Name != requested.Name || loaded.Culture != requested.Culture ||
            loaded.PublicKeyToken != requested.PublicKeyToken || !Platform(loaded))
            throw new InvalidDataException("Trusted platform assembly identity mismatch: " + requested.ToDisplay());
    }

    static Dictionary<MetadataName, string> PlatformPaths()
    {
        var paths = new Dictionary<MetadataName, string>();
        if (AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") is not string trusted) return paths;
        foreach (string path in trusted.Split(Path.PathSeparator))
            if (string.Equals(Path.GetExtension(path), ".dll", StringComparison.OrdinalIgnoreCase))
                paths[MetadataName.OfText(Path.GetFileNameWithoutExtension(path))] = path;
        return paths;
    }

    AssemblyName IdentityOf(AssemblyNameReference name) => identityRows.TryGetValue(name, out var row)
        ? row.Read() : throw new InvalidDataException("Assembly reference without registered image provenance");

    void RegisterRows(ModuleDefinition module, MetadataImage image)
    {
        IdentityRows.RequireModule(image, module);
        if (registrations.ContainsKey(module))
            throw new InvalidDataException("Module identity already registered");
        if (module.Assembly is null || module.MetadataKind != MetadataKind.Ecma335 ||
            module.AssemblyReferences.Count != image.Count(0x23))
            throw new InvalidDataException("Assembly references do not match image rows");
        AssemblyNameReference[] names = [module.Assembly.Name, .. module.AssemblyReferences];
        for (int index = 0; index < names.Length; index++)
        {
            uint token = index == 0 ? 0x20000001 : 0x23000000 + (uint)index;
            if (names[index].MetadataToken.ToUInt32() != token || identityRows.ContainsKey(names[index]))
                throw new InvalidDataException("Assembly reference without an original image row");
        }
        bool knownImage = rowsByImage.TryGetValue(image, out var rows);
        rows ??= [];
        if (!rows.TryGetValue(0x20000001, out var definition))
            rows.Add(0x20000001, definition = new(image, 0x20000001));
        definition.Read();
        var primitiveEntries = Signatures.Prepare(module, image, names);
        int added = 0;
        bool published = false;
        try
        {
            if (!knownImage) rowsByImage.Add(image, rows);
            foreach (AssemblyNameReference name in names)
            {
                uint token = name.MetadataToken.ToUInt32();
                if (!rows.TryGetValue(token, out var row)) rows.Add(token, row = new(image, token));
                identityRows.Add(name, row);
                added++;
            }
            Signatures.Publish(primitiveEntries);
            published = true;
            registrations.Add(module, new(names, primitiveEntries));
        }
        catch
        {
            if (published) Signatures.Remove(primitiveEntries);
            for (int index = 0; index < added; index++) identityRows.Remove(names[index]);
            if (!knownImage) rowsByImage.Remove(image);
            throw;
        }
    }

    void UnregisterRows(ModuleDefinition module)
    {
        if (registrations.Remove(module, out var registration))
        {
            foreach (AssemblyNameReference name in registration.Names) identityRows.Remove(name);
            Signatures.Remove(registration.Primitives);
        }
    }

    void ReleaseModule(ModuleDefinition module)
    {
        UnregisterIdentityImage(module);
        if (!ownedModules.Remove(module, out var stream)) return;
        module.Dispose();
        stream.Dispose();
    }

    public void Dispose()
    {
        if (disposed) return;
        disposed = true;
        if (active == this) active = previous;
        foreach (PEReader reader in readers.Values) reader.Dispose();
        foreach (var image in identityImages.Values) image.Reader.Dispose();
        foreach (var (module, stream) in ownedModules)
        {
            module.Dispose();
            stream.Dispose();
        }
        identityRows.Clear();
        Signatures.Dispose();
        rowsByImage.Clear();
        registrations.Clear();
        ownedModules.Clear();
        identityImages.Clear();
        modules.Clear();
        platformAssemblies.Clear();
        platformByName.Clear();
        images.Clear();
        readers.Clear();
        metadata.Clear();
        indices.Clear();
        originals.Clear();
        working.Clear();
        byName.Clear();
    }
}
