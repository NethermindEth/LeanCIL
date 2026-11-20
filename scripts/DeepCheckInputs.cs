using System.Buffers.Binary;
using System.Collections.ObjectModel;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

/// <summary>
/// A SHA-256 digest held as its 32 bytes and compared by value; its lowercase hexadecimal text is for reports and
/// generated names only.
/// </summary>
internal readonly record struct Sha256Digest
{
    /// <summary>The bytes of a SHA-256 digest.</summary>
    internal const int Length = 32;

    const int HalfLength = Length / 2;
    readonly UInt128 high;
    readonly UInt128 low;

    Sha256Digest(ReadOnlySpan<byte> digest)
    {
        high = BinaryPrimitives.ReadUInt128BigEndian(digest);
        low = BinaryPrimitives.ReadUInt128BigEndian(digest[HalfLength..]);
    }

    /// <summary>The digest of <paramref name="data"/>.</summary>
    internal static Sha256Digest Of(ReadOnlySpan<byte> data)
    {
        Span<byte> digest = stackalloc byte[Length];
        SHA256.HashData(data, digest);
        return new(digest);
    }

    /// <summary>The digest 64 hexadecimal digits of either case spell; anything else names no digest.</summary>
    internal static Sha256Digest Parse(ReadOnlySpan<char> text, string source)
    {
        if (text.Length != 2 * Length || text.ContainsAnyExcept("0123456789abcdefABCDEF"))
            throw new ArgumentException($"Invalid SHA-256 digest in {source}.");
        return new(Convert.FromHexString(text));
    }

    /// <summary>Writes the digest's 32 bytes, most significant first.</summary>
    internal void CopyTo(Span<byte> destination)
    {
        BinaryPrimitives.WriteUInt128BigEndian(destination, high);
        BinaryPrimitives.WriteUInt128BigEndian(destination[HalfLength..Length], low);
    }

    /// <summary>The 64 lowercase hexadecimal digits of the digest.</summary>
    public override string ToString()
    {
        Span<byte> digest = stackalloc byte[Length];
        CopyTo(digest);
        return Convert.ToHexStringLower(digest);
    }
}

/// <summary>Consumer-stated image bytes and digest-indexed extraction pins; these are inputs, not evidence.</summary>
internal sealed class DeepCheckInputs
{
    /// <summary>A file snapshot whose bytes have the consumer-stated SHA-256 digest.</summary>
    internal sealed class Image
    {
        readonly byte[] bytes;

        internal Image(string path, Sha256Digest digest, byte[] bytes)
        {
            Path = path;
            Digest = digest;
            this.bytes = bytes;
        }

        internal string Path { get; }
        internal Sha256Digest Digest { get; }
        internal ReadOnlySpan<byte> Bytes => bytes;
        internal PEReader OpenPe() => new(new MemoryStream(bytes, writable: false));
    }

    /// <summary>An extraction pin matched by digest; its display identity does not select the image.</summary>
    internal sealed record Pin(string Identity, Image Image, bool Platform = false,
        bool? ObjectCoverage = null, bool? TupleCoverage = null, bool? KeyCoverage = null,
        bool Reference = false);

    readonly Dictionary<Sha256Digest, Image> byDigest;

    DeepCheckInputs(string path, Sha256Digest digest, List<Image> images, Dictionary<Sha256Digest, Image> byDigest)
    {
        Path = path;
        Digest = digest;
        Images = images.AsReadOnly();
        this.byDigest = byDigest;
    }

    internal string Path { get; }
    internal Sha256Digest Digest { get; }
    internal ReadOnlyCollection<Image> Images { get; }

    /// <summary>Reads and checks every stated file once per normalized path, retaining the checked bytes.</summary>
    internal static DeepCheckInputs Read(string path)
    {
        path = System.IO.Path.GetFullPath(path);
        var source = File.ReadAllBytes(path);
        var text = new UTF8Encoding(false, true).GetString(source);
        var directory = System.IO.Path.GetDirectoryName(path)!;
        Dictionary<string, Sha256Digest> paths = new(StringComparer.Ordinal);
        Dictionary<Sha256Digest, Image> digests = [];
        List<Image> images = [];
        using var reader = new StringReader(text);
        var lineNumber = 0;
        while (reader.ReadLine() is { } line)
        {
            lineNumber++;
            var escaped = line.StartsWith('\\');
            var start = escaped ? 1 : 0;
            if (line.Length < start + 67 || line[start + 64] != ' ' ||
                line[start + 65] is not (' ' or '*'))
                throw InvalidLine();
            var digest = Sha256Digest.Parse(line.AsSpan(start, 2 * Sha256Digest.Length), $"{path}:{lineNumber}");
            var name = line[(start + 66)..];
            if (escaped) name = Unescape(name, path, lineNumber);
            var file = System.IO.Path.GetFullPath(name, directory);
            if (paths.TryGetValue(file, out var previous))
            {
                if (previous != digest)
                    throw new ArgumentException($"Conflicting SHA-256 digests for {file} in {path}.");
                continue;
            }
            paths.Add(file, digest);
            var bytes = File.ReadAllBytes(file);
            var actual = Sha256Digest.Of(bytes);
            if (actual != digest)
                throw new ArgumentException($"SHA-256 of {file} is {actual}; {path} states {digest}.");
            var image = new Image(file, digest, bytes);
            images.Add(image);
            digests.TryAdd(digest, image);
        }
        if (images.Count == 0) throw new ArgumentException($"No SHA-256 records in {path}.");
        return new(path, Sha256Digest.Of(source), images, digests);

        ArgumentException InvalidLine() =>
            new($"Invalid sha256sum record at {path}:{lineNumber}.");
    }

    /// <summary>Matches every selected and referenced assembly by its recorded digest in linear total work.</summary>
    internal ReadOnlyCollection<Pin> MatchPins(JsonElement identity)
    {
        List<Pin> pins = [];
        Add(identity, "assemblySha256");
        if (identity.TryGetProperty("references", out var references))
            foreach (var reference in references.EnumerateArray()) Add(reference, "sha256");
        var sourceCount = pins.Count;
        AddPlatformImages(pins, identity);
        AddReferenceImages(pins, sourceCount);
        return pins.AsReadOnly();

        void Add(JsonElement record, string digestProperty)
        {
            var name = record.GetProperty("assemblyIdentity").GetString()
                ?? throw new ArgumentException("Missing pinned assembly identity.");
            var digest = Sha256Digest.Parse(record.GetProperty(digestProperty).GetString().AsSpan(), "identity.json");
            if (!byDigest.TryGetValue(digest, out var image))
                throw new ArgumentException($"No line of {Path} has the digest identity.json pins for {name}.");
            pins.Add(new(name, image));
        }
    }

    /// <summary>Match direct AssemblyRefs of the extraction pins to digest-checked images.
    /// The kernel checks the physical rows, the carried tokens and the definition keys.</summary>
    void AddReferenceImages(List<Pin> pins, int sourceCount)
    {
        HashSet<string> required = new(StringComparer.Ordinal);
        var malformed = false;
        foreach (var pin in pins.Take(sourceCount).DistinctBy(pin => pin.Image.Digest))
        {
            try
            {
                using var pe = pin.Image.OpenPe();
                var metadata = pe.GetMetadataReader();
                foreach (var handle in metadata.AssemblyReferences)
                {
                    var reference = metadata.GetAssemblyReference(handle);
                    if (InvalidTokenWidth(metadata, reference))
                        malformed = true;
                    else
                        required.Add(reference.GetAssemblyName().FullName);
                }
            }
            catch (BadImageFormatException) { return; } // The image audit diagnoses malformed extraction pins.
        }
        if (required.Count == 0 && !malformed) return;
        var digests = pins.Select(pin => pin.Image.Digest).ToHashSet();
        var pinnedNames = pins.Select(pin => pin.Identity).ToHashSet(StringComparer.Ordinal);
        var matched = required.Where(pinnedNames.Contains).ToHashSet(StringComparer.Ordinal);
        foreach (var image in byDigest.Values.Where(image => !digests.Contains(image.Digest)))
        {
            string identity;
            try
            {
                using var pe = image.OpenPe();
                if (!pe.HasMetadata) continue;
                var metadata = pe.GetMetadataReader();
                if (!metadata.IsAssembly) continue;
                identity = metadata.GetAssemblyDefinition().GetAssemblyName().FullName;
            }
            catch (BadImageFormatException) { continue; }
            if (!required.Contains(identity) || pinnedNames.Contains(identity)) continue;
            if (!matched.Add(identity)) throw new ArgumentException($"More than one image for {identity} in {Path}.");
            pins.Add(new(identity, image, Reference: true));
        }
        if (matched.Count > 0 || malformed)
            pins[0] = pins[0] with { KeyCoverage = !malformed && matched.Count == required.Count };
    }

    static bool InvalidTokenWidth(MetadataReader reader, AssemblyReference reference) =>
        (reference.Flags & AssemblyFlags.PublicKey) == 0 &&
        reader.GetBlobReader(reference.PublicKeyOrToken).Length is not (0 or 8);

    /// <summary>Find platform inputs by full assembly identity in the retained bytes. The kernel independently
    /// resolves every scope from method evidence and checks the defining image and its physical fields.</summary>
    void AddPlatformImages(List<Pin> pins, JsonElement extraction)
    {
        var direct = pins.ToLookup(pin => pin.Image.Digest);
        if (direct.Count == byDigest.Count && !pins.Any(pin => CouldBePlatform(pin.Identity))) return;
        var available = byDigest.Values
            .Where(image => !direct.Contains(image.Digest) || direct[image.Digest].Any(pin => CouldBePlatform(pin.Identity)))
            .Select(image => (Image: image, Name: PlatformIdentity(image)))
            .Where(candidate => candidate.Name is not null)
            .ToLookup(candidate => candidate.Name!, candidate => candidate.Image, StringComparer.Ordinal);
        if (available.Count == 0) return;

        HashSet<string> required = new(StringComparer.Ordinal);
        foreach (var pin in pins.DistinctBy(pin => pin.Image.Digest))
        {
            using var pe = pin.Image.OpenPe();
            var metadata = pe.GetMetadataReader();
            if (available.Contains(pin.Identity)) required.Add(pin.Identity);
            foreach (var handle in metadata.AssemblyReferences)
            {
                var reference = metadata.GetAssemblyReference(handle).GetAssemblyName();
                if (CoreLibrary(reference)) required.Add(reference.FullName);
            }
        }
        const string pairName = "ValueTuple`2";
        // The admitted pair TypeRef has this exact scope (CIL.Extraction.runtimeScope).
        const string pairScope = "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a";
        const string pairPrefix = pairScope + "::System." + pairName + "<";
        HashSet<string> pairs = new(StringComparer.Ordinal);
        if (required.Contains(pairScope) && extraction.TryGetProperty("layoutIdentities", out var layouts) &&
            layouts.EnumerateArray().Any(layout => layout.GetString()!.StartsWith(pairPrefix, StringComparison.Ordinal)))
            pairs.Add(pairScope);

        FollowForwarders(required, "Object");
        FollowForwarders(pairs, pairName);
        var objectsComplete = required.All(available.Contains);
        var pairsComplete = pairs.All(available.Contains);
        foreach (var name in required.Union(pairs).Order(StringComparer.Ordinal))
        {
            if (available[name].SingleOrDefault() is { } image && !direct.Contains(image.Digest))
                pins.Add(new(name, image, Platform: true));
        }
        for (var index = 0; index < pins.Count; index++)
        {
            var pin = pins[index];
            pins[index] = pin with
            {
                ObjectCoverage = required.Contains(pin.Identity) ? objectsComplete : null,
                TupleCoverage = pairs.Contains(pin.Identity) ? pairsComplete : null
            };
        }

        void FollowForwarders(HashSet<string> scopes, string typeName)
        {
            Queue<string> pending = new(scopes);
            while (pending.TryDequeue(out var name))
            {
                var matches = available[name].ToArray();
                if (matches.Length == 0) continue;
                if (matches.Length != 1)
                    throw new InvalidDataException("Multiple images supplied for platform assembly " + name);
                using var pe = matches[0].OpenPe();
                var metadata = pe.GetMetadataReader();
                foreach (var handle in metadata.ExportedTypes)
                {
                    var type = metadata.GetExportedType(handle);
                    if (!type.IsForwarder || type.Implementation.Kind != HandleKind.AssemblyReference ||
                        !metadata.StringComparer.Equals(type.Name, typeName) ||
                        !metadata.StringComparer.Equals(type.Namespace, "System")) continue;
                    var target = metadata.GetAssemblyReference((AssemblyReferenceHandle)type.Implementation);
                    var assembly = target.GetAssemblyName();
                    if (CoreLibrary(assembly) && scopes.Add(assembly.FullName)) pending.Enqueue(assembly.FullName);
                }
            }
        }

        static bool CouldBePlatform(string identity)
        {
            var comma = identity.IndexOf(',');
            return comma > 0 && PlatformToken(identity.AsSpan(0, comma)) is not null;
        }
    }

    static string? PlatformIdentity(Image image)
    {
        try
        {
            using var pe = image.OpenPe();
            if (!pe.HasMetadata) return null;
            var metadata = pe.GetMetadataReader();
            if (!metadata.IsAssembly) return null;
            var assembly = metadata.GetAssemblyDefinition().GetAssemblyName();
            return CoreLibrary(assembly) ? assembly.FullName : null;
        }
        catch (BadImageFormatException) { return null; } // A digest list can include arbitrary unused files.
    }

    /// <summary>The physical AssemblyRef and token width of a rejected publisher-token check.</summary>
    internal static string? ReferenceKeyDiagnostic(IEnumerable<Pin> pins)
    {
        foreach (var pin in pins.Where(pin => !pin.Platform && !pin.Reference))
        {
            using var pe = pin.Image.OpenPe();
            var metadata = pe.GetMetadataReader();
            foreach (var handle in metadata.AssemblyReferences)
            {
                var reference = metadata.GetAssemblyReference(handle);
                if (InvalidTokenWidth(metadata, reference))
                    return $"{pin.Identity}, AssemblyRef {metadata.GetString(reference.Name)} has a " +
                        $"{metadata.GetBlobReader(reference.PublicKeyOrToken).Length}-byte public key token.";
            }
        }
        return null;
    }

    /// <summary>Physical field details for an already rejected kernel theorem.</summary>
    internal static string? ObjectFieldDiagnostic(IEnumerable<Pin> pins)
    {
        foreach (var pin in pins)
        {
            using var pe = pin.Image.OpenPe();
            var metadata = pe.GetMetadataReader();
            foreach (var handle in metadata.TypeDefinitions)
            {
                var type = metadata.GetTypeDefinition(handle);
                if (!type.GetDeclaringType().IsNil || !metadata.StringComparer.Equals(type.Name, "Object") ||
                    !metadata.StringComparer.Equals(type.Namespace, "System")) continue;
                foreach (var field in type.GetFields())
                    if ((metadata.GetFieldDefinition(field).Attributes & FieldAttributes.Static) == 0)
                        return $"System.Object in {pin.Identity} declares instance field 0x{MetadataTokens.GetToken(field):x8}.";
            }
        }
        return null;
    }

    /// <summary>The first declared instance field that disagrees with the pair's names or FIELD VAR signatures.
    /// The diagnostic accompanies a kernel rejection and plays no part in accepting the image.</summary>
    internal static string? TupleFieldDiagnostic(IEnumerable<Pin> pins)
    {
        foreach (var pin in pins)
        {
            using var pe = pin.Image.OpenPe();
            var metadata = pe.GetMetadataReader();
            foreach (var handle in metadata.TypeDefinitions)
            {
                var type = metadata.GetTypeDefinition(handle);
                if (!type.GetDeclaringType().IsNil || !metadata.StringComparer.Equals(type.Name, "ValueTuple`2") ||
                    !metadata.StringComparer.Equals(type.Namespace, "System")) continue;
                var slot = 0;
                foreach (var handleField in type.GetFields())
                {
                    var field = metadata.GetFieldDefinition(handleField);
                    if ((field.Attributes & FieldAttributes.Static) != 0) continue;
                    var name = metadata.GetString(field.Name);
                    var signature = metadata.GetBlobBytes(field.Signature);
                    if (slot >= 2 || name != "Item" + (slot + 1) ||
                        signature is not [0x06, 0x13, var parameter] || parameter != slot)
                        return $"System.ValueTuple`2 in {pin.Identity}, field 0x{MetadataTokens.GetToken(handleField):x8}" +
                            $" at instance slot {slot}: {name}, signature {Convert.ToHexStringLower(signature)}.";
                    slot++;
                }
                if (slot != 2) return $"System.ValueTuple`2 in {pin.Identity} declares {slot} instance fields.";
            }
        }
        return null;
    }

    static bool CoreLibrary(AssemblyName assembly)
    {
        var token = PlatformToken(assembly.Name);
        return token is not null && string.IsNullOrEmpty(assembly.CultureName) &&
            assembly.GetPublicKeyToken() is { Length: 8 } key && Convert.ToHexStringLower(key) == token;
    }

    static string? PlatformToken(ReadOnlySpan<char> name) => name switch
    {
        "System.Runtime" => "b03f5f7f11d50a3a",
        "System.Private.CoreLib" => "7cec85d7bea7798e",
        "mscorlib" => "b77a5c561934e089",
        "netstandard" => "cc7b13ffcd2ddd51",
        _ => null
    };

    static string Unescape(string name, string path, int line)
    {
        StringBuilder decoded = new(name.Length);
        for (var index = 0; index < name.Length; index++)
        {
            var character = name[index];
            if (character == '\\')
            {
                if (++index == name.Length)
                    throw new ArgumentException($"Incomplete filename escape at {path}:{line}.");
                character = name[index] switch
                {
                    '\\' => '\\',
                    'n' => '\n',
                    'r' => '\r',
                    _ => throw new ArgumentException($"Invalid filename escape at {path}:{line}.")
                };
            }
            decoded.Append(character);
        }
        return decoded.ToString();
    }
}
