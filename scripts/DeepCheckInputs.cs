using System.Collections.ObjectModel;
using System.Text;
using System.Text.Json;

/// <summary>Consumer-stated image bytes and digest-indexed extraction pins; these are inputs, not evidence.</summary>
internal sealed class DeepCheckInputs
{
    /// <summary>A file snapshot whose bytes have the consumer-stated SHA-256 digest.</summary>
    internal sealed class Image
    {
        readonly byte[] bytes;

        internal Image(string path, string digest, byte[] bytes)
        {
            Path = path;
            Digest = digest;
            this.bytes = bytes;
        }

        internal string Path { get; }
        internal string Digest { get; }
        internal ReadOnlySpan<byte> Bytes => bytes;
    }

    /// <summary>An extraction pin matched by digest; its display identity does not select the image.</summary>
    internal sealed record Pin(string Identity, Image Image);

    readonly Dictionary<string, Image> byDigest;

    DeepCheckInputs(string path, string digest, List<Image> images, Dictionary<string, Image> byDigest)
    {
        Path = path;
        Digest = digest;
        Images = images.AsReadOnly();
        this.byDigest = byDigest;
    }

    internal string Path { get; }
    internal string Digest { get; }
    internal ReadOnlyCollection<Image> Images { get; }

    /// <summary>Reads and checks every stated file once per normalized path, retaining the checked bytes.</summary>
    internal static DeepCheckInputs Read(string path)
    {
        path = System.IO.Path.GetFullPath(path);
        var source = File.ReadAllBytes(path);
        var text = new UTF8Encoding(false, true).GetString(source);
        var directory = System.IO.Path.GetDirectoryName(path)!;
        Dictionary<string, string> paths = new(StringComparer.Ordinal);
        Dictionary<string, Image> digests = new(StringComparer.Ordinal);
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
            var digest = NormalizeDigest(line.AsSpan(start, 64), $"{path}:{lineNumber}");
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
            var actual = BindingImage.Digest(bytes);
            if (actual != digest)
                throw new ArgumentException($"SHA-256 of {file} is {actual}; {path} states {digest}.");
            var image = new Image(file, digest, bytes);
            images.Add(image);
            digests.TryAdd(digest, image);
        }
        if (images.Count == 0) throw new ArgumentException($"No SHA-256 records in {path}.");
        return new(path, BindingImage.Digest(source), images, digests);

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
        return pins.AsReadOnly();

        void Add(JsonElement record, string digestProperty)
        {
            var name = record.GetProperty("assemblyIdentity").GetString()
                ?? throw new ArgumentException("Missing pinned assembly identity.");
            var digest = NormalizeDigest(record.GetProperty(digestProperty).GetString().AsSpan(), "identity.json");
            if (!byDigest.TryGetValue(digest, out var image))
                throw new ArgumentException($"No line of {Path} has the digest identity.json pins for {name}.");
            pins.Add(new(name, image));
        }
    }

    static string NormalizeDigest(ReadOnlySpan<char> value, string source)
    {
        if (value.Length != 64 || value.ContainsAnyExcept("0123456789abcdefABCDEF"))
            throw new ArgumentException($"Invalid SHA-256 digest in {source}.");
        return value.ToString().ToLowerInvariant();
    }

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
