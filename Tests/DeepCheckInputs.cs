#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include ../scripts/Checking/BindingImage.cs

using System.Diagnostics;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

var root = Path.Combine(Path.GetTempPath(), "LeanCIL-DeepInputs-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
try
{
    var file = Path.Combine(root, "pins.sha256");
    byte[] original = [1, 2, 3, 4];
    var digest = Hash(original);
    File.WriteAllBytes(Path.Combine(root, "first image.dll"), original);
    File.WriteAllBytes(Path.Combine(root, "second.dll"), original);
    var source = $"{digest.ToUpperInvariant()}  first image.dll\r\n{digest} *second.dll\n";
    var inputs = Read(source);
    Require(inputs.Images.Count == 2 && inputs.Digest.ToString() == Hash(Encoding.UTF8.GetBytes(source)),
        "File snapshot hash");
    var pins = inputs.MatchPins(Identity(digest, [digest, digest], "Unrelated, Version=1.0.0.0"));
    Require(pins.Count == 3 && pins.All(pin => pin.Image.Digest.ToString() == digest),
        "Digest matching ignores names");
    var stated = Sha256Digest.Parse(digest.ToUpperInvariant(), "a test digest");
    Require(stated == Sha256Digest.Parse(digest, "a test digest") && stated == Sha256Digest.Of(original) &&
        stated.ToString() == digest && new HashSet<Sha256Digest> { stated, Sha256Digest.Of(original) }.Count == 1,
        "A digest stated in either case is one 32-byte value with lowercase text");
    var changed = digest[..^1] + (digest[^1] == '0' ? '1' : '0');
    Require(Sha256Digest.Parse(changed, "a test digest") != stated, "One changed digit is another digest");
    Reject(() => Sha256Digest.Parse(digest.AsSpan()[..^1], "a test digest"), "Invalid SHA-256 digest");
    Require(Read(source + $"{digest}  ./first image.dll\n").Images.Count == 2, "Identical duplicate paths");
    Reject(() => Read(source + $"{new string('0', 64)}  first image.dll\n"), "Conflicting SHA-256");
    Reject(() => inputs.MatchPins(Identity(new string('0', 64), [])), "No line");
    Reject(() => inputs.MatchPins(Identity(digest, [new string('0', 64)])), "No line");
    Reject(() => Read($"{new string('0', 64)}  first image.dll\n"), "SHA-256 of");
    File.WriteAllBytes(Path.Combine(root, "second.dll"), [9]);
    Reject(() => Read(source), "SHA-256 of");
    Require(inputs.Images.All(image => image.Bytes.SequenceEqual(original)), "Retained image snapshot");
    File.WriteAllText(file, "changed");
    Require(inputs.Digest.ToString() == Hash(Encoding.UTF8.GetBytes(source)), "Retained digest file hash");
    File.WriteAllBytes(file, [0xc3, 0x28]);
    Reject(() => DeepCheckInputs.Read(file), null);
    Reject(() => Read($"{digest}  missing.dll\n"), "Could not find file");
    foreach (var malformed in new[] { "", "\n", "# comment\n", digest + " first image.dll\n",
        digest + " xfirst image.dll\n", digest + "  \n", new string('g', 64) + "  first image.dll\n",
        "\\" + digest + "  invalid\\q\n", "\\" + digest + "  incomplete\\\n" })
        Reject(() => Read(malformed), null);

    var nested = Path.Combine(root, "folder");
    Directory.CreateDirectory(nested);
    var escapedName = OperatingSystem.IsWindows() ? "folder\\escaped.dll" : "escaped\\name.dll";
    File.WriteAllBytes(Path.Combine(root, escapedName), original);
    var escaped = "\\" + digest + " *" + escapedName.Replace("\\", "\\\\") + "\n";
    Require(Read(escaped).Images.Single().Bytes.SequenceEqual(original), "Escaped backslash filename");
    if (!OperatingSystem.IsWindows())
    {
        foreach (var character in new[] { '\n', '\r' })
        {
            var name = "escaped" + character + "name.dll";
            File.WriteAllBytes(Path.Combine(root, name), original);
            var encoded = name.Replace("\n", "\\n").Replace("\r", "\\r");
            Require(Read("\\" + digest + "  " + encoded).Images.Count == 1, "Escaped control filename");
        }
    }

    var consumer = Image("Consumer", reference: "Facade");
    var facade = Image("Facade", forward: "Middle", other: "Unrelated");
    var middle = Image("Middle", forward: "Destination");
    var destination = Image("Destination");
    var unrelated = Image("Unrelated");
    var request = Identity(Hash(File.ReadAllBytes(consumer)), [], AssemblyName.GetAssemblyName(consumer).FullName);
    string[] Selected(params string[] paths) =>
        Read(string.Concat(paths.Select(path => Hash(File.ReadAllBytes(path)) + "  " + path + "\n")))
            .MatchPins(request).Select(pin => Path.GetFileNameWithoutExtension(pin.Image.Path)).ToArray();

    Require(Selected(unrelated, destination, consumer, middle, facade)
        .SequenceEqual(["Consumer", "Facade", "Middle", "Destination"]), "Matching type across two forwards");
    Require(Selected(consumer, facade, destination, unrelated).SequenceEqual(["Consumer", "Facade"]),
        "A destination without the intervening forwarding image cannot be selected");
    Image("Middle", forward: "Facade");
    Require(Selected(consumer, facade, middle, destination).SequenceEqual(["Consumer", "Facade", "Middle"]),
        "A forwarding cycle terminates without selecting an unrelated destination");

    var shortChain = MeasureForwarding(8);
    var longChain = MeasureForwarding(64);
    Console.WriteLine($"Forwarding selection: 8={shortChain:F3} ms, 64={longChain:F3} ms");
    Require(longChain < shortChain * 24, "Forwarding selection must scale below quadratic growth");

    var small = Measure(512);
    var large = Measure(4096);
    Console.WriteLine($"Pin matching: 512={small.Match:F3} ms, 4096={large.Match:F3} ms");
    Console.WriteLine($"Reading and hashing: 512={small.Read:F3} ms, 4096={large.Read:F3} ms");
    Require(large.Match < small.Match * 24, "Pin matching must scale below quadratic growth");
    Require(large.Read < small.Read * 24, "Reading and hashing must scale below quadratic growth");
    Console.WriteLine("PASS digest parsing, all-file checking, pin matching, snapshots and scaling");

    DeepCheckInputs Read(string text)
    {
        File.WriteAllText(file, text, new UTF8Encoding(false));
        return DeepCheckInputs.Read(file);
    }

    string Image(string name, string? reference = null, string? forward = null, string? other = null)
    {
        var rows = new MetadataBuilder();
        var version = new Version(1, 0, 0, 0);
        var fileName = name + ".dll";
        rows.AddModule(0, rows.GetOrAddString(fileName), rows.GetOrAddGuid(Guid.Empty), default, default);
        rows.AddAssembly(rows.GetOrAddString(name), version, default, default, 0, AssemblyHashAlgorithm.Sha1);
        rows.AddTypeDefinition(0, default, rows.GetOrAddString("<Module>"), default,
            MetadataTokens.FieldDefinitionHandle(1), MetadataTokens.MethodDefinitionHandle(1));
        var ns = rows.GetOrAddString("Example");
        var item = rows.GetOrAddString("Item");
        AssemblyReferenceHandle AssemblyRef(string target) =>
            rows.AddAssemblyReference(rows.GetOrAddString(target), version, default, default, 0, default);
        if (reference is not null) rows.AddTypeReference(AssemblyRef(reference), ns, item);
        const TypeAttributes forwarder = (TypeAttributes)0x00200000;
        if (forward is not null) rows.AddExportedType(forwarder, ns, item, AssemblyRef(forward), 0);
        if (other is not null)
            rows.AddExportedType(forwarder, rows.GetOrAddString("Other"), item, AssemblyRef(other), 0);
        var pe = new ManagedPEBuilder(PEHeaderBuilder.CreateLibraryHeader(), new MetadataRootBuilder(rows),
            new BlobBuilder());
        var bytes = new BlobBuilder();
        pe.Serialize(bytes);
        var path = Path.Combine(root, fileName);
        File.WriteAllBytes(path, bytes.ToArray());
        return path;
    }

    double MeasureForwarding(int links)
    {
        var first = Image("ChainConsumer", reference: "Link0");
        var paths = new List<string> { first };
        for (var index = 0; index < links; index++)
            paths.Add(Image("Link" + index, forward: "Link" + (index + 1)));
        paths.Add(Image("Link" + links));
        var manifest = Read(string.Concat(paths.Select(path => Hash(File.ReadAllBytes(path)) + "  " + path + "\n")));
        var identity = Identity(Hash(File.ReadAllBytes(first)), [], AssemblyName.GetAssemblyName(first).FullName);
        Require(manifest.MatchPins(identity).Select(pin => pin.Image.Path).SequenceEqual(paths),
            "Every hop resolves the same qualified type through its assembly reference");
        List<double> samples = [];
        for (var sample = 0; sample < 7; sample++)
        {
            var timer = Stopwatch.StartNew();
            for (var repeat = 0; repeat < 12; repeat++) manifest.MatchPins(identity);
            samples.Add(timer.Elapsed.TotalMilliseconds);
        }
        samples.Sort();
        return samples[samples.Count / 2];
    }

    (double Read, double Match) Measure(int count)
    {
        StringBuilder records = new();
        List<string> hashes = [];
        for (var index = 0; index < count; index++)
        {
            var bytes = BitConverter.GetBytes(index);
            var hash = Hash(bytes);
            var name = $"image{index}.dll";
            File.WriteAllBytes(Path.Combine(root, name), bytes);
            hashes.Add(hash);
            records.Append(hash).Append("  ").Append(name).Append('\n');
        }
        var request = Read(records.ToString());
        List<double> reads = [];
        for (var sample = 0; sample < 5; sample++)
        {
            var timer = Stopwatch.StartNew();
            Require(DeepCheckInputs.Read(file).Images.Count == count, "All stated images retained");
            reads.Add(timer.Elapsed.TotalMilliseconds);
        }
        reads.Sort();
        var identity = Identity(hashes[0], hashes.Skip(1).ToArray());
        Require(request.MatchPins(identity).Select(pin => pin.Image.Digest.ToString()).SequenceEqual(hashes),
            "Distinct digests with the same display name match distinct images");
        for (var warm = 0; warm < 10; warm++) request.MatchPins(identity);
        List<double> measurements = [];
        for (var sample = 0; sample < 7; sample++)
        {
            var timer = Stopwatch.StartNew();
            for (var repeat = 0; repeat < 30; repeat++)
                Require(request.MatchPins(identity).Count == count, "All pins retained");
            measurements.Add(timer.Elapsed.TotalMilliseconds);
        }
        measurements.Sort();
        return (reads[reads.Count / 2], measurements[measurements.Count / 2]);
    }
}
finally
{
    Directory.Delete(root, recursive: true);
}

static string Hash(byte[] bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));

static JsonElement Identity(string digest, string[] references, string name = "Same, Version=1.0.0.0") =>
    JsonSerializer.SerializeToElement(new
    {
        assemblyIdentity = name,
        assemblySha256 = digest,
        references = references.Select(hash => new { assemblyIdentity = name, sha256 = hash }).ToArray()
    });

static void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}

static void Reject(Action action, string? message)
{
    try { action(); }
    catch (Exception error) when (error is ArgumentException or IOException)
    {
        if (message is null || error.Message.Contains(message, StringComparison.Ordinal)) return;
        throw new InvalidOperationException($"Expected {message}, got {error.Message}", error);
    }
    throw new InvalidOperationException("Invalid deep input was accepted");
}
