#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/DeepCheckInputs.cs
#:include ../scripts/BindingImage.cs

using System.Diagnostics;
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
    Require(inputs.Images.Count == 2 && inputs.Digest == Hash(Encoding.UTF8.GetBytes(source)), "File snapshot hash");
    var pins = inputs.MatchPins(Identity(digest, [digest, digest], "Unrelated, Version=1.0.0.0"));
    Require(pins.Count == 3 && pins.All(pin => pin.Image.Digest == digest), "Digest matching ignores names");
    Require(Read(source + $"{digest}  ./first image.dll\n").Images.Count == 2, "Identical duplicate paths");
    Reject(() => Read(source + $"{new string('0', 64)}  first image.dll\n"), "Conflicting SHA-256");
    Reject(() => inputs.MatchPins(Identity(new string('0', 64), [])), "No line");
    Reject(() => inputs.MatchPins(Identity(digest, [new string('0', 64)])), "No line");
    Reject(() => Read($"{new string('0', 64)}  first image.dll\n"), "SHA-256 of");
    File.WriteAllBytes(Path.Combine(root, "second.dll"), [9]);
    Reject(() => Read(source), "SHA-256 of");
    Require(inputs.Images.All(image => image.Bytes.SequenceEqual(original)), "Retained image snapshot");
    File.WriteAllText(file, "changed");
    Require(inputs.Digest == Hash(Encoding.UTF8.GetBytes(source)), "Retained digest file hash");
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
        Require(request.MatchPins(identity).Select(pin => pin.Image.Digest).SequenceEqual(hashes),
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
