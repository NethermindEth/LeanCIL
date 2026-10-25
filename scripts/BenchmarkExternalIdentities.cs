#!/usr/bin/env dotnet
#:property PublishAot=false
#:include Verification.cs
#:include ../Extractor/ExternalIdentityEvidence.cs

using System.Diagnostics;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using Nethermind.LeanCIL;

if (args.Length == 0)
    throw new ArgumentException(
        "Pass fixed baseline Extracted.lean files containing externalIdentityNBytes_eq proofs.");
var directory = At("artifacts/ExternalIdentityBenchmark");
Directory.CreateDirectory(directory);
var leanPath = directory + Path.PathSeparator + At(".lake/build/lib/lean");
var checker = Path.Combine(Run(["lean", "--print-prefix"]).Trim(), "bin",
    OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
var declaration = new Regex(@"def (externalIdentity\d+)Bytes : ByteArray := ⟨#\[([^\]]*)\]⟩" +
    @"[\s\S]*?#print axioms \1_eq");
var measurements = new List<object>();
foreach (var (input, index) in args.Select((input, index) => (Path.GetFullPath(input), index)))
{
    var baseline = File.ReadAllText(input);
    var emitter = new ExternalIdentityEvidence();
    var count = 0;
    var updated = declaration.Replace(baseline, match =>
    {
        var bytes = match.Groups[2].Value.Split(", ", StringSplitOptions.RemoveEmptyEntries)
            .Select(byte.Parse).ToArray();
        var name = emitter.Reference(Encoding.UTF8.GetString(bytes), true);
        if (name != match.Groups[1].Value)
            throw new InvalidOperationException("Unexpected identity declaration order in " + input);
        var emitted = new StringBuilder();
        emitter.Emit(emitted);
        count++;
        return emitted.ToString();
    });
    foreach (var (variant, text) in new[] { ("Baseline", baseline), ("Updated", updated) })
    {
        var module = "Input" + index + variant;
        var source = Path.Combine(directory, module + ".lean");
        File.WriteAllText(source, text);
        var timer = Stopwatch.StartNew();
        var output = Run(["lean", "-j1", "--root=" + directory, "-o", Path.ChangeExtension(source, ".olean"), source],
            leanPath: leanPath, progress: module + " compilation");
        if (output.Contains("sorryAx", StringComparison.Ordinal))
            throw new InvalidOperationException("Unproved declaration in " + module);
        var compileMs = timer.Elapsed.TotalMilliseconds;
        timer.Restart();
        Run([checker, module], leanPath: leanPath, progress: module + " kernel replay");
        var replayMs = timer.Elapsed.TotalMilliseconds;
        var measurement = new
        {
            input, sha256 = Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(input))),
            variant, identities = count, compileMs, replayMs,
            sourceBytes = new FileInfo(source).Length,
            oleanBytes = new FileInfo(Path.ChangeExtension(source, ".olean")).Length
        };
        measurements.Add(measurement);
        Console.WriteLine(JsonSerializer.Serialize(measurement));
    }
}
File.WriteAllText(Path.Combine(directory, "timings.json"),
    JsonSerializer.Serialize(measurements, new JsonSerializerOptions { WriteIndented = true }));
