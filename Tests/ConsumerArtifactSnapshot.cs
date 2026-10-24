#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Reflection;
using System.Text.Json;

var verifier = Assembly.LoadFrom(ExtractorPath).GetType("Program", throwOnError: true)!;
var flags = BindingFlags.NonPublic | BindingFlags.Static;
var capture = verifier.GetMethod("ConsumerArtifactSnapshot", flags)!;
var parts = verifier.GetMethod("ConsumerSnapshotParts", flags)!;
var originalParts = verifier.GetMethod("ConsumerModuleParts", flags)!;
var root = Path.Combine(Path.GetTempPath(), "leancil-consumer-snapshot-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
try
{
    var path = Path.Combine(root, "Proof.olean");
    foreach (var suffix in new[] { "", ".private", ".server", ".unexpected" })
        File.WriteAllText(path + suffix, "checked " + suffix);
    File.WriteAllText(Path.Combine(root, "Orphan.olean.private"), "orphan private part");
    File.WriteAllText(Path.Combine(root, "Proof.trace"), "not a module part");
    SortedDictionary<string, string> Snapshot() =>
        (SortedDictionary<string, string>)capture.Invoke(null, [root])!;
    string Manifest(SortedDictionary<string, string> snapshot) =>
        JsonSerializer.Serialize(parts.Invoke(null, [snapshot, "Proof.olean", path]));
    var snapshot = Snapshot();
    var manifest = Manifest(snapshot);
    if (manifest != JsonSerializer.Serialize(originalParts.Invoke(null, [path])))
        throw new Exception("Snapshot changed the exact replay manifest bytes.");
    if (snapshot.Count != 5 || !snapshot.ContainsKey("Orphan.olean.private") ||
        !snapshot.ContainsKey("Proof.olean.unexpected"))
        throw new Exception("Discovery lost orphan or unknown artifact parts.");
    foreach (var suffix in new[] { "", ".private", ".server" })
    {
        var before = File.ReadAllText(path + suffix);
        File.WriteAllText(path + suffix, "tampered " + suffix);
        if (Manifest(Snapshot()) == manifest)
            throw new Exception("Fresh snapshot missed changed module part: " + suffix);
        File.WriteAllText(path + suffix, before);
        File.Delete(path + suffix);
        if (Manifest(Snapshot()) == manifest)
            throw new Exception("Fresh snapshot missed removed module part: " + suffix);
        File.WriteAllText(path + suffix, before);
    }
    File.WriteAllText(Path.Combine(root, "Shadow.olean"), "new module");
    if (!Snapshot().ContainsKey("Shadow.olean")) throw new Exception("Fresh snapshot missed an added module.");
    // Windows resolves part names without regard to casing, including existing package artifacts.
    if (OperatingSystem.IsWindows())
    {
        File.Move(path + ".private", path + ".PRIVATE");
        if (Manifest(Snapshot()) != JsonSerializer.Serialize(originalParts.Invoke(null, [path])))
            throw new Exception("Snapshot changed case-insensitive part resolution.");
    }
    Console.WriteLine("Consumer artifact snapshots preserve manifests and detect changed, removed and added artifacts.");
}
finally { Directory.Delete(root, true); }
