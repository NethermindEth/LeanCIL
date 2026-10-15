#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

// Fast cache-integrity regressions; end-to-end cold/warm verification exercises the builder.
var directory = Path.Combine(Path.GetTempPath(), "leancil-cache-test-" + Guid.NewGuid().ToString("N"));
var copy = directory + "-copy";
try
{
    var artifact = Path.Combine(directory, ".lake/build/lib/lean/CIL.olean");
    Directory.CreateDirectory(Path.GetDirectoryName(artifact)!);
    File.WriteAllText(artifact, "compiled artifact");
    File.WriteAllText(Path.Combine(directory, "cache-manifest.json"), System.Text.Json.JsonSerializer.Serialize(CacheFiles(directory)));
    if (!ValidCache(directory)) throw new Exception("Valid manifest rejected");
    CopyTree(directory, copy);
    if (!ValidCache(copy)) throw new Exception("Private session copy rejected");
    File.AppendAllText(artifact, "corruption");
    if (ValidCache(directory)) throw new Exception("Changed artifact accepted");
    if (!ValidCache(copy)) throw new Exception("Private session shares mutable artifacts");
    File.WriteAllText(Path.Combine(copy, "unexpected.olean"), "untracked");
    if (ValidCache(copy)) throw new Exception("Untracked artifact accepted");
    File.Delete(artifact);
    if (ValidCache(directory)) throw new Exception("Missing artifact accepted");

    var snapshot = new SortedDictionary<string, string>(StringComparer.Ordinal)
    {
        ["CIL.lean"] = "root", ["CIL/Types.lean"] = "types", ["lean-toolchain"] = "toolchain",
        ["Examples/Proofs/Add.lean"] = "proof", ["Tests/Semantics.lean"] = "test", ["proof:custom.lean"] = "custom"
    };
    var sources = LibrarySources(snapshot);
    snapshot["Examples/Proofs/Add.lean"] = "edited proof";
    snapshot["proof:custom.lean"] = "edited custom";
    if (!Same(sources, LibrarySources(snapshot))) throw new Exception("Proof edits invalidate base library");
    snapshot["CIL/Types.lean"] = "edited types";
    if (Same(sources, LibrarySources(snapshot))) throw new Exception("Source edit does not invalidate base library");
    Console.WriteLine("PASS cache corruption, missing and extra artifacts, private copy isolation and source/proof key separation");
}
finally
{
    Directory.Delete(directory, true);
    if (Directory.Exists(copy)) Directory.Delete(copy, true);
}
