#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

// Synthetic donor bytes exercise authentication and invalidation without running a compiler.
var root = At("artifacts/LibraryIncremental-" + Guid.NewGuid().ToString("N"));
var donor = Path.Combine(root, "donor");
Directory.CreateDirectory(donor);
using var verifier = new Program();
var current = LibrarySources(CommonInputs());
foreach (var name in current.Keys)
{
    var target = Path.Combine(donor, name);
    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
    File.Copy(At(name), target);
}
const string changed = "CIL/Replay.lean";
File.AppendAllText(Path.Combine(donor, changed), "\n-- previous source\n");
File.WriteAllText(Path.Combine(donor, "CIL/Removed.lean"), "-- removed source\n");
string[] stale = [".lake/build/lib/lean/CIL/Replay.olean", ".lake/build/ir/CIL/Replay.c",
    ".lake/build/lib/lean/CIL/Removed.olean", ".lake/build/bin/leancil-audit",
    CertifiedFingerprintsName];
string[] retained = [".lake/build/lib/lean/CIL.olean", ".lake/build/lib/lean/CIL/Types.olean",
    ".lake/build/lib/lean/CIL/Types.trace"];
foreach (var name in stale.Concat(retained))
{
    var target = Path.Combine(donor, name);
    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
    File.WriteAllText(target, "authenticated " + name);
}
string Publish()
{
    var (key, _) = verifier.LibraryIdentity(LibrarySources(CacheFiles(donor)));
    File.WriteAllText(Path.Combine(donor, "library-key.txt"), key);
    File.WriteAllText(Path.Combine(donor, "cache-manifest.json"), JsonSerializer.Serialize(CacheFiles(donor)));
    return Sha(Path.Combine(donor, "cache-manifest.json"));
}
var digest = Publish();
var destination = Path.Combine(root, "staged");
verifier.StageIncrementalLibrary(destination, donor, digest, current);
if (stale.Any(name => File.Exists(Path.Combine(destination, name))) ||
    File.Exists(Path.Combine(destination, "CIL/Removed.lean")) ||
    retained.Any(name => Sha(Path.Combine(destination, name)) != Sha(Path.Combine(donor, name))))
    throw new Exception("Incremental staging retained stale outputs or lost authenticated unaffected outputs.");
File.WriteAllText(Path.Combine(destination, retained[0]), "private mutation");
if (!File.ReadAllText(Path.Combine(donor, retained[0])).StartsWith("authenticated ", StringComparison.Ordinal))
    throw new Exception("Incremental staging shares writable bytes with donor.");
Console.WriteLine("PASS changed/deleted module invalidation, unaffected trace reuse, native/metadata reset and isolation");

void Reject(string label, string expected)
{
    try { verifier.StageIncrementalLibrary(Path.Combine(root, label), donor, digest, current); }
    catch (InvalidDataException error) when (error.Message.Contains(expected, StringComparison.Ordinal))
    {
        Console.WriteLine("PASS incremental donor rejects " + label);
        return;
    }
    throw new Exception("Incremental donor accepted " + label);
}
var oldDigest = digest;
digest = new string('0', 64);
Reject("wrong-digest", "manifest digest mismatch");
digest = oldDigest;
File.AppendAllText(Path.Combine(donor, retained[0]), "tampered");
Reject("tampered-artifact", "identity or integrity mismatch");
_ = Publish();
Reject("self-rehashed-manifest", "manifest digest mismatch");
File.AppendAllText(Path.Combine(donor, "lakefile.toml"), "\n# different build\n");
digest = Publish();
Reject("changed-configuration", "build configuration changed");
File.Copy(At("lakefile.toml"), Path.Combine(donor, "lakefile.toml"), true);
digest = Publish();
File.WriteAllText(Path.Combine(donor, "library-key.txt"), "another-runtime-or-toolchain");
File.WriteAllText(Path.Combine(donor, "cache-manifest.json"), JsonSerializer.Serialize(CacheFiles(donor)));
digest = Sha(Path.Combine(donor, "cache-manifest.json"));
Reject("incompatible-toolchain", "identity or integrity mismatch");
