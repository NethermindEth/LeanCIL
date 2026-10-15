#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

var cli = new[] { "dotnet", args.Length == 0 ? ExtractorPath : Path.GetFullPath(args[0]) };
var root = Path.GetFullPath(At("artifacts/ConsumerPackage"));
var output = At("artifacts/ConsumerExtraction");
Directory.CreateDirectory(Path.Combine(root, "Client"));
var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
File.WriteAllText(Path.Combine(root, "lakefile.toml"),
    $"name = \"consumer\"\n[[require]]\nname = \"leancil\"\ngit = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}\nrev = \"{revision}\"\n[[lean_lib]]\nname = \"Client\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(root, "lean-toolchain"), true);
const string shared = """
import Extracted
import CIL.Semantics
namespace Client
theorem execution (x y : CIL.W64) (memory : CIL.Memory) :
    CIL.invoke Extracted.program 4 0 [.i64 x, .i64 y] memory =
      some (memory, [.i64 (x + y)]) := by rfl
end Client
""";
var sharedPath = Path.Combine(root, "Client", "Shared.lean");
File.WriteAllText(sharedPath, shared);
var proof = Path.Combine(root, "Proof.lean");
File.WriteAllText(proof, """
import Client.Shared
namespace ExampleProof
theorem correctness (x y : CIL.W64) (memory : CIL.Memory) :
    CIL.invoke Extracted.program 4 0 [.i64 x, .i64 y] memory =
      some (memory, [.i64 (x + y)]) := Client.execution x y memory
end ExampleProof
""");
Run(["lake", "update"], root);
var staleCache = Path.Combine(root, ".lake", "build", "lib", "lean", "Client");
Directory.CreateDirectory(staleCache);
File.WriteAllText(Path.Combine(staleCache, "Shared.olean"), "Not a valid compiled module; consumer caches must not be used.");
Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"), "InitializedTypes::Add(ulong,ulong)", output,
    "--assume-initialized", "Examples.InitializedTypes"]);

void Verify(params string[] options)
{
    var text = Run([.. cli, "verify", output, .. options]);
    if (!text.Contains("Verified: ExampleProof.correctness")) throw new InvalidOperationException(text);
}
void Reject(string marker, params string[] options)
{
    var result = Execute([.. cli, "verify", output, .. options]);
    if (result.Code != 1 || !result.Output.Contains(marker) || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Expected consumer proof rejection: " + result.Output);
}
Verify("--proof", proof, "--proof-root", root);
var first = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
var inputs = first.GetProperty("inputs");
if (first.GetProperty("initializedTypes")[0].GetString() != "Examples.InitializedTypes")
    throw new InvalidOperationException("Consumer report dropped initialization preconditions.");
if (!inputs.TryGetProperty("consumer:" + sharedPath, out _) ||
    !inputs.TryGetProperty("consumer:" + Path.Combine(root, "lake-manifest.json"), out _) ||
    inputs.GetProperty("revision:leancil").GetString() != revision)
    throw new InvalidOperationException("Missing consumer source or dependency identity.");
Console.WriteLine("PASS external consumer package and transitive dependency importing Extracted");

// A changed imported proof must fail, regardless of any existing consumer caches.
File.WriteAllText(sharedPath, shared.Replace("x + y", "x - y"));
Reject("error:");
File.WriteAllText(sharedPath, shared + "\n-- Imported-source identity changed.\n");
Verify();
var restored = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (inputs.GetProperty("consumer:" + sharedPath).GetString() ==
    restored.GetProperty("inputs").GetProperty("consumer:" + sharedPath).GetString())
    throw new InvalidOperationException("Imported source edit did not change report identity.");
Console.WriteLine("PASS incorrect imported lemma rejected, settings reused and source hashes updated");

File.WriteAllText(sharedPath, shared.Replace("theorem execution", "axiom execution").Replace(" := by rfl", ""));
Reject("Unapproved proof axioms");
File.WriteAllText(sharedPath, shared);
Console.WriteLine("PASS axiom hidden in imported consumer module rejected");

File.WriteAllText(Path.Combine(root, "Extracted.lean"), "-- stale extraction");
Reject("reserved");
File.Delete(Path.Combine(root, "Extracted.lean"));
var framework = Path.Combine(root, ".lake/packages/leancil/CIL/Types.lean");
var frameworkSource = File.ReadAllText(framework);
try
{
    File.AppendAllText(framework, "\n-- changed framework\n");
    Reject("differ from the verifier");
}
finally { File.WriteAllText(framework, frameworkSource); }
Console.WriteLine("PASS stale generated modules and mismatched framework sources rejected");
