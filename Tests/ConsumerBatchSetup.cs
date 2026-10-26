#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ConsumerTraceDirectory.cs
#:include ConsumerBatchOutcomes.cs

using System.Text.Json;

var separate = args.Contains("--separate", StringComparer.Ordinal);
var cli = new[] { "dotnet", args.FirstOrDefault(argument => argument != "--separate") ?? ExtractorPath };
var directory = Path.GetFullPath(At("artifacts/ConsumerBatchSetup-" + Guid.NewGuid().ToString("N")));
var root = Path.Combine(directory, "Package");
Directory.CreateDirectory(Path.Combine(root, "Client"));
var revision = Run(["git", "rev-parse", "HEAD"]).Trim();
File.WriteAllText(Path.Combine(root, "lakefile.toml"),
    "name = \"consumer\"\n[[require]]\nname = \"leancil\"\ngit = " +
    JsonSerializer.Serialize(Root.Replace('\\', '/')) + "\nrev = " + JsonSerializer.Serialize(revision) +
    "\n[[lean_lib]]\nname = \"Client\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(root, "lean-toolchain"));
Run(["lake", "update"], root);
File.WriteAllText(Path.Combine(root, "Client", "Shared.lean"), """
    import Extracted
    import CIL.Semantics
    namespace Client
    theorem execution (x y : CIL.W64) (memory : CIL.Memory) :
        CIL.invoke Extracted.program 4 0 [.i64 x, .i64 y] memory =
          some (memory, [.i64 (x + y)]) := by rfl
    #print axioms execution
    end Client
    """);
var proof = Path.Combine(root, "Proof.lean");
File.WriteAllText(proof, """
    import Client.Shared
    namespace ExampleProof
    theorem correctness (x y : CIL.W64) (memory : CIL.Memory) :
        CIL.invoke Extracted.program 4 0 [.i64 x, .i64 y] memory =
          some (memory, [.i64 (x + y)]) := Client.execution x y memory
    #print axioms correctness
    end ExampleProof
    """);
var alternate = Path.Combine(root, "ProofAlternate.lean");
File.WriteAllText(alternate, File.ReadAllText(proof).Replace("namespace ExampleProof", "namespace AlternateProof")
    .Replace("end ExampleProof", "end AlternateProof"));
var outputs = new[] { "A", "B", "C" }.Select(name => Path.Combine(directory, name)).ToArray();
Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"), "InitializedTypes::Add(ulong,ulong)", outputs[0],
    "--assume-initialized", "Examples.InitializedTypes"]);
Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"), "Arithmetic::Add(ulong,ulong)", outputs[1]]);
Run([.. cli, "extract", At("Examples/Assembly/bin/Examples.dll"), "Arithmetic::WrongAdd(ulong,ulong)", outputs[2]]);
CheckConsumerBatchOutcomes(cli, root, proof, outputs[0], outputs[1], outputs[2], alternate, separate);
