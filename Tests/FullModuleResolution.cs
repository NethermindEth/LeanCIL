#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include ../scripts/Consumer/FullModuleResolution.cs
#:include ../scripts/CI/ExportVerificationSuites.cs

ExportCaseLedger completed = new("resolution");

using Program paths = new();
string root = At($"artifacts/FullModuleResolution-\U00010400-{Guid.NewGuid():N}");
Directory.CreateDirectory(root);
string library = Path.GetFullPath(Path.Combine(paths.Toolchain, "lib", "lean"));
SortedDictionary<string, string> accepted = new(StringComparer.Ordinal)
{
    ["Init"] = Path.Combine(library, "Init.olean"),
    ["Lean.Elab"] = Path.Combine(library, "Lean", "Elab.olean")
};
// Lean joins search roots verbatim, so the root's spelling (separators, "." segments, drive case) must not matter.
string spelled = paths.Toolchain + "/lib/./lean";
paths.CheckFullResolution(root, spelled, accepted);
completed.CompleteCase("resolution.same-files");
Console.WriteLine("PASS full-verification resolution accepts the same files under another root spelling");

SortedDictionary<string, string> swapped = new(StringComparer.Ordinal) { ["Init"] = accepted["Lean.Elab"] };
string? rejection = null;
try { paths.CheckFullResolution(root, spelled, swapped); }
catch (InvalidOperationException error) { rejection = error.Message; }
if (rejection?.Contains("Full-verification resolved module path changed: Init", StringComparison.Ordinal) != true)
    throw new InvalidOperationException("Full-verification resolution accepted a module loaded from a different file: " + rejection);
Console.WriteLine("PASS full-verification resolution rejects a module loaded from a different file");
completed.CompleteCase("resolution.changed-file");

string artifact = Path.Combine(root, "Caller.olean");
File.WriteAllBytes(artifact, [1, 2, 3, 4]);
SortedDictionary<string, string> hashed = FullArtifactHashes([artifact]);
DateTime written = File.GetLastWriteTimeUtc(artifact);
File.WriteAllBytes(artifact, [1, 2, 3, 5]);
File.SetLastWriteTimeUtc(artifact, written);
string? rewritten = null;
try { RequireFullArtifactHashes(hashed); }
catch (InvalidDataException error) { rewritten = error.Message; }
if (rewritten?.Contains("Full-verification source or compiled artifact changed: " + artifact,
    StringComparison.Ordinal) != true)
    throw new InvalidOperationException("Full verification accepted a same-length artifact rewrite: " + rewritten);
Console.WriteLine("PASS full verification rejects a same-length caller artifact rewrite with its write time restored");
completed.CompleteCase("resolution.rewritten-artifact");
completed.Finish();
