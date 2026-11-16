#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

// Closure::AddTwo's contract is proved once over the closure of AddTwo and carried to the extraction and to two
// programs built from its records, where Entry applies it. Proof.lean also refutes a relocation into a program with
// other bytes at an index AddTwo links to, and one sending AddTwo and Bump, whose bodies differ, to one index; it
// fails when any of its theorems depends on sorryAx.
var fixture = At("Tests/ProgramClosures");
Run(["dotnet", "build", Path.Combine(fixture, "Assembly/ProgramClosures.csproj"), "-c", "Release"]);
using var verification = new Program();
verification.Verify(Path.Combine(fixture, "Assembly/bin/ProgramClosures.dll"), "ProgramClosures",
    "System.UInt64 Closure::Entry(System.UInt64)", Path.Combine(fixture, "Proof.lean"), At("artifacts/ProgramClosures"));
Console.WriteLine("PASS a summary of AddTwo proved over its closure applies in the extraction, at other indices and " +
    "with its identical callees at one index; other bytes and differing bodies at one index are refuted");
