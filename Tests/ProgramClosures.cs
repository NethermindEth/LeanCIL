#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

// Entry uses AddTwo's contract after relocation. Equal executable bodies may share an index,
// while each decoded call still has to name the target's metadata token.
var fixture = At("Tests/ProgramClosures");
Run(["dotnet", "build", Path.Combine(fixture, "Assembly/ProgramClosures.csproj"), "-c", "Release"]);
using var verification = new Program();
verification.Verify(Path.Combine(fixture, "Assembly/bin/ProgramClosures.dll"), "ProgramClosures",
    "System.UInt64 Closure::Entry(System.UInt64)", Path.Combine(fixture, "Proof.lean"),
    At("artifacts/ProgramClosures"));
Console.WriteLine("PASS AddTwo's contract relocates across equal bodies and decoding rejects mismatched method tokens");
