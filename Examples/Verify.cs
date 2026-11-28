#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs

// Build the sample, extract its CIL and prove the addition contract.
Run(["dotnet", "build", "Examples/Assembly", "-c", "Release"]);

using var verification = new Program();
var report = verification.Verify(
    At("Examples/Assembly/bin/Examples.dll"),
    "Examples",
    "Arithmetic::Add(ulong,ulong)",
    At("Examples/Proofs/Add.lean"),
    At("artifacts/Add"));

Console.WriteLine("Verified: " + report.theorem);
Console.WriteLine("Generated CIL and verification report: " + At("artifacts/Add"));
