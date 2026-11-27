#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs

if (args is not ([] or ["--prepare-only"]))
    throw new ArgumentException("Usage: DispatchEvidence.cs [--prepare-only]");
using var fixtures = new Program();
fixtures.PrepareLeanFixtures("Tests.ConstrainedEvidence", "Tests.MetadataBuilder",
    "Tests.BodyEncoding", "Tests.ConstantCalls",
    "Tests.NativeMethodTables", "Tests.StackAllocation", "Tests.StackAllocationEvidence");
if (args is ["--prepare-only"]) return;
RunFixturesConcurrently(
[
    ("Tests/ConstrainedResolution.cs", "ConstrainedResolution"),
    ("Tests/ConstrainedCalls.cs", "ConstrainedCalls"),
    ("Tests/ManagedDispatch.cs", "ManagedDispatch"),
    ("Tests/NativeManagedDispatch.cs", "NativeManagedDispatch"),
    ("Tests/StackAllocation.cs", "StackAllocation"),
    ("Tests/RuntimeModelInventory.cs", "Runtime model catalog"),
    ("Tests/CompilerCoverage.cs", "Pinned compiler coverage")
]);
Console.WriteLine("PASS dispatch, constant calls, stack allocation and pinned compiler coverage");
