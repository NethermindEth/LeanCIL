#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs

if (args is not ([] or ["--prepare-only"]))
    throw new ArgumentException("Usage: DispatchEvidence.cs [--prepare-only]");
using var fixtures = new Program();
fixtures.PrepareLeanFixtures("Tests.ConstrainedEvidence", "Tests.BodyEncoding", "Tests.ConstantCalls",
    "Tests.NativeMethodTables", "Tests.StackAllocation", "Tests.StackAllocationEvidence");
if (args is ["--prepare-only"]) return;
Run(["dotnet", "run", "--file", "Tests/ConstrainedResolution.cs"], streamOutput: true,
    progress: "ConstrainedResolution");
Run(["dotnet", "run", "--file", "Tests/ConstrainedCalls.cs"], streamOutput: true, progress: "ConstrainedCalls");
Run(["dotnet", "run", "--file", "Tests/ManagedDispatch.cs"], streamOutput: true, progress: "ManagedDispatch");
Run(["dotnet", "run", "--file", "Tests/NativeManagedDispatch.cs"], streamOutput: true,
    progress: "NativeManagedDispatch");
Run(["dotnet", "run", "--file", "Tests/StackAllocation.cs"], streamOutput: true, progress: "StackAllocation");
Run(["dotnet", "run", "--file", "Tests/RuntimeModelInventory.cs"], streamOutput: true,
    progress: "Runtime model catalog");
Run(["dotnet", "run", "--file", "Tests/CompilerCoverage.cs"], streamOutput: true,
    progress: "Pinned compiler coverage");
Console.WriteLine("PASS dispatch, constant calls, stack allocation and pinned compiler coverage");
