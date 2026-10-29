#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs

if (args is not ([] or ["--prepare-only"]))
    throw new ArgumentException("Usage: ExtractionEvidence.cs [--prepare-only]");
using var fixtures = new Program();
fixtures.PrepareLeanFixtures(
    "Tests.ExtractionLayout", "Tests.ExtractionParameters", "Tests.FeatureEvidence", "Tests.ScalarEvidence",
    "Tests.LayoutCoverage", "Tests.TypeTestEvidence", "Tests.ThrowEvidence", "Tests.SpanEvidence",
    "Tests.ImportEvidence", "Tests.ImportedLayouts", "Tests.StaticValueEvidence", "Tests.SpanViews",
    "Tests.MemorySpanExecution", "Tests.ConstrainedEvidence", "Tests.ManagedPointerValues", "Tests.StackAllocationEvidence",
    "Tests.StackAllocation", "Tests.PrimitiveArrays", "Tests.ArrayElementReferences", "Tests.ReadOnlyArrayReferences",
    "Tests.ExtractionGenerics", "Tests.ReferenceTests", "Tests.PointerOperations");
if (args is ["--prepare-only"]) return;
Run(["dotnet", "run", "--file", "Tests/PreparedLeanFixturesTests.cs"]);
Run(["dotnet", "run", "--file", "Tests/RejectedEvidenceTests.cs"]);
Run(["dotnet", "run", "--file", "Tests/ConstrainedResolution.cs"]);
Run(["dotnet", "run", "--file", "Tests/ConstrainedCalls.cs"]);
Run(["dotnet", "run", "--file", "Tests/ManagedDispatch.cs"]);
Run(["dotnet", "run", "--file", "Tests/NativeManagedDispatch.cs"]);
Run(["dotnet", "run", "--file", "Tests/StackAllocation.cs"]);
Run(["dotnet", "run", "--file", "Tests/PrimitiveArrays.cs"], streamOutput: true,
    progress: "Supplied primitive arrays");
Run(["dotnet", "run", "--file", "Tests/ArrayElementReferences.cs"], streamOutput: true,
    progress: "Array element references");
Run(["dotnet", "run", "--file", "Tests/ReadOnlyArrayReferences.cs"], streamOutput: true,
    progress: "Readonly array references");
Run(["dotnet", "run", "--file", "Tests/ExternalIdentityEncoding.cs"], streamOutput: true,
    progress: "UTF-8 metadata identity certificates");
foreach (var name in new[] { "LayoutEvidence", "ParameterEvidence", "GenericEvidence", "FeatureEvidence", "TypeTests", "Throws", "SpanTables", "MemorySpans", "ReferenceInstructions", "PointerOperations", "StaticValues", "StaticScalarValues", "TranslationAudit" })
    Run(["dotnet", "run", "--file", $"Tests/{name}.cs"], streamOutput: true, progress: name);
Console.WriteLine("PASS complete extraction evidence, compiled fixtures, mutations and mandatory certificate audit");
