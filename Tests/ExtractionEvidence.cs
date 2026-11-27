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
    throw new ArgumentException("Usage: ExtractionEvidence.cs [--prepare-only]");
using var fixtures = new Program();
fixtures.PrepareLeanFixtures(
    "Tests.MetadataBuilder", "Tests.BodyEncoding", "Tests.ExtractionLayout", "Tests.ExtractionParameters",
    "Tests.FeatureEvidence", "Tests.CallDecoding",
    "Tests.ScalarEvidence", "Tests.CoreStringLength", "Tests.CoreExceptionHResult", "Tests.CoreMonitor",
    "Tests.CoreHeaderPointer", "Tests.PercentRuntime",
    "Tests.LayoutCoverage", "Tests.TypeTestEvidence", "Tests.ThrowEvidence", "Tests.SpanEvidence",
    "Tests.ImportEvidence", "Tests.ImportedLayouts", "Tests.AssemblyPins", "Tests.StaticValueEvidence", "Tests.SpanViews",
    "Tests.MemorySpanExecution", "Tests.ManagedPointerValues", "Tests.PrimitiveArrays", "Tests.ArrayElementReferences",
    "Tests.ReadOnlyArrayReferences", "Tests.ExtractionGenerics", "Tests.ReferenceTests", "Tests.PointerOperations",
    "Tests.Objects");
if (args is ["--prepare-only"]) return;
(string Script, string Progress)[] fixturesToRun =
[
    ("Tests/PreparedLeanFixturesTests.cs", "PreparedLeanFixturesTests"),
    ("Tests/RejectedEvidenceTests.cs", "RejectedEvidenceTests"),
    ("Tests/PrimitiveArrays.cs", "Supplied primitive arrays"),
    ("Tests/ArrayElementReferences.cs", "Array element references"),
    ("Tests/ReadOnlyArrayReferences.cs", "Readonly array references"),
    ("Tests/SpanHomeReads.cs", "Span locals read through their addresses"),
    ("Tests/ExternalIdentityEncoding.cs", "UTF-8 metadata identity certificates"),
    .. new[]
    {
        "LayoutEvidence", "ParameterEvidence", "GenericEvidence", "FeatureEvidence", "TypeTests", "Throws",
        "SpanTables", "MemorySpans", "ReferenceInstructions", "PointerOperations", "Objects", "StaticValues",
        "StaticScalarValues", "TranslationAudit", "MetadataDifferential", "Guards", "CallSiteAgreement"
    }.Select(name => ($"Tests/{name}.cs", name))
];
RunFixturesConcurrently(fixturesToRun);
Console.WriteLine("PASS complete extraction evidence, compiled fixtures, mutations and mandatory certificate audit");
