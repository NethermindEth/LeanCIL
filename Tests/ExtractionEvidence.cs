#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

Run(["lake", "build", "Tests.ExtractionLayout", "Tests.ExtractionParameters", "Tests.FeatureEvidence", "Tests.ScalarEvidence", "Tests.LayoutCoverage", "Tests.TypeTestEvidence", "Tests.ThrowEvidence", "Tests.SpanEvidence", "Tests.ImportEvidence", "Tests.ImportedLayouts", "Tests.StaticValueEvidence"],
    streamOutput: true, progress: "Extraction validator regressions");
Run(["lake", "build", "Tests.SpanViews", "Tests.MemorySpanExecution"]);
foreach (var name in new[] { "LayoutEvidence", "ParameterEvidence", "GenericEvidence", "FeatureEvidence", "TypeTests", "Throws", "SpanTables", "MemorySpans", "StaticValues", "StaticScalarValues", "TranslationAudit" })
    Run(["dotnet", "run", "--file", $"Tests/{name}.cs"], streamOutput: true, progress: name);
Console.WriteLine("PASS complete extraction evidence, compiled fixtures, mutations and mandatory certificate audit");
