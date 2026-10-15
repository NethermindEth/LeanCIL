#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

Run(["lake", "build", "Tests.ExtractionLayout", "Tests.ExtractionParameters", "Tests.FeatureEvidence", "Tests.LayoutCoverage"],
    streamOutput: true, progress: "Extraction validator regressions");
foreach (var name in new[] { "LayoutEvidence", "ParameterEvidence", "GenericEvidence", "FeatureEvidence", "TranslationAudit" })
    Run(["dotnet", "run", "--file", $"Tests/{name}.cs"], streamOutput: true, progress: name);
Console.WriteLine("PASS complete extraction evidence, compiled fixtures, mutations and mandatory certificate audit");
