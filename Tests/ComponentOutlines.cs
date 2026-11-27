#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

// Consolidated component outline suite covering struct, receiver-loop, word-reader and saved-local outlines.
foreach (var (name, script) in new[]
{
    ("struct outlines", "Tests/StructOutlines.cs"),
    ("receiver loop outlines", "Tests/ReceiverLoopOutlines.cs"),
    ("word reader outlines", "Tests/WordReaderOutlines.cs"),
    ("saved word reader outlines", "Tests/SavedWordReaderOutlines.cs")
})
    Run(["dotnet", "run", "--file", script], streamOutput: true, progress: name);

Console.WriteLine("PASS consolidated component outlines (struct, receiver, wordreader, savedwordreader)");
