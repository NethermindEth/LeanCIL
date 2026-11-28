#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

// Consolidated component outline suite covering struct, receiver-loop, word-reader and saved-local outlines.
RunFixturesConcurrently(
[
    ("Tests/StructOutlines.cs", "struct outlines"),
    ("Tests/ReceiverLoopOutlines.cs", "receiver loop outlines"),
    ("Tests/WordReaderOutlines.cs", "word reader outlines"),
    ("Tests/SavedWordReaderOutlines.cs", "saved word reader outlines")
]);

Console.WriteLine("PASS consolidated component outlines (struct, receiver, wordreader, savedwordreader)");
