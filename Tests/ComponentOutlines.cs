#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs

// Consolidated component outline suite covering struct, receiver-loop, word-reader and saved-local outlines.
RunFixturesConcurrently(
[
    ("Tests/StructOutlines.cs", "struct outlines"),
    ("Tests/ReceiverLoopOutlines.cs", "receiver loop outlines"),
    ("Tests/WordReaderOutlines.cs", "word reader outlines"),
    ("Tests/SavedWordReaderOutlines.cs", "saved word reader outlines")
]);

Console.WriteLine("PASS consolidated component outlines (struct, receiver, wordreader, savedwordreader)");
