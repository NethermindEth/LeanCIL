#!/usr/bin/env dotnet
#:property PublishAot=false
#:include VerificationGroupRunner.cs

using System.Text.Json;

var suites = JsonSerializer.Deserialize<string[]>(Environment.GetEnvironmentVariable("VERIFICATION_SUITES")
    ?? throw new ArgumentException("VERIFICATION_SUITES is required"))
    ?? throw new ArgumentException("Expected a suite array");
return await VerificationGroupRunner.Run(
    ["dotnet", "artifacts/verification-fixtures/Test/Test.dll"], suites, "artifacts");
