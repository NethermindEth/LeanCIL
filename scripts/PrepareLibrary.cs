#!/usr/bin/env dotnet
#:property PublishAot=false
#:include Verification.cs

if (args is not [var directory])
    throw new ArgumentException("Usage: dotnet run --file scripts/PrepareLibrary.cs -- <output-directory>");

using var verifier = new Program { freshLibrary = true };
var digest = verifier.PrepareLibrary(directory);
Console.WriteLine("Certified library manifest SHA256: " + digest);
if (Environment.GetEnvironmentVariable("GITHUB_OUTPUT") is { Length: > 0 } output)
    File.AppendAllText(output, "manifest-sha256=" + digest + Environment.NewLine);
