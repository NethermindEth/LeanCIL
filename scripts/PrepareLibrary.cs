#!/usr/bin/env dotnet
#:property PublishAot=false
#:include Verification.cs

if (args is not ([_] or [_, "--reuse"]))
    throw new ArgumentException("Usage: dotnet run --file scripts/PrepareLibrary.cs -- <output-directory> [--reuse]");
var directory = args[0];
var reuse = args.Length == 2;

// The producer certifies a from-source build, never a previously supplied library.
Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY", null);
using var verifier = new Program { freshLibrary = true };
// --reuse accepts a library restored into the destination, or replaces it with a fresh build.
var digest = reuse ? verifier.ReusePreparedLibrary(directory) : null;
if (digest is not null)
    Console.WriteLine("Reusing certified library for identical sources and toolchain");
else
{
    if (reuse && Directory.Exists(directory)) Directory.Delete(directory, true);
    digest = verifier.PrepareLibrary(directory);
}
Console.WriteLine("Certified library manifest SHA256: " + digest);
if (Environment.GetEnvironmentVariable("GITHUB_OUTPUT") is { Length: > 0 } output)
    File.AppendAllText(output, "manifest-sha256=" + digest + Environment.NewLine);
