#!/usr/bin/env dotnet
#:property PublishAot=false
#:include Verification.cs
#:include ConsumerVerification.cs
#:include LeanDiagnostics.cs

if (args is not ([_] or [_, "--reuse", _] or [_, "--extend", _, _] or [_, "--incremental", _, _]))
    throw new ArgumentException("Usage: PrepareLibrary.cs <output-directory> " +
        "[--reuse <trusted-manifest-sha256> | --extend <certified-base> <trusted-manifest-sha256> | " +
        "--incremental <certified-base> <trusted-manifest-sha256>]");
var directory = args[0];
var trustedDigest = args.Length == 3 ? args[2] : null;

// Fresh production must not inherit a supplied library from a consumer's environment.
Environment.SetEnvironmentVariable("LEANCIL_CERTIFIED_LIBRARY", null);
var incremental = args.Length == 4 && args[1] == "--incremental";
if (args.Length == 1 || incremental) directory = RequireEmptyLibraryDestination(directory);
using var verifier = new Program
{
    freshLibrary = true,
    incrementalLibrary = incremental ? args[2] : null,
    incrementalDigest = incremental ? args[3] : null
};
if (args.Length == 1 || incremental) verifier.PrepareCertifiedFingerprints();
// The reuse digest must come from a trusted producer, independently of the restored files.
var digest = args.Length == 4 && !incremental ? verifier.ExtendPreparedLibrary(directory, args[2], args[3])
    : verifier.PrepareLibrary(directory, trustedDigest);
if (trustedDigest is not null)
    Console.WriteLine("Reusing certified library for identical sources and toolchain");
Console.WriteLine("Certified library manifest SHA256: " + digest);
if (Environment.GetEnvironmentVariable("GITHUB_OUTPUT") is { Length: > 0 } output)
    File.AppendAllText(output, "manifest-sha256=" + digest + Environment.NewLine);
