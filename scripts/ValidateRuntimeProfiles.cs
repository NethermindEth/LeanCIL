#!/usr/bin/env dotnet
#:property PublishAot=false
#:include RuntimeProfileValidation.cs

using System.Diagnostics;

if (args.Length < 2) throw new ArgumentException("Usage: ValidateRuntimeProfiles.cs <extractor.dll> <evidence.json>...");
var output = Path.GetFullPath("artifacts/RuntimeProfileEvidence.lean");
Directory.CreateDirectory(Path.GetDirectoryName(output)!);
RuntimeProfileValidation.Check(RuntimeProfileValidation.Observations(args.Skip(1)), args[0], output);
var start = new ProcessStartInfo("lake") { UseShellExecute = false };
foreach (var argument in new[] { "env", "lean", output }) start.ArgumentList.Add(argument);
using var process = Process.Start(start) ?? throw new InvalidOperationException("Cannot start Lean.");
await process.WaitForExitAsync();
Environment.ExitCode = process.ExitCode;
