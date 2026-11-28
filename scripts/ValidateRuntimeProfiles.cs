#!/usr/bin/env dotnet
#:property PublishAot=false
#:include CI/RuntimeProfileValidation.cs
#:include Verification/Verification.cs
#:include Checking/DeepChecks.cs
#:include Checking/FailureReports.cs
#:include Checking/LeanDiagnostics.cs
#:include Checking/BindingImage.cs
#:include Checking/DeepCheckInputs.cs

if (args.Length < 2) throw new ArgumentException("Usage: ValidateRuntimeProfiles.cs <extractor.dll> <evidence.json>...");
var output = Path.GetFullPath("artifacts/RuntimeProfileEvidence.lean");
Directory.CreateDirectory(Path.GetDirectoryName(output)!);
RuntimeProfileValidation.Check(RuntimeProfileValidation.Observations(args.Skip(1)), args[0], output);
// A nonzero exit or an internal error in Lean's output fails the validation.
Run(["lake", "env", "lean", output], Environment.CurrentDirectory, streamOutput: true);
