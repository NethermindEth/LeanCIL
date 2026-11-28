#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ProofCost/ProofCostReport.cs
#:include Verification/Verification.cs
#:include Checking/DeepChecks.cs
#:include Checking/FailureReports.cs
#:include Checking/LeanDiagnostics.cs
#:include Checking/BindingImage.cs
#:include Checking/DeepCheckInputs.cs
#:include CI/CertifiedLibraryDonor.cs
#:include CI/ExportVerificationSuites.cs
#:include CI/VerificationGroupRunner.cs
#:include CI/VerificationSuites.cs

return ProofCostReport.Run(args);
