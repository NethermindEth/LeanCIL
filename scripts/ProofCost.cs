#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ProofCostReport.cs
#:include Verification.cs
#:include BindingAudit.cs
#:include BindingImage.cs
#:include DeepCheckInputs.cs
#:include CertifiedLibraryDonor.cs
#:include ExportVerificationSuites.cs
#:include VerificationGroupRunner.cs
#:include VerificationSuites.cs

return ProofCostReport.Run(args);
