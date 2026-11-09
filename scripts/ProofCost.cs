#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ProofCostReport.cs

return ProofCostReport.Run(args);
