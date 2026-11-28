#!/usr/bin/env dotnet
#:property PublishAot=false
#:include CI/VerificationTimings.cs

VerificationTimings.Run(args);
