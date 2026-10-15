#!/usr/bin/env dotnet
#:property PublishAot=false
#:include Verification.cs

if (args.Length < 5)
{
    Console.Error.WriteLine("Usage: dotnet run --file scripts/Verify.cs -- assembly name-or-identity entry proof output [--profile name|@file] [--theorem name] [--check] [--fresh]");
    return 2;
}

var profile = "scalar";
var theorem = "ExampleProof.correctness";
var check = false;
var fresh = false;

for (var i = 5; i < args.Length; i++)
{
    switch (args[i])
    {
        case "--fresh":
            fresh = true;
            break;

        case "--check":
            check = true;
            break;

        case "--profile" when i + 1 < args.Length:
            profile = args[++i];
            break;

        case "--theorem" when i + 1 < args.Length:
            theorem = args[++i];
            break;

        default:
            throw new ArgumentException("Unknown or incomplete option: " + args[i]);
    }
}

using var verification = new Program { freshLibrary = fresh };
var report = verification.Verify(args[0], args[1], args[2], args[3], args[4], profile, theorem, check);

Console.WriteLine((check ? "Identity checked: " : "Verified: ") + report.theorem);
return 0;
