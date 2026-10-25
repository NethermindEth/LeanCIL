#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs

var root = Path.Combine(Path.GetTempPath(), "leancil-support-candidates-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
try
{
    string Source(string module, string contents)
    {
        var path = Path.Combine(root, module + ".lean");
        File.WriteAllText(path, contents);
        return path;
    }
    Source("Early", "/- import Extracted /- nested -/ -/\ntheorem early : True := True.intro\n");
    Source("Late", "theorem late : True := True.intro\n");
    Source("Dependent", "import Extracted\n");
    Source("Indirect", "public meta import Dependent\n");
    Source("Unknown", "import Missing\n");
    Source("Symbols", "import ExtractedSymbols\n");
    Source("Published", "import ImportedInterface\n");
    var first = Source("FirstProof", "import Early\nimport Indirect\nimport Unknown\n");
    var second = Source("SecondProof", "public import all Early /- nested /- comment -/ -/ import Late -- comment\n" +
        "import Symbols\nimport Published\n");
    foreach (var proofs in new[] { new[] { first, second }, new[] { second, first } })
    {
        var modules = ConsumerSupportCandidates(proofs, [root], ["ImportedInterface"], Path.Combine(root, "Toolchain"));
        if (!modules.SequenceEqual(new[] { "Early", "Late" }))
            throw new Exception("Unexpected candidate union: " + string.Join(',', modules));
    }
    Console.WriteLine("PASS candidate union is order independent and excludes transitive generated imports");
}
finally { Directory.Delete(root, true); }
