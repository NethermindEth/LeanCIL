#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include ../Extractor/ExternalIdentityEvidence.cs

using System.Text;
using System.Text.RegularExpressions;
using Nethermind.LeanCIL;

var directory = At("artifacts/ExternalIdentityEncoding");
Directory.CreateDirectory(directory);
var malformed = new ExternalIdentityEvidence();
malformed.Reference("unpaired\ud800", true);
try
{
    malformed.Emit(new StringBuilder());
    throw new InvalidOperationException("Malformed UTF-16 identity was silently replaced.");
}
catch (EncoderFallbackException) { }
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution");
var leanPath = directory + Path.PathSeparator + At(".lake/build/lib/lean");
var checker = Path.Combine(Run(["lean", "--print-prefix"]).Trim(), "bin",
    OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");

void Check(string name, string source, bool accepted, string? diagnostic = null)
{
    var path = Path.Combine(directory, name + ".lean");
    File.WriteAllText(path, source);
    var result = Execute(["lean", "--root=" + directory, "-o", Path.ChangeExtension(path, ".olean"), path],
        leanPath: leanPath);
    if ((result.Code == 0) != accepted || accepted && result.Output.Contains("sorryAx", StringComparison.Ordinal) ||
        diagnostic is not null && !result.Output.Contains(diagnostic, StringComparison.Ordinal))
        throw new InvalidOperationException(name + ": " + result.Output);
    if (accepted) Run([checker, name], leanPath: leanPath);
    Console.WriteLine("PASS external identity encoding: " + name);
}

var emitter = new ExternalIdentityEvidence();
var source = new StringBuilder("import CIL.Extraction.Translation\nset_option maxRecDepth 4096\n" +
    "namespace EncodingFixture\n");
var identities = new[]
{
    "", "ASCII", new string('a', 31) + "λ", new string('b', 30) + "漢",
    new string('c', 29) + "🚀", "embedded\0null", "quote\" and slash\\",
    "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a::" +
        "System.Boolean System.Runtime.Intrinsics.Vector256::get_IsHardwareAccelerated()"
};
foreach (var identity in identities)
{
    var reference = emitter.Reference(identity, true);
    emitter.Emit(source);
    var literal = "\"" + identity.Replace("\\", "\\\\").Replace("\"", "\\\"").Replace("\0", "\\x00") + "\"";
    source.AppendLine($"theorem {reference}_matches : {reference} = {literal} := rfl");
    source.AppendLine($"#print axioms {reference}_matches");
}
source.AppendLine("end EncodingFixture");
Check("Encoded", source.ToString(), true);
var invalid = source.ToString().Replace("⟨#[65, 83, 67, 73, 73]⟩", "⟨#[255, 83, 67, 73, 73]⟩",
    StringComparison.Ordinal);
if (invalid == source.ToString()) throw new InvalidOperationException("UTF-8 mutation did not apply.");
Check("InvalidUtf8", invalid, false, "externalIdentityChunk0_valid");

var extraction = Path.Combine(directory, "Extraction");
Run(Extract("extract", At("Examples/Assembly/bin/Examples.dll"), "Examples",
    "Examples.IntegerMath::AbsInt64(long)", extraction));
var compiled = File.ReadAllText(Path.Combine(extraction, "Extracted.lean"));
Check("CompiledHelper", compiled, true);
var identityBytes = Regex.Match(compiled, @"def externalIdentity0Bytes : ByteArray := ⟨#\[([^\]]+)\]⟩");
if (!identityBytes.Success) throw new InvalidOperationException("Missing compiled helper identity.");
var bytes = identityBytes.Groups[1].Value.Split(", ").Select(byte.Parse).ToArray();
var original = Encoding.UTF8.GetString(bytes);
var forged = original.Replace("::", ":!", StringComparison.Ordinal);
if (original == forged) throw new InvalidOperationException("Identity mutation did not apply.");
var changedBytes = string.Join(", ", Encoding.UTF8.GetBytes(forged));
var changed = compiled.Remove(identityBytes.Index, identityBytes.Length).Insert(identityBytes.Index,
    "def externalIdentity0Bytes : ByteArray := ⟨#[" + changedBytes + "]⟩");
// Give the changed bytes a valid UTF-8 proof so rejection must come from scalar call matching.
changed = Regex.Replace(changed, @"theorem externalIdentity0Bytes_valid[^\r\n]+",
    "theorem externalIdentity0Bytes_valid : externalIdentity0Bytes.IsValidUTF8 := by decide +kernel");
Check("ChangedHelper", changed, false, "Extraction.ScalarFlowValid");
