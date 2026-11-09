#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.RegularExpressions;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/StructOutlines");
Directory.CreateDirectory(root);
string[] Cli(params string[] arguments) => ["dotnet", ExtractorPath, .. arguments];
var extraction = Path.Combine(root, "ExchangeAdd");
Run(Extract("extract", assembly, "Examples", "OutlineCounters::ExchangeAdd(ulong)", extraction));
var outline = Path.Combine(root, "Proof.lean");
File.Delete(outline);
Run(Cli("new-proof", extraction, outline));
var source = File.ReadAllText(outline);
if (source.Contains("-- not outlined:", StringComparison.Ordinal))
    throw new InvalidOperationException("The interleaved struct field accesses were not outlined:\n" + source);
source = Regex.Replace(source, @"(def Precondition[\s\S]*?: Prop :=) sorry", "$1 True");
source = Regex.Replace(source, @"(def Postcondition[\s\S]*?: Prop :=) sorry",
    "$1\n  result = (value + outlineCountersSecond + 1) + (value + outlineCountersSecond) ∧\n" +
    "  Contents final outlineCounters 8 [value + outlineCountersSecond + 1] ∧\n" +
    "  Contents final (outlineCounters.element 1 8) 8 [value + outlineCountersSecond]");
source = source.Replace("case postcondition => sorry", "case postcondition => exact ⟨rfl, held3, kept3Field8⟩",
    StringComparison.Ordinal);
File.WriteAllText(outline, source);
Run(Cli("verify", extraction, "--proof", outline));
var wrong = Path.Combine(root, "WrongExchangeAdd");
Run(Extract("extract", assembly, "Examples", "OutlineCounters::WrongExchangeAdd(ulong)", wrong));
var wrongProof = Path.Combine(root, "WrongProof.lean");
File.WriteAllText(wrongProof, Regex.Replace(source, @"\Aimport Extracted\.\w+", "import Extracted"));
var rejected = Execute(Cli("verify", wrong, "--proof", wrongProof));
if (rejected.Code == 0 || !rejected.Output.Contains("Stage: proof checking", StringComparison.Ordinal) ||
    File.Exists(Path.Combine(wrong, "verified.json")))
    throw new InvalidOperationException("Incorrect struct mutation accepted:\n" + rejected.Output);
Console.WriteLine("PASS interleaved struct fields, repeated stores, preserved contents and mutation rejection");

var narrow = Path.Combine(root, "Narrow");
Run(Extract("extract", assembly, "Examples", "NarrowTotals::WriteRead(uint)", narrow));
var narrowProof = Path.Combine(root, "Narrow.lean");
File.Delete(narrowProof);
Run(Cli("new-proof", narrow, narrowProof));
var narrowSource = File.ReadAllText(narrowProof);
if (narrowSource.Contains("-- not outlined:", StringComparison.Ordinal))
    throw new InvalidOperationException("Narrow field accesses were not outlined:\n" + narrowSource);
narrowSource = Regex.Replace(narrowSource, @"(def Precondition[\s\S]*?: Prop :=) sorry", "$1 True");
narrowSource = Regex.Replace(narrowSource, @"(def Postcondition[\s\S]*?: Prop :=) sorry",
    "$1\n  result = (value.setWidth 8).setWidth 32 + (value.setWidth 16).signExtend 32 ∧\n" +
    "  Contents final (narrowTotals.element 1 4) 4 [result]");
narrowSource = narrowSource.Replace("case postcondition => sorry",
    "case postcondition =>\n    constructor\n" +
    "    · simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff]\n" +
    "      congr 1\n      congr 1\n      ext index bound\n" +
    "      simp [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend, bound] <;> omega\n" +
    "    · exact held3", StringComparison.Ordinal);
File.WriteAllText(narrowProof, narrowSource);
Run(Cli("verify", narrow, "--proof", narrowProof));
Console.WriteLine("PASS byte, signed short and 32-bit struct fields with truncating stores");

var read = Path.Combine(root, "ReadSum");
Run(Extract("extract", assembly, "Examples", "NarrowTotals::ReadSum()", read));
var readProof = Path.Combine(root, "ReadSum.lean");
File.Delete(readProof);
Run(Cli("new-proof", read, readProof));
var readSource = File.ReadAllText(readProof);
if (readSource.Contains("-- not outlined:", StringComparison.Ordinal))
    throw new InvalidOperationException("Initial narrow field contents were not outlined:\n" + readSource);
readSource = Regex.Replace(readSource, @"(def Precondition[\s\S]*?: Prop :=) sorry", "$1 True");
readSource = Regex.Replace(readSource, @"(def Postcondition[\s\S]*?: Prop :=) sorry",
    "$1\n  final = initial ∧ result = narrowTotalsSmall.setWidth 32 +\n" +
    "    narrowTotalsSigned.signExtend 32 + narrowTotalsCount");
readSource = readSource.Replace("case postcondition => sorry", "case postcondition => exact ⟨rfl, rfl⟩",
    StringComparison.Ordinal);
File.WriteAllText(readProof, readSource);
Run(Cli("verify", read, "--proof", readProof));
Console.WriteLine("PASS read-only initial narrow field contents and signed extension");
