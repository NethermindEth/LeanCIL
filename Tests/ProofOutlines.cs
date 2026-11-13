#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Text.Json;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

string? group = null;
string[]? cases = null;
var list = false;
for (var index = 0; index < args.Length; index++)
{
    if (args[index] == "--list") list = true;
    else if (args[index] == "--group" && index + 1 < args.Length) group = args[++index];
    // A focused run of the named cases of the group; the suites run each whole group.
    else if (args[index] == "--case" && index + 1 < args.Length) cases = args[++index].Split(',');
    else throw new ArgumentException(
        "Usage: ProofOutlines.cs --group control|objects|buffers [--case name[,name...]] [--list]");
}
if (group is not (null or "control" or "objects" or "buffers") || group is null && !list)
    throw new ArgumentException("Choose --group control|objects|buffers, or --list for every group");
// A generated starting proof must elaborate with only its holes open, and verification must refuse it
// until every hole is filled; otherwise an author could mistake the outline for a proof.
// Each selected method has an independent extraction; the straight-line
// methods cover `bool`, narrow and array parameters and a `bool` result, the indexed loops reading and storing
// array elements, the loops slicing a span local made from a span or an array argument, and the object methods
// `this`, field loads and stores, an object result, calls and a loop over a `callvirt`.
var catalog = new (string Name, string Selector, string Group)[]
{
    ("Countdown", "Loops::Countdown(uint)", "control"),
    ("FillWords", "Loops::FillWords(ulong&,ulong,int)", "control"),
    ("CountUntil", "Loops::CountUntil(uint,uint)", "control"),
    ("CountCalls", "Loops::CountCalls(uint)", "control"),
    ("SpanDrain", "Loops::Drain(System.ReadOnlySpan`1<System.Int32>)", "control"),
    ("SpanAllZero", "Loops::AllZero(System.ReadOnlySpan`1<System.UInt32>)", "control"),
    ("SpanSum", "Loops::Sum(System.ReadOnlySpan`1<System.UInt64>)", "control"),
    ("TallyTwice", "Loops::TallyTwice(uint)", "control"),
    ("TwoStructs", "Loops::TwoStructs(uint)", "control"),
    ("InnerCount", "Loops::InnerCount(Examples.Loops/Outer,uint)", "control"),
    ("FillWordsDown", "Loops::FillWordsDown(ulong&,ulong,int)", "control"),
    ("CopyUntilZero", "Loops::CopyUntilZero(System.ReadOnlySpan`1<System.UInt32>,uint&)", "control"),
    ("Choose", "Arithmetic::Choose(bool,ulong,ulong)", "control"),
    ("Narrow", "Arguments::Narrow(byte)", "control"),
    ("ReverseI16", "Bits::ReverseI16(short)", "control"),
    ("PowerU32", "Bits::PowerU32(uint)", "control"),
    ("Deposit", "Account::Deposit(System.UInt64)", "objects"),
    ("Headroom", "Account::get_Headroom()", "objects"),
    ("SetLimit", "Objects::SetLimit(Examples.Account,System.UInt32)", "objects"),
    ("Replace", "Objects::Replace(Examples.Account,System.UInt64)", "objects"),
    ("SecondValue", "Objects::SecondValue(Examples.Node)", "objects"),
    ("Link", "Objects::Link(Examples.Node,Examples.Node)", "objects"),
    ("LinkBoth", "Objects::LinkBoth(Examples.Node,Examples.Node,Examples.Node)", "objects"),
    // Its nodes are named like the hypotheses and memories the proof introduces, which must not capture them.
    ("Relink", "Objects::Relink(Examples.Node,Examples.Node,Examples.Node)", "objects"),
    ("FirstPresent", "Objects::FirstPresent(Examples.Account,Examples.Account)", "objects"),
    ("DepositBoth", "Objects::DepositBoth(Examples.Account,Examples.Account,System.UInt64)", "objects"),
    ("DepositTimes", "Objects::DepositTimes(Examples.Account,System.UInt64,System.UInt32)", "objects"),
    ("DepositFrom", "Objects::DepositFrom(Examples.Account,Examples.Account,System.UInt32)", "objects"),
    ("Withdraw", "Objects::Withdraw(Examples.Account,System.UInt64)", "objects"),
    ("LinkedValue", "Objects::LinkedValue(Examples.Node,Examples.Node)", "objects"),
    ("IsIdle", "ItemPool::IsIdle(Examples.PooledItem)", "objects"),
    // A field tested against a small constant, in a signed, an equality and an unsigned branch.
    ("BelowFive", "Gauge::BelowFive()", "objects"),
    ("IsFive", "Gauge::IsFive()", "objects"),
    ("UnderFive", "Objects::UnderFive(Examples.Account)", "objects"),
    // The same tests of words over a loop, a branching helper and straight-line code.
    ("CountToFive", "Loops::CountToFive(int)", "control"),
    ("CountUpToFive", "Loops::CountUpToFive(uint)", "control"),
    ("ReachFive", "Loops::ReachFive(uint)", "control"),
    ("AtLeastFive", "Arithmetic::AtLeastFive(int)", "control"),
    ("AtMostFive", "Arithmetic::AtMostFive(uint)", "control"),
    ("FiveToOne", "Arithmetic::FiveToOne(int)", "control"),
    ("Floored", "Gauge::Floored(int)", "control"),
    // A static helper that tests its word arguments gets a contract stub: its result returned, stored into a
    // field after the call, and returned by a caller over words alone.
    ("HelperResult", "Gauge::Current()", "objects"),
    ("HelperStore", "Gauge::Settle()", "objects"),
    ("HelperWords", "Gauge::Smaller(int,int)", "control"),
    // A helper that throws on one side of its test, and one that only computes, each from a caller over words.
    ("HelperThrows", "Gauge::Bounded(int,int)", "control"),
    ("HelperComputes", "Gauge::Twice(int)", "control"),
    // A helper's result kept in a numeric local, by a caller over an object and by one over words alone, whose
    // frame makes its statement speak of any well-formed memory.
    ("HelperLocal", "Gauge::Slack()", "objects"),
    ("HelperWordsLocal", "Gauge::Gap(int,int)", "control"),
    // A helper that keeps its own locals does not keep the memory, so its contract is read from its body.
    ("HelperOwnLocals", "Gauge::Blended(int,int)", "control"),
    // A helper that tests a field of the object it is handed gets a contract with the facts its body needs.
    ("HelperObject", "Gauge::CappedLevel()", "objects"),
    // A test of a helper result read back from its local splits the frame's proof, and a helper that tests a
    // local of its own gets a contract with holes whose proof splits inside its frame.
    ("HelperLocalTest", "Gauge::Margin()", "objects"),
    ("HelperTestsLocal", "Gauge::Clamped(int,int,int)", "control"),
    // An object helper called from a frame, whose facts are carried to each call; one that throws beyond a
    // field, and one that throws from a frame of its own, each side that throws closed from its `pre`.
    ("HelperObjectLocal", "Gauge::CappedSlack()", "objects"),
    ("HelperObjectThrows", "Gauge::CheckedLevel()", "objects"),
    ("HelperFrameThrows", "Gauge::RaisedLevel()", "objects"),
    ("DownThenUp", "Loops::DownThenUp(uint)", "control"),
    ("CheckedAdd", "CheckedArithmetic::Add(uint,uint)", "control"),
    ("Log64", "Bits::Log64(ulong)", "control"),
    ("AddSigned", "CheckedArithmetic::AddSigned(int,int)", "control"),
    ("Distance", "Arithmetic::Distance(ulong,ulong)", "control"),
    ("Larger", "Arithmetic::Larger(int,int)", "control"),
    ("CounterAdd", "Counter::Add(ulong)", "control"),
    ("OdometerNext", "Odometer::Next()", "control"),
    ("PacketValue", "Arguments::Struct(Examples.Packet)", "control"),
    ("NestedLocal", "Nested::Sized(ulong)", "control"),
    // A string field's reference is copied, compared, tested and cleared without being read through.
    ("CopyTag", "Objects::CopyTag(Examples.Tagged,Examples.Tagged)", "objects"),
    ("SameTag", "Objects::SameTag(Examples.Tagged,Examples.Tagged)", "objects"),
    ("HasTag", "Objects::HasTag(Examples.Tagged)", "objects"),
    ("FillTag", "Objects::FillTag(Examples.Tagged,Examples.Tagged)", "objects"),
    ("ClearTag", "Objects::ClearTag(Examples.Tagged)", "objects"),
    ("Detach", "Objects::Detach(Examples.Node)", "objects"),
    // Array arguments of class references: an element load, the length and a covariance-checked store.
    ("ArrayElement", "NodeArrays::At(Examples.Node[],System.Int32)", "objects"),
    ("ArrayLength", "NodeArrays::Count(Examples.Node[])", "objects"),
    ("ArrayCovariance", "NodeArrays::Put(Examples.Shape[],System.Int32,Examples.Shape)", "objects"),
    ("TagStore", "TagArrays::Put(System.String[],System.Int32,Examples.Tagged)", "objects"),
    ("TagLoad", "TagArrays::Take(Examples.Tagged,System.String[],System.Int32)", "objects"),
    // Element facts carried across element and field stores: a load after them reads back what was stored.
    ("ElementShift", "NodeArrays::Shift(Examples.Node[],Examples.Node)", "objects"),
    ("ElementInstall", "NodeArrays::Install(Examples.Node[],System.Int32,Examples.Node,System.UInt64)", "objects"),
    ("ElementStamp", "TagArrays::Stamp(System.String[],Examples.Tagged,System.UInt64)", "objects"),
    // A fresh array charged to the heap budget, filled and read back, forgotten by the footprint.
    ("FreshPair", "NodeArrays::Pair(Examples.Node,Examples.Node)", "objects"),
    // A writable span filled from the front, directly or through a helper storing its first element, and that
    // helper alone.
    ("SpanFill", "Loops::Fill(System.Span`1<System.UInt32>,uint)", "buffers"),
    ("SpanFillThrough", "Loops::FillThrough(System.Span`1<System.UInt32>,uint)", "buffers"),
    ("SpanPut", "Loops::Put(System.Span`1<System.UInt32>,uint)", "buffers"),
    // Element reads of word arrays, directly and through a helper returning the element's address.
    ("ArrayReadInt32", "PrimitiveArrays::ReadInt32(int[],int)", "buffers"),
    ("ArrayReadUInt64", "PrimitiveArrays::ReadUInt64(ulong[],int)", "buffers"),
    ("ArrayRead", "ArrayElementReferences::Read(int[],int)", "buffers"),
    ("ArraySum", "Loops::SumIndexed(ulong[])", "buffers"),
    ("ArrayFill", "Loops::FillIndexed(uint[],uint)", "buffers"),
    // The receiver of a class instance method beside the array it indexes.
    ("ReceiverArraySum", "Gauge::Total(int[])", "buffers"),
    ("SpanLocalSum", "Loops::SumThroughLocal(System.ReadOnlySpan`1<System.UInt64>)", "buffers"),
    ("ArraySpanSum", "Loops::SumThroughSpan(ulong[])", "buffers"),
    ("ArraySpanFill", "Loops::FillThroughSpan(uint[],uint)", "buffers"),
    // Value arrays class fields hold: measured, stored from an argument, returned, and shared through a local
    // whose length is read after the store; struct and vector elements are named by their field.
    ("SampleCount", "SampleArrays::Count(Examples.Samples)", "buffers"),
    ("SampleRefill", "SampleArrays::Refill(Examples.Samples,System.Int32[])", "buffers"),
    ("SampleValues", "SampleArrays::ValuesOf(Examples.Samples)", "buffers"),
    ("SampleShare", "SampleArrays::Share(Examples.Samples,Examples.Samples)", "buffers"),
    ("TilePairCount", "TileArrays::PairCount(Examples.Tiles)", "buffers"),
    ("TileRelane",
        "TileArrays::Relane(Examples.Tiles,System.Runtime.Intrinsics.Vector128`1<System.UInt64>[])", "buffers"),
    ("TilePairs", "TileArrays::PairsOf(Examples.Tiles)", "buffers"),
    // A struct array argument no field names: its element is a definition whose identity spans two lines.
    ("PairLength",
        "AggregateArrays::ConstructedLength(Examples.AggregateArrays/Pair[],System.Int32,System.Int32)", "buffers")
};
var outlined = catalog.Where(entry => (group is null || entry.Group == group) &&
    (cases is null || cases.Contains(entry.Name, StringComparer.Ordinal))).ToArray();
if (catalog.Select(entry => entry.Name).Distinct(StringComparer.Ordinal).Count() != catalog.Length)
    throw new InvalidOperationException("Outline catalog names must be unique");
if (cases?.Except(outlined.Select(entry => entry.Name), StringComparer.Ordinal).ToArray() is { Length: > 0 } absent)
    throw new ArgumentException($"No case of the {group} group is named {string.Join(", ", absent)}");
if (list)
{
    Console.WriteLine(JsonSerializer.Serialize(outlined.Select(entry =>
        new { entry.Name, entry.Selector, entry.Group }), new JsonSerializerOptions { WriteIndented = true }));
    return;
}
using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/ProofOutlines/" + group);
Directory.CreateDirectory(root);
bool Selected(string name) => outlined.Any(entry => entry.Name == name);
var outlineTimer = System.Diagnostics.Stopwatch.StartNew();
var outlineRoot = Path.Combine(root, "Outlines");
if (Directory.Exists(outlineRoot)) DeleteTree(outlineRoot);
Directory.CreateDirectory(outlineRoot);
string[] Cli(params string[] arguments) => ["dotnet", At("Extractor/bin/Nethermind.LeanCIL.dll"), .. arguments];
var libraryPath = verification.CheckoutLeanPath();
var elaborated = outlined.AsParallel().WithDegreeOfParallelism(Environment.ProcessorCount).Select(entry =>
{
    var (name, selector, _) = entry;
    var scratch = Path.Combine(outlineRoot, name);
    Directory.CreateDirectory(scratch);
    var extraction = Path.Combine(scratch, "Extraction");
    Run(Extract("extract", assembly, "Examples", selector, extraction));
    var outline = Path.Combine(scratch, "Proof.lean");
    Run(Cli("new-proof", extraction, outline));
    Run(Cli("new-proof", extraction, Path.Combine(scratch, "Again.lean")));
    var source = File.ReadAllText(outline);
    if (source != File.ReadAllText(Path.Combine(scratch, "Again.lean")))
        return $"new-proof wrote different outlines of {name}";
    Run([verification.LeanExecutable, "--root=" + extraction, "-o", Path.Combine(scratch, "Extracted.olean"),
        Path.Combine(extraction, "Extracted.lean")], leanPath: libraryPath);
    // The outline imports the keyed module the editor workspace builds, which re-exports the extraction.
    var keyed = Regex.Match(source, @"\Aimport Extracted\.(\w+)\n");
    if (!keyed.Success) return $"The {name} outline does not import a keyed extraction module:\n{source}";
    var module = Path.Combine(scratch, "Extracted", keyed.Groups[1].Value + ".lean");
    Directory.CreateDirectory(Path.GetDirectoryName(module)!);
    File.WriteAllText(module, "import Extracted\n");
    Run([verification.LeanExecutable, "--root=" + scratch, "-o", Path.ChangeExtension(module, ".olean"), module],
        leanPath: scratch + Path.PathSeparator + libraryPath);
    var result = Execute([verification.LeanExecutable, outline],
        leanPath: scratch + Path.PathSeparator + libraryPath);
    var messages = Regex.Matches(result.Output, @"Proof\.lean:\d+:\d+: (error|warning): (.*)")
        .Select(match => (Kind: match.Groups[1].Value, Text: match.Groups[2].Value.Trim())).ToArray();
    var holes = Regex.Match(result.Output, @"'ExampleProof\.correctness' depends on axioms: \[[^\]]*sorryAx");
    return result.Code != 0 || messages.Length == 0 || !holes.Success ||
        messages.Any(message => message.Kind == "error" || message.Text != "declaration uses `sorry`")
        ? $"The {name} outline did not elaborate with only its holes open:\n{result.Output}" : null;
}).Where(failure => failure is not null).ToArray();
if (elaborated.Length > 0) throw new InvalidOperationException(string.Join("\n", elaborated));
Console.WriteLine($"PASS new-proof outlines {outlined.Length} methods that elaborate with only their holes open");

if (Selected("PairLength"))
{
    // The element definition must read back as the extraction's own element, or the outline states another array type,
    // and a body the outline does not step may write the array, so its footprint is the author's to state.
    var pairOutline = File.ReadAllText(Path.Combine(outlineRoot, "PairLength", "Proof.lean"));
    var pairElement = Regex.Match(pairOutline,
        @"@\[reducible\] def sourceElement : CIL\.ArrayElement :=\n  (?<term>(?:[^\n]*\\\n)+[^\n]*)\n");
    var pairExtraction = File.ReadAllText(Path.Combine(outlineRoot, "PairLength", "Extraction", "Extracted.lean"));
    if (!pairElement.Success ||
        !pairExtraction.Contains($"({Regex.Replace(pairElement.Groups["term"].Value, @"\\\n\s*", "")})",
            StringComparison.Ordinal) ||
        !pairOutline.Contains("  sorry -- caller memory the method may write", StringComparison.Ordinal))
        throw new InvalidOperationException("The PairLength outline does not name its struct element across lines " +
            "or leaves its footprint stated:\n" + pairOutline);
    Console.WriteLine("PASS a struct element wider than a line reads back as the extraction's element, and an " +
        "unstepped body over a value array leaves its footprint to the author");
}

if (Selected("DepositFrom"))
{
    // A loop asks write authority only of the object whose field it or a callee stores; the other is only read.
    var depositFrom = File.ReadAllText(Path.Combine(outlineRoot, "DepositFrom", "Proof.lean"));
    if (!depositFrom.Contains("Account.Balance.Owned initial account", StringComparison.Ordinal) ||
        !depositFrom.Contains("Account.Balance.Readable initial source", StringComparison.Ordinal) ||
        depositFrom.Contains("Account.Balance.Owned initial source", StringComparison.Ordinal))
        throw new InvalidOperationException("The DepositFrom outline does not ask per-object field facts:\n" +
            depositFrom);
    Console.WriteLine("PASS a loop outline asks Owned only of the object its callee stores and " +
        "Readable of the one it reads");
}

{
    // A literal operand is written as `simp` normalizes it, so the split's fact rewrites the simplified goal:
    // by its word for an equality or an unsigned order, and by its value for a signed one.
    (string Case, string Fact)[] branches =
    [
        ("BelowFive", "branch1 : (Gauge.Level.of initial gauge).toInt < 5"),
        ("IsFive", "branch1 : (Gauge.Level.of initial gauge) = 5#32"),
        ("UnderFive", "branch1 : (Account.Limit.of initial account) < 5#32"),
        ("CountToFive", "guard : count.toInt < 5"),
        ("CountUpToFive", "guard : count < 5#32"),
        ("ReachFive", "guard : count = 5#32"),
        ("AtLeastFive", "branch1 : x.toInt < 5"),
        ("AtMostFive", "branch1 : 5#32 < x"),
        ("FiveToOne", "branch1 : x = 5#32"),
        ("Floored", "branch1 : value.toInt < 5")
    ];
    var checkedBranches = 0;
    foreach (var (name, fact) in branches.Where(branch => Selected(branch.Case)))
    {
        checkedBranches++;
        if (!File.ReadAllText(Path.Combine(outlineRoot, name, "Proof.lean"))
                .Contains($"by_cases {fact}\n", StringComparison.Ordinal))
            throw new InvalidOperationException($"The {name} outline does not split on `{fact}`");
    }
    if (checkedBranches > 0)
        Console.WriteLine($"PASS {checkedBranches} outlines write a branch against a small constant as simp " +
            "normalizes it");
}

if (Selected("IsIdle"))
{
    // An object local changes its frame slot at each store, so the head must name the slot from the loop state, and its
    // null test must split the walk rather than stop it.
    var isIdle = File.ReadAllText(Path.Combine(outlineRoot, "IsIdle", "Proof.lean"));
    if (!isIdle.Contains("locals := [.object (some state.values)]", StringComparison.Ordinal) ||
        !isIdle.Contains("cases node with", StringComparison.Ordinal) ||
        !isIdle.Contains("by_cases branch1 : ((.address nodeObject) : ManagedReference) = (.address item)",
            StringComparison.Ordinal))
        throw new InvalidOperationException("The IsIdle outline does not follow its object local:\n" + isIdle);
    Console.WriteLine("PASS a loop outline carries an object local in its head and splits on its " +
        "null and identity tests");
}

if (Selected("CopyUntilZero"))
{
    // A test of a `bool` struct field splits on the word its load zero-extends, and each side steps to its return.
    var copyOutline = File.ReadAllText(Path.Combine(outlineRoot, "CopyUntilZero", "Proof.lean"));
    if (!copyOutline.Contains("by_cases branch1 : (scanStopped.setWidth 8).setWidth 32 = 0#32",
            StringComparison.Ordinal) ||
        copyOutline.Contains("narrow field", StringComparison.Ordinal))
        throw new InvalidOperationException(
            "The CopyUntilZero outline does not split on its narrow field:\n" + copyOutline);
    Console.WriteLine("PASS a loop outline splits on a narrow struct field's loaded word");
}

if (Selected("Countdown"))
{
    // The audit refuses an outline for its holes, whatever the method; one loop shows it end to end.
    var countdownOutline = OutlineExtraction("Countdown");
    var countdownSource = Path.Combine(outlineRoot, "Countdown", "Proof.lean");
    var outlineRefused = Execute(Cli("verify", countdownOutline, "--proof", countdownSource));
    if (outlineRefused.Code == 0 || !outlineRefused.Output.Contains("Unapproved proof axioms: sorryAx") ||
        outlineRefused.Output.Contains(": error") || File.Exists(Path.Combine(countdownOutline, "verified.json")))
        throw new InvalidOperationException("verify did not refuse the Countdown outline for its holes:\n" +
            outlineRefused.Output);

    // Filling only the holes, with nothing else edited, must give a proof that verifies.
    var filled = Path.Combine(outlineRoot, "Countdown", "Filled.lean");
    var countdownHoles = new (string Hole, string Filled)[]
    {
        ("def Precondition (value : W32) : Prop := sorry", "def Precondition (value : W32) : Prop := True"),
        ("def Postcondition (value result : W32) : Prop := sorry",
            "def Postcondition (value result : W32) : Prop := result = 0"),
        ("(state : State home0) : Prop := sorry", "(state : State home0) : Prop := True"),
        ("(state : State home0) : Nat := sorry", "(state : State home0) : Nat := state.values.toNat"),
        ("case invariant => sorry -- invariant at the first loop head", "case invariant => trivial"),
        (@"sorry -- Postcondition at the return at Loops\.cs:\d+", "simp_all [Postcondition]"),
        ("case invariant => sorry -- invariant again at the loop head", "case invariant => trivial"),
        ("case measure => sorry -- measure decreases over this iteration", """
        case measure =>
              show (remaining - 1).toNat < remaining.toNat
              have positive : 0 < remaining.toNat := by
                have : remaining.toNat ≠ 0 := fun zero => guard (BitVec.eq_of_toNat_eq zero)
                omega
              rw [BitVec.toNat_sub_of_le]
              · simp; omega
              · change 1 ≤ remaining.toNat
                omega
        """.Trim())
    };
    var filledSource = File.ReadAllText(countdownSource);
    // The CLI reference shows this outline, so the page must change when the generator does.
    var documented = Regex.Match(File.ReadAllText(At("docs/CLI.md")).ReplaceLineEndings("\n"),
        "```lean extracted\n(import Extracted\\.\\w+\n.*?)```", RegexOptions.Singleline);
    if (!documented.Success || documented.Groups[1].Value != filledSource)
        throw new InvalidOperationException("docs/CLI.md does not show the current Countdown outline");
    foreach (var (hole, replacement) in countdownHoles)
    {
        var pattern = hole.Contains(@"\d") ? hole : Regex.Escape(hole);
        if (Regex.Matches(filledSource, pattern).Count != 1)
            throw new InvalidOperationException("The Countdown outline lacks the hole " + hole);
        filledSource = Regex.Replace(filledSource, pattern, replacement.Replace("$", "$$"));
    }
    if (Regex.IsMatch(filledSource, @"(?<![`\w])sorry(?![`\w])"))
        throw new InvalidOperationException("The Countdown outline has a hole the test does not fill");
    File.WriteAllText(filled, filledSource);
    var proved = Execute(Cli("verify", countdownOutline, "--proof", filled));
    if (proved.Code != 0 || !proved.Stdout.StartsWith("Verified: ExampleProof.correctness"))
        throw new InvalidOperationException("The filled Countdown outline did not verify:\n" + proved.Output);
    Console.WriteLine("PASS verify refuses the Countdown outline until its holes are filled, then verifies it " +
        $"({outlineTimer.Elapsed.TotalSeconds:F0}s for every outline check)");
}

// A reader returns the element its index selects; an index outside the array throws, which the precondition rules
// out. Only a read through a helper leaves the memory as the caller's frame left it.
(string Hole, string Filled)[] ArrayReadSpecification(string word, string memory) => [
    ($"""
        def Precondition (values1 : ArrayView) (values1Elements : List {word}) (index : W32) (initial : Memory)
            : Prop := sorry
        """,
        $"""
        def Precondition (_ : ArrayView) (values1Elements : List {word}) (index : W32) (_ : Memory) : Prop :=
          index.toNat < values1Elements.length
        """),
    ($"""
        def Postcondition (values1 : ArrayView) (values1Elements : List {word}) (index : W32)
            (initial final : Memory) (result : {word}) : Prop := sorry
        """,
        $"""
        def Postcondition (_ : ArrayView) (values1Elements : List {word}) (index : W32)
            (initial final : Memory) (result : {word}) : Prop :=
          final = initial ∧ values1Elements[index.toNat]? = some result
        """),
    ("      sorry -- Postcondition of `values1Elements[index.toNat]`", $"      simp [Postcondition{memory}]"),
    ("    sorry -- Precondition excludes an index outside `values1`", "    exact values1Bound assumed")];

// A span filled from the front, directly or through a helper, has one specification and loop head proof.
(string Hole, string Filled)[] spanFillSpecification = [
    ("def Precondition (target1 : SpanView) (value : W32) (initial : Memory) : Prop := sorry",
        """
        def Precondition (_ : SpanView) (_ : W32) (_ : Memory) : Prop := True
        """),
    ("def Postcondition (target1 : SpanView) (value : W32) (initial final : Memory) : Prop := sorry",
        """
        def Postcondition (target1 : SpanView) (value : W32) (_ final : Memory) : Prop :=
          ∀ base, target1.reference = .address base →
            Contents final base 4 (List.replicate target1.length (value : BitVec (8 * 4)))
        """),
    ("""
    def invariant (target1 : SpanView) (value : W32)
        {memory : Memory} {written : List (Reference × Nat)} (state : State memory written)
        : Prop := sorry
    """,
        """
        def invariant (target1 : SpanView) (value : W32)
            {memory : Memory} {written : List (Reference × Nat)} (state : State memory written)
            : Prop :=
          ∀ base, target1.reference = .address base → ∃ done,
            done + state.values.remaining = target1.length ∧
            state.values.view.reference = .address (base.element 4 done) ∧
            Filled state.memory base 4 (List.replicate done (value : BitVec (8 * 4)))
              state.values.remaining
        """),
    ("""
    def measure (target1 : SpanView) (value : W32) {memory : Memory} {written : List (Reference × Nat)}
        (state : State memory written) : Nat := sorry
    """,
        """
        def measure (_ : SpanView) (_ : W32) {memory : Memory} {written : List (Reference × Nat)}
            (state : State memory written) : Nat := state.values.remaining
        """),
    ("    case invariant => sorry -- invariant at the first loop head",
        """
            case invariant =>
              dsimp only [invariant]
              intro base address
              refine ⟨0, by simp, by simp [address], ?_⟩
              have room := (target1Authority.writable base address).after_confined entryFrame.confined
                wellFormed
              rw [target1Width] at room
              simpa using Filled.start room
        """),
    ("    case measure => sorry -- measure decreases over this iteration",
        """
            case measure =>
              simp only [measure]
              omega
        """)];

// A span local over a span argument or a whole array folds as the argument itself does: the local's suffix is
// the loop state, and the theorem names the source's elements.
(string Hole, string Filled)[] SpanLocalSumSpecification(string source, int returnLine) => [
    ($"def Precondition (values1 : {source}) (values1Elements : List W64) (initial : Memory)\n    : Prop := sorry",
        $"def Precondition (_ : {source}) (_ : List W64) (_ : Memory) : Prop := True"),
    ("    (result : W64) : Prop := sorry", "    (result : W64) : Prop := result = values1Elements.sum"),
    ("{memory : Memory} {home1 : Reference} (state : State memory home1) : Prop := sorry",
        "{memory : Memory} {home1 : Reference} (state : State memory home1) : Prop :=\n" +
        "  state.values.2 + state.values.1.values.sum = values1Elements.sum"),
    ("(state : State memory home1) : Nat := sorry",
        "(state : State memory home1) : Nat := state.values.1.values.length"),
    ("case invariant => sorry -- invariant at the first loop head", "case invariant => simp [invariant]"),
    ($"sorry -- Postcondition at the return at Loops.cs:{returnLine}",
        "simpa [Postcondition, invariant] using holds"),
    ("case invariant => sorry -- invariant again at the loop head",
        "case invariant => simpa [invariant, BitVec.add_assoc] using holds"),
    ("case measure => sorry -- measure decreases over this iteration", "case measure => simp [measure]")];

// Object outlines leave only their specification: once it is written, an instance method's field store, a
// reference field store, a null test of an argument followed through a local, a split on a field value and a
// call to a callee that loads the object a field holds each verify.
const string storedHole = "sorry -- Postcondition of the returned value, with `held1` the stored fields";
// A helper's stub leaves its contract to the author: here it needs nothing and returns the smaller argument as a
// signed word, which each side of its test then proves, and its caller proves `pre` at the call.
(string Hole, string Filled)[] SaturateStub(params int[] lines) => [
    ("  pre := fun (value, limit) memory => sorry", "  pre := fun (value, limit) memory => True"),
    ("final = initial ∧ sorry", "final = initial ∧ result.toInt = min value.toInt limit.toInt"),
    ("""
          -- what `saturateContract.post` states of the returned value where `value.toInt <
          -- limit.toInt`, from `permitted`, its `pre`
          sorry
    """, "      omega"),
    ("""
          -- what `saturateContract.post` states of the returned value where not `value.toInt <
          -- limit.toInt`, from `permitted`, its `pre`
          sorry
    """, "      omega"),
    .. lines.Select(line =>
        ($"    sorry -- `saturateContract.pre` at the call at OutlineHelpers.cs:{line}, from `assumed`",
            "    trivial"))];
const string smallerLevel = "min (Gauge.Level.of initial gauge).toInt (Gauge.Limit.of initial gauge).toInt";
// Two helper results, the first read back from its local: the return learns of each only its `post`.
const string helperPairHole = """
      -- Postcondition of the returned value, from `assumed` and `post1`, `post2`, each helper's `post`
      -- of its result
      sorry
    """;
const string helperHole = """
      -- Postcondition of the returned value, from `assumed` and `post1`, the helper's `post` of
      -- `output1`
      sorry
    """;
foreach (var (name, fills) in new (string Name, (string Hole, string Filled)[] Fills)[]
{
    // The caller learns of the helper's result only what the contract's `post` states, `post1`.
    ("HelperResult", [
        .. SaturateStub(15),
        ("def Precondition (gauge : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (gauge : Reference) (initial : Memory) : Prop := True"),
        ("def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop :=\n" +
            $"  result.toInt = {smallerLevel}"),
        (helperHole, "  exact post1")]),
    // The helper keeps the memory, so the store after it starts from the caller's own field facts.
    ("HelperStore", [
        .. SaturateStub(18),
        ("def Precondition (gauge : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (gauge : Reference) (initial : Memory) : Prop := True"),
        ("def Postcondition (gauge : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (gauge : Reference) (initial final : Memory) : Prop :=\n" +
            $"  ∃ settled : W32, Gauge.Limit.Holds final gauge settled ∧ settled.toInt = {smallerLevel}"),
        ("""
          -- Postcondition of the returned value, with `held1` the stored fields, from `assumed` and
          -- `post1`, the helper's `post` of `output1`
          sorry
        """, "  exact ⟨_, held1, post1⟩")]),
    // A caller over words alone composes the helper the same way, from the empty memory.
    ("HelperWords", [
        .. SaturateStub(21),
        ("def Precondition (value limit : W32) : Prop := sorry",
            "def Precondition (value limit : W32) : Prop := True"),
        ("def Postcondition (value limit result : W32) : Prop := sorry",
            "def Postcondition (value limit result : W32) : Prop := result.toInt = min value.toInt limit.toInt"),
        (helperHole, "  exact post1")]),
    // The helper's `pre` rules out the side where it throws, and the caller proves it from its own precondition.
    ("HelperThrows", [
        ("  pre := fun (value, limit) memory => sorry",
            "  pre := fun (value, limit) memory => value.toInt ≤ limit.toInt"),
        ("final = initial ∧ sorry", "final = initial ∧ result = value"),
        ("""
              -- what `withinContract.post` states of the returned value where not `limit.toInt <
              -- value.toInt`, from `permitted`, its `pre`
              sorry
        """, "      rfl"),
        ("def Precondition (value limit : W32) : Prop := sorry",
            "def Precondition (value limit : W32) : Prop := value.toInt ≤ limit.toInt"),
        ("def Postcondition (value limit result : W32) : Prop := sorry",
            "def Postcondition (value limit result : W32) : Prop := result = value"),
        ("    sorry -- `withinContract.pre` at the call at OutlineHelpers.cs:35, from `assumed`", "    exact assumed"),
        (helperHole, "  exact post1")]),
    // A helper that only computes is stepped in one run, leaving what its `post` states of the result.
    ("HelperComputes", [
        ("  pre := fun value memory => sorry", "  pre := fun value memory => True"),
        ("final = initial ∧ sorry", "final = initial ∧ result = value + value"),
        ("    sorry -- what `doubledContract.post` states of the returned value, from `permitted`, its `pre`",
            "    rfl"),
        ("def Precondition (value : W32) : Prop := sorry", "def Precondition (value : W32) : Prop := True"),
        ("def Postcondition (value result : W32) : Prop := sorry",
            "def Postcondition (value result : W32) : Prop := result = value + value"),
        ("    sorry -- `doubledContract.pre` at the call at OutlineHelpers.cs:40, from `assumed`", "    trivial"),
        (helperHole, "  exact post1")]),
    // The first result is stored into the frame's home and loaded back as the word the helper returned.
    ("HelperLocal", [
        .. SaturateStub(45, 46),
        ("def Precondition (gauge : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (gauge : Reference) (initial : Memory) : Prop := True"),
        ("def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop :=\n" +
            $"  ∃ level limit : W32, result = limit - level ∧ level.toInt = {smallerLevel} ∧\n" +
            "    limit.toInt = (Gauge.Limit.of initial gauge).toInt"),
        (helperPairHole, "  exact ⟨_, _, rfl, post1, by simpa using post2⟩")]),
    // A caller over words with a local is entered in any well-formed memory, where its home is allocated.
    ("HelperWordsLocal", [
        .. SaturateStub(53, 54),
        ("def Precondition (value limit : W32) (initial : Memory) : Prop := sorry",
            "def Precondition (value limit : W32) (initial : Memory) : Prop := True"),
        ("def Postcondition (value limit : W32) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (value limit : W32) (initial final : Memory) (result : W32) : Prop :=\n" +
            "  ∃ low high : W32, result = high - low ∧ low.toInt = min value.toInt limit.toInt ∧\n" +
            "    high.toInt = limit.toInt"),
        (helperPairHole, "  exact ⟨_, _, rfl, post1, by simpa using post2⟩")]),
    // The contract read from the helper's body names its result, so only the specification is left.
    ("HelperOwnLocals", [
        ("def Precondition (value limit : W32) (initial : Memory) : Prop := sorry",
            "def Precondition (value limit : W32) (initial : Memory) : Prop := True"),
        ("def Postcondition (value limit : W32) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (value limit : W32) (initial final : Memory) (result : W32) : Prop :=\n" +
            "  result = value * limit - (value + limit)"),
        ("  sorry -- Postcondition of the returned value", "  rfl")]),
    // The helper's `pre` already asks the facts its field load needs, which the caller gives from its own.
    ("HelperObject", [
        ("Gauge.Limit.Readable memory gauge ∧ sorry", "Gauge.Limit.Readable memory gauge ∧ True"),
        ("final = initial ∧ sorry",
            "final = initial ∧ result.toInt = min value.toInt (Gauge.Limit.of initial gauge).toInt"),
        ("""
            -- what `cappedContract.post` states of the returned value where `branch1` holds, from
            -- `permitted`, its `pre`
            sorry
        """, "    omega"),
        ("""
            -- what `cappedContract.post` states of the returned value where `branch1` fails, from
            -- `permitted`, its `pre`
            sorry
        """, "    omega"),
        ("    sorry -- `cappedContract.pre` at the call at OutlineHelpers.cs:71, from `assumed`", "    trivial"),
        ("def Precondition (gauge : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (gauge : Reference) (initial : Memory) : Prop := True"),
        ("def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop :=\n" +
            $"  result.toInt = {smallerLevel}"),
        (helperHole, "  exact post1")]),
    // Each side of the test goes on from the home the result was stored into.
    ("HelperLocalTest", [
        .. SaturateStub(76),
        ("def Precondition (gauge : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (gauge : Reference) (initial : Memory) : Prop := True"),
        ("def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop :=\n" +
            $"  ∃ level : W32, level.toInt = {smallerLevel} ∧\n" +
            "    result = if level.toInt < (Gauge.Limit.of initial gauge).toInt\n" +
            "      then Gauge.Limit.of initial gauge - level else 0"),
        ("""
            -- Postcondition of the returned value where `branch1` holds, from `assumed` and `post1`, the
            -- helper's `post` of `output1`
            sorry
        """, "    exact ⟨_, post1, by simp [branch1]⟩"),
        ("""
            -- Postcondition of the returned value where `branch1` fails, from `assumed` and `post1`, the
            -- helper's `post` of `output1`
            sorry
        """, "    exact ⟨_, post1, by simp [branch1]⟩")]),
    // The helper's frame changes the memory, so its `post` states the result alone, proved on four paths.
    ("HelperTestsLocal", [
        ("memory.WellFormed ∧ sorry", "memory.WellFormed ∧ True"),
        ("  post := fun (value, low, high) initial final result => sorry",
            "  post := fun (value, low, high) initial final result =>\n" +
            "    result.toInt = min (max value.toInt low.toInt) high.toInt"),
        .. new[] { ("holds", "holds"), ("holds", "fails"), ("fails", "holds"), ("fails", "fails") }.Select(side =>
            ($"      -- what `clampContract.post` states of the returned value where `branch1` {side.Item1} and " +
                $"`branch2`\n      -- {side.Item2}, from `permitted`, its `pre`\n      sorry", "      omega")),
        ("    sorry -- `clampContract.pre` at the call at OutlineHelpers.cs:87, from `assumed`", "    trivial"),
        ("def Precondition (value low high : W32) (initial : Memory) : Prop := sorry",
            "def Precondition (value low high : W32) (initial : Memory) : Prop := True"),
        ("def Postcondition (value low high : W32) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (value low high : W32) (initial final : Memory) (result : W32) : Prop :=\n" +
            "  result.toInt = min (max value.toInt low.toInt) high.toInt"),
        (helperHole, "  exact post1")]),
    // Each call's `post` reads the limit in the frame's memory, which the frame's equations name in `initial`.
    ("HelperObjectLocal", [
        ("Gauge.Limit.Readable memory gauge ∧ sorry", "Gauge.Limit.Readable memory gauge ∧ True"),
        ("final = initial ∧ sorry",
            "final = initial ∧ result.toInt = min value.toInt (Gauge.Limit.of initial gauge).toInt"),
        .. new[] { "holds", "fails" }.Select(side =>
            ($"    -- what `cappedContract.post` states of the returned value where `branch1` {side}, from\n" +
                "    -- `permitted`, its `pre`\n    sorry", "    omega")),
        .. new[] { 92, 93 }.Select(line =>
            ($"    sorry -- `cappedContract.pre` at the call at OutlineHelpers.cs:{line}, from `assumed`",
                "    trivial")),
        ("def Precondition (gauge : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (gauge : Reference) (initial : Memory) : Prop := True"),
        ("def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop :=\n" +
            $"  ∃ capped limit : W32, result = limit - capped ∧ capped.toInt = {smallerLevel} ∧\n" +
            "    limit.toInt = (Gauge.Limit.of initial gauge).toInt"),
        (helperPairHole, """
              simp only [gaugeLimitEqual1, gaugeLimitEqual2] at post1 post2
              exact ⟨_, _, rfl, post1, by simpa using post2⟩
            """)]),
    // The helper's `pre` excludes the side that throws, which its caller proves from its own precondition.
    ("HelperObjectThrows", [
        ("Gauge.Limit.Readable memory gauge ∧ sorry",
            "Gauge.Limit.Readable memory gauge ∧ value.toInt ≤ (Gauge.Limit.of memory gauge).toInt"),
        ("final = initial ∧ sorry", "final = initial ∧ result = value"),
        ("""
            -- what `checkedContract.post` states of the returned value where `branch1` fails, from
            -- `permitted`, its `pre`
            sorry
        """, "    rfl"),
        ("    sorry -- `checkedContract.pre` at the call at OutlineHelpers.cs:101, from `assumed`",
            "    exact assumed"),
        ("def Precondition (gauge : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (gauge : Reference) (initial : Memory) : Prop :=\n" +
            "  (Gauge.Level.of initial gauge).toInt ≤ (Gauge.Limit.of initial gauge).toInt"),
        ("def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop :=\n" +
            "  result = Gauge.Level.of initial gauge"),
        (helperHole, "  exact post1")]),
    // Both sides that throw compare the helper's local with the limit, which its `pre` bounds.
    ("HelperFrameThrows", [
        ("Gauge.Limit.Readable memory gauge ∧ sorry",
            "Gauge.Limit.Readable memory gauge ∧\n      value.toInt ≤ (Gauge.Limit.of memory gauge).toInt ∧ " +
            "low.toInt ≤ (Gauge.Limit.of memory gauge).toInt"),
        ("  post := fun (gauge, value, low) initial final result => sorry",
            "  post := fun (gauge, value, low) initial final result =>\n" +
            "    result.toInt = max value.toInt low.toInt"),
        .. new[] { "holds", "fails" }.Select(side =>
            ($"      -- what `raiseContract.post` states of the returned value where `branch1` {side} and " +
                "`branch2`\n      -- fails, from `permitted`, its `pre`\n      sorry", "      omega")),
        ("    sorry -- `raiseContract.pre` at the call at OutlineHelpers.cs:110, from `assumed`",
            "    simpa [Precondition, gaugeLimitEqual1] using assumed"),
        ("def Precondition (gauge : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (gauge : Reference) (initial : Memory) : Prop :=\n" +
            "  (Gauge.Level.of initial gauge).toInt ≤ (Gauge.Limit.of initial gauge).toInt ∧\n" +
            "    0 ≤ (Gauge.Limit.of initial gauge).toInt"),
        ("def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (gauge : Reference) (initial final : Memory) (result : W32) : Prop :=\n" +
            "  result.toInt = max (Gauge.Level.of initial gauge).toInt 0"),
        (helperHole, "  simpa [Postcondition] using post1")]),
    ("Deposit", [
        ("def Precondition (account : Reference) (amount : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : W64) (_ : Memory) : Prop := True"),
        ("def Postcondition (account : Reference) (amount : W64) (initial final : Memory) : Prop := sorry",
            "def Postcondition (account : Reference) (amount : W64) (initial final : Memory) : Prop :=\n" +
            "  Account.Balance.Holds final account (Account.Balance.of initial account + amount)"),
        (storedHole, "exact held1")]),
    ("Link", [
        ("def Precondition (node next : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (node next : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (node next : Reference) (_ final : Memory) : Prop :=\n" +
            "  Node.Next.Holds final node (.address next)"),
        (storedHole, "exact held1")]),
    ("FirstPresent", [
        ("def Precondition (first second : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (first second : Reference) (initial final : Memory) (result : ManagedReference)\n" +
            "    : Prop := sorry",
            "def Postcondition (first _ : Reference) (_ _ : Memory) (result : ManagedReference) : Prop :=\n" +
            "  result = .address first"),
        ("sorry -- Postcondition of the returned value", "rfl")]),
    // The second store may reach the first node's field too, which `across` splits on.
    ("LinkBoth", [
        ("def Precondition (first second next : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (first second next : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (first second next : Reference) (_ final : Memory) : Prop :=\n" +
            "  Node.Next.Holds final first (.address next) ∧ Node.Next.Holds final second (.address next)"),
        ("sorry -- Postcondition of the returned value, with `held1`, `held2` the stored fields", """
        have firstHeld := held1.1.across secondLive1 framed2 held2
          rw [held1.2, ite_self] at firstHeld
          exact ⟨firstHeld, held2⟩
        """.Trim())]),
    ("DepositBoth", [
        ("def Precondition (first second : Reference) (amount : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (first second : Reference) (_ : W64) (_ : Memory) : Prop := first ≠ second"),
        ("def Postcondition (first second : Reference) (amount : W64) (initial final : Memory) : Prop := sorry",
            "def Postcondition (first second : Reference) (amount : W64) (initial final : Memory) : Prop :=\n" +
            "  Account.Balance.Holds final first (Account.Balance.of initial first + amount) ∧\n" +
            "    Account.Balance.Holds final second (Account.Balance.of initial second + amount)"),
        ("sorry -- Postcondition of the returned value, with `held1`, `held2` the stored fields", """
        have distinct : first ≠ second := assumed
          have firstHeld := held1.1.across secondLive1 framed2 held2
          have secondBefore := (secondBalance.across firstLive framed1 held1).2
          simp only [distinct, ite_false] at secondBefore
          simp only [Ne.symm distinct, ite_false, held1.2] at firstHeld
          rw [secondBefore] at held2
          exact ⟨firstHeld, held2⟩
        """.Trim())]),
    // Each side of the test on the balance steps to its own return and leaves its own postcondition.
    ("Withdraw", [
        ("def Precondition (account : Reference) (amount : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : W64) (_ : Memory) : Prop := True"),
        ("def Postcondition (account : Reference) (amount : W64) (initial final : Memory) (result : W64)\n" +
            "    : Prop := sorry",
            "def Postcondition (account : Reference) (amount : W64) (initial final : Memory) (result : W64)\n" +
            "    : Prop :=\n" +
            "  if amount ≤ Account.Balance.of initial account then\n" +
            "    result = amount ∧\n" +
            "      Account.Balance.Holds final account (Account.Balance.of initial account - amount)\n" +
            "  else result = 0 ∧ final = initial"),
        ("-- Postcondition of the returned value where `branch1` holds, with `held1` the stored fields\n" +
            "    sorry",
            "simp only [Postcondition, branch1, ↓reduceIte, true_and]\n    exact held1"),
        ("sorry -- Postcondition of the returned value where `branch1` fails",
            "simp only [Postcondition, branch1, ↓reduceIte, and_true]\n    rfl")]),
    // The callee's contract states its result of whatever node the field holds; the caller names it by the
    // store just before the call, so the result is the value of `next`.
    ("LinkedValue", [
        ("def Precondition (node next : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (node next : Reference) (initial final : Memory) (result : W64) : Prop := sorry",
            "def Postcondition (_ next : Reference) (initial _ : Memory) (result : W64) : Prop :=\n" +
            "  result = Node.Value.of initial next"),
        (storedHole, "exact (nextValue.frame framed1 (apart_of_entries rfl)).2")]),
    // Each path stores the total before it loads the span again, and the loop tactics step on with no frame lemma.
    ("SpanSum", [
        ("def Precondition (values1 : SpanView) (values1Elements : List W64) (initial : Memory)\n    : Prop := sorry",
            "def Precondition (_ : SpanView) (_ : List W64) (_ : Memory) : Prop := True"),
        ("    (result : W64) : Prop := sorry", "    (result : W64) : Prop := result = values1Elements.sum"),
        ("{memory : Memory} {home0 : Reference} (state : State memory home0) : Prop := sorry",
            "{memory : Memory} {home0 : Reference} (state : State memory home0) : Prop :=\n" +
            "  state.values.1 + state.values.2.values.sum = values1Elements.sum"),
        ("(state : State memory home0) : Nat := sorry",
            "(state : State memory home0) : Nat := state.values.2.values.length"),
        ("case invariant => sorry -- invariant at the first loop head", "case invariant => simp [invariant]"),
        ("sorry -- Postcondition at the return at Loops.cs:25", "simpa [Postcondition, invariant] using holds"),
        ("case invariant => sorry -- invariant again at the loop head",
            "case invariant => simpa [invariant, BitVec.add_assoc] using holds"),
        ("case measure => sorry -- measure decreases over this iteration", "case measure => simp [measure]")]),
    // A test of a `bool` argument splits the run into one stepped side per value.
    ("Choose", [
        ("def Precondition (flag : Bool) (x y : W64) : Prop := sorry",
            "def Precondition (_ : Bool) (_ _ : W64) : Prop := True"),
        ("def Postcondition (flag : Bool) (x y result : W64) : Prop := sorry",
            "def Postcondition (flag : Bool) (x y result : W64) : Prop := result = if flag then x else y"),
        ("sorry -- Postcondition of the returned value where `flag` is false", "rfl"),
        ("sorry -- Postcondition of the returned value where `flag` is true", "rfl")]),
    // An `Unsafe.Add` store's write authority, index bound and footprint follow from the specification.
    ("FillWords", [
        ("""
            def Precondition (destination : Reference) (value : W64) (count : W32) (initial : Memory)
                : Prop := sorry
            """,
            """
            def Precondition (destination : Reference) (_ : W64) (count : W32) (initial : Memory)
                : Prop := count.toNat < 2 ^ 31 ∧ Writable initial destination 8 0 count.toNat
            """),
        ("""
            def Postcondition (destination : Reference) (value : W64) (count : W32) (initial final : Memory)
                : Prop := sorry
            """,
            """
            def Postcondition (destination : Reference) (value : W64) (count : W32) (_ final : Memory)
                : Prop := Contents final destination 8 (List.replicate count.toNat (value : BitVec (8 * 8)))
            """),
        ("""
            def footprint (destination : Reference) (value : W64) (count : W32) : List (Reference × Nat) :=
              sorry -- caller memory the loop may write
            """,
            """
            def footprint (destination : Reference) (_ : W64) (count : W32) : List (Reference × Nat) :=
              [(destination, 8 * count.toNat)]
            """),
        ("    (state : State memory written home0) : Prop := sorry",
            """
                (state : State memory written home0) : Prop :=
              state.values.toNat ≤ count.toNat ∧ Filled state.memory destination 8
                (List.replicate state.values.toNat (value : BitVec (8 * 8))) (count.toNat - state.values.toNat)
            """),
        ("def measure (destination : Reference) (value : W64) (count : W32)",
            "def measure (_ : Reference) (_ : W64) (count : W32)"),
        ("    (state : State memory written home0) : Nat := sorry",
            "    (state : State memory written home0) : Nat := count.toNat - state.values.toNat"),
        ("    case invariant => sorry -- invariant at the first loop head",
            """
                case invariant =>
                  simp only [Precondition] at assumed
                  simpa [invariant] using Filled.start (assumed.2.after_confined storedFrame.confined wellFormed)
            """),
        ("    case invariant => sorry -- invariant again at the loop head",
            """
                case invariant =>
                  simp only [Precondition] at assumed
                  simp only [invariant] at holds ⊢
                  obtain ⟨-, filled⟩ := holds
                  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at guard
                  simp only [show 2 * i.toNat < 2 ^ 32 by omega, show 2 * count.toNat < 2 ^ 32 by omega,
                    ↓reduceIte] at guard
                  have lower : i.toNat < count.toNat := by omega
                  rw [show count.toNat - i.toNat = count.toNat - (i.toNat + 1) + 1 by omega] at filled
                  have pushed := filled.push (x := (value : BitVec (8 * 8))) (by simpa using destinationWrote)
                  rw [toNat_succ lower, List.replicate_succ']
                  exact ⟨by omega, pushed.after_below storedBelow (wellFormed.form_bound destinationForm)⟩
            """),
        ("    case measure => sorry -- measure decreases over this iteration",
            """
                case measure =>
                  simp only [Precondition] at assumed
                  simp only [invariant] at holds
                  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at guard
                  simp only [show 2 * i.toNat < 2 ^ 32 by omega, show 2 * count.toNat < 2 ^ 32 by omega,
                    ↓reduceIte] at guard
                  simp only [measure, toNat_succ (show i.toNat < count.toNat by omega)]
                  omega
            """),
        ("    case postcondition => sorry -- Postcondition at the return at Loops.cs:69",
            """
                case postcondition =>
                  simp only [Precondition] at assumed
                  simp only [invariant] at holds
                  obtain ⟨bounded, filled⟩ := holds
                  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at guard
                  simp only [show 2 * i.toNat < 2 ^ 32 by omega, show 2 * count.toNat < 2 ^ 32 by omega,
                    ↓reduceIte] at guard
                  rw [show i.toNat = count.toNat by omega] at filled
                  exact filled.1.after_below exitBelow (wellFormed.form_bound destinationForm)
            """)]),
    // A callee that throws where its precondition fails is split, and the call keeps its output's name.
    ("CountUntil", [
        ("  pre _ _ := sorry",
            "  pre input _ := input.1 ≠ input.2"),
        ("  post _ _ _ _ := sorry",
            "  post input _ _ result := result = input.1 + 1"),
        ("    case postcondition1 => sorry",
            "    case postcondition1 => rfl"),
        ("def Precondition (value limit : W32) : Prop := sorry",
            "def Precondition (value limit : W32) : Prop := value.toNat ≤ limit.toNat"),
        ("def Postcondition (value limit result : W32) : Prop := sorry",
            "def Postcondition (value _ result : W32) : Prop := result = value"),
        ("""
            def invariant (value limit : W32) {home0 home1 : Reference} (state : State home0 home1)
                : Prop := sorry
            """,
            """
            def invariant (value _ : W32) {home0 home1 : Reference} (state : State home0 home1)
                : Prop := state.values.1.toNat + state.values.2.toNat = value.toNat
            """),
        ("def measure (value limit : W32) {home0 home1 : Reference} (state : State home0 home1) : Nat := sorry",
            """
            def measure (_ _ : W32) {home0 home1 : Reference} (state : State home0 home1) : Nat :=
              state.values.1.toNat
            """),
        ("    case invariant => sorry -- invariant at the first loop head",
            "    case invariant => simp [invariant]"),
        ("      sorry -- Postcondition at the return at Loops.cs:145",
            """
                  simp only [invariant] at holds
                  simp only [Postcondition]
                  subst guard
                  exact BitVec.eq_of_toNat_eq (by simpa using holds)
            """),
        ("    case precondition => sorry -- Bump's precondition at this call",
            """
                case precondition =>
                  simp only [invariant] at holds
                  simp only [Precondition] at assumed
                  have positive : remaining.toNat ≠ 0 := fun zero =>
                    guard (BitVec.eq_of_toNat_eq (by simpa using zero))
                  intro same
                  subst same
                  omega
            """),
        ("    case invariant => sorry -- invariant again at the loop head",
            """
                case invariant =>
                  simp only [invariant] at holds ⊢
                  simp only [Precondition] at assumed
                  subst returned
                  have positive : remaining.toNat ≠ 0 := fun zero =>
                    guard (BitVec.eq_of_toNat_eq (by simpa using zero))
                  simp [BitVec.toNat_sub, BitVec.toNat_add]
                  omega
            """),
        ("    case measure => sorry -- measure decreases over this iteration",
            """
                case measure =>
                  have positive : remaining.toNat ≠ 0 := fun zero =>
                    guard (BitVec.eq_of_toNat_eq (by simpa using zero))
                  simp [measure, BitVec.toNat_sub]
                  omega
            """)]),
    // A storing callee's contract is proved from its body, and the element passed to it through `Unsafe.Add`
    // is named at the call; this specification needs its own proofs of the element's side conditions.
    ("CopyUntilZero", [
        ("""
            /-- Replace with what callers must guarantee about the arguments, or `True`. -/
            def Precondition (values1 : SpanView) (values1Elements : List W32) (argument1 : Reference)
                (initial : Memory) : Prop := sorry
            """,
            """
            /-- The words copied: those before the first zero, or all of them. -/
            def copied (values : List W32) : List W32 := values.takeWhile (· ≠ 0#32)

            /-- The count of copied words, with bit 31 set exactly when a zero ended the copy. -/
            def answer (values : List W32) : W32 :=
              let count := BitVec.ofNat 32 (copied values).length
              if 0#32 ∈ values then count ||| 0x80000000 else count

            /-- Copying is unaffected by a nonzero prefix. -/
            theorem copied_append {done : List W32} (nonzero : 0#32 ∉ done) (rest : List W32) :
                copied (done ++ rest) = done ++ copied rest :=
              List.takeWhile_append_of_pos fun word mem => by
                simpa using fun same : word = 0#32 => nonzero (same ▸ mem)

            /-- A nonzero word after a nonzero prefix is copied. -/
            theorem copy_bound {values done tail : List W32} {head : W32} (nonzero : 0#32 ∉ done)
                (more : ¬head = 0#32) (split : values = done ++ head :: tail) :
                done.length < (copied values).length := by
              rw [split, copied_append nonzero]
              simp [copied, more]

            /-- The output has room for the copied words, apart from the span. -/
            def Precondition (values1 : SpanView) (values1Elements : List W32) (argument1 : Reference)
                (initial : Memory) : Prop :=
              Writable initial argument1 4 0 (copied values1Elements).length ∧
                SpanApart values1 (argument1, 4 * (copied values1Elements).length)
            """),
        ("""
            def Postcondition (values1 : SpanView) (values1Elements : List W32) (argument1 : Reference)
                (initial final : Memory) (result : W32) : Prop := sorry
            """,
            """
            def Postcondition (_ : SpanView) (values1Elements : List W32) (argument1 : Reference)
                (_ final : Memory) (result : W32) : Prop :=
              result = answer values1Elements ∧ Contents final argument1 4 (copied values1Elements)
            """),
        ("""
            def footprint (values1 : SpanView) (values1Elements : List W32) (argument1 : Reference)
                : List (Reference × Nat) :=
              sorry -- caller memory the loop may write
            """,
            """
            def footprint (_ : SpanView) (values1Elements : List W32) (argument1 : Reference)
                : List (Reference × Nat) :=
              [(argument1, 4 * (copied values1Elements).length)]
            """),
        ("    (state : State memory written home0 home1) : Prop := sorry",
            """
                (state : State memory written home0 home1) : Prop :=
              ∃ done, values1Elements = done ++ state.values.2.2.2.values ∧ 0#32 ∉ done ∧
                state.values.1.toNat = done.length ∧ state.values.2.1 = 0 ∧
                Filled state.memory argument1 4 done (copied state.values.2.2.2.values).length ∧
                SpanApart state.values.2.2.2.view (argument1, 4 * (copied values1Elements).length)
            """),
        ("def measure (values1 : SpanView) (values1Elements : List W32) (argument1 : Reference)",
            "def measure (_ : SpanView) (_ : List W32) (_ : Reference)"),
        ("    (state : State memory written home0 home1) : Nat := sorry",
            "    (state : State memory written home0 home1) : Nat := state.values.2.2.2.values.length"),
        ("    case invariant => sorry -- invariant at the first loop head",
            """
                case invariant =>
                  simp only [Precondition] at assumed
                  simp only [invariant]
                  exact ⟨[], by simp, by simp, by simp, by simp,
                    Filled.start (assumed.1.after_confined storedFrame.confined wellFormed), assumed.2⟩
            """),
        ("""
                have values1Apart : ∀ entry ∈ footprint values1 values1Elements argument1,
                    SpanApart values1View entry :=
                    sorry -- `values1` lies apart from the memory the loop writes
            """,
            """
                have values1Apart : ∀ entry ∈ footprint values1 values1Elements argument1,
                    SpanApart values1View entry := by
                  simp only [invariant] at holds
                  obtain ⟨-, -, -, -, -, -, apart⟩ := holds
                  simpa [footprint] using apart
            """),
        ("""
                  have argument1Reach : Writable initial (argument1.element 4 scanCount.toNat) 4 0 1 := by
                    cil_loop_obligation [invariant, Precondition, footprint]
            """,
            """
                  have argument1Reach : Writable initial (argument1.element 4 scanCount.toNat) 4 0 1 := by
                    simp only [invariant] at holds
                    simp only [Precondition] at assumed
                    obtain ⟨done, split, nonzero, counted, -, -, -⟩ := holds
                    have := copy_bound nonzero branch2 split
                    exact Writable.element_writable assumed.1 (by omega) (by omega)
            """),
        ("""
                  have argument1Small : scanCount.toNat < 2 ^ 31 := by
                    cil_loop_obligation [invariant, Precondition, footprint]
            """,
            """
                  have argument1Small : scanCount.toNat < 2 ^ 31 := by
                    simp only [invariant] at holds
                    obtain ⟨done, split, -, counted, -, -, -⟩ := holds
                    have short := values1Contents.length ▸ SpanView.length_bounded values1 initial values1Valid
                    have lengths := congrArg List.length split
                    simp only [List.length_append, List.length_cons] at lengths
                    omega
            """),
        ("""
                      Within (argument1.element 4 scanCount.toNat, 4) entry := by
                    cil_loop_obligation [invariant, Precondition, footprint]
            """,
            """
                      Within (argument1.element 4 scanCount.toNat, 4) entry := by
                    simp only [invariant] at holds
                    obtain ⟨done, split, nonzero, counted, -, -, -⟩ := holds
                    have := copy_bound nonzero branch2 split
                    refine ⟨_, List.mem_singleton_self _, ?_⟩
                    simp [Within]
                    omega
            """),
        ("""
            def invariant (values1 : SpanView) (values1Elements : List W32) (argument1 : Reference)
                {memory : Memory}
            """,
            """
            def invariant (_ : SpanView) (values1Elements : List W32) (argument1 : Reference)
                {memory : Memory}
            """),
        ("""
                · -- leaves the loop at Loops.cs:129
                  cil_loop_finish [branch1]
                  case postcondition =>
                    refine ⟨_, rfl, ?_⟩
                    sorry -- Postcondition at the return at Loops.cs:129
                · -- leaves the loop at Loops.cs:129
                  cil_loop_finish [branch1]
                  case postcondition =>
                    refine ⟨_, rfl, ?_⟩
                    sorry -- Postcondition at the return at Loops.cs:129
            """,
            """
                · -- leaves the loop at Loops.cs:129
                  cil_loop_finish [branch1]
                  case postcondition =>
                    refine ⟨_, rfl, ?_⟩
                    simp only [invariant] at holds
                    obtain ⟨done, split, nonzero, counted, stopped, filled, -⟩ := holds
                    simp only [List.append_nil] at split
                    subst split
                    have whole : copied values1Elements = values1Elements := by
                      simpa [copied] using copied_append nonzero []
                    simp only [Postcondition]
                    refine ⟨?_, ?_⟩
                    · simp only [answer, whole, nonzero, ite_false, ← counted, BitVec.ofNat_toNat,
                        BitVec.setWidth_eq]
                    · rw [whole]
                      exact filled.1.after_below exitBelow (wellFormed.form_bound argument1Form)
                · -- leaves the loop at Loops.cs:129
                  cil_loop_finish [branch1]
                  case postcondition =>
                    simp only [invariant] at holds
                    obtain ⟨-, -, -, -, stopped, -, -⟩ := holds
                    simp [stopped] at branch1
            """),
        ("""
                  cil_loop_finish [branch2]
                  case postcondition =>
                    refine ⟨_, rfl, ?_⟩
                    sorry -- Postcondition at the return at Loops.cs:129
            """,
            """
                  cil_loop_finish [branch2]
                  case postcondition =>
                    refine ⟨_, rfl, ?_⟩
                    simp only [invariant] at holds
                    obtain ⟨done, split, nonzero, counted, stopped, filled, -⟩ := holds
                    subst branch2
                    have whole : copied values1Elements = done := by
                      rw [split, copied_append nonzero]
                      simp [copied]
                    have old := wellFormed.form_bound argument1Form
                    simp only [Postcondition]
                    refine ⟨?_, ?_⟩
                    · unfold answer
                      rw [whole, ← counted, BitVec.ofNat_toNat, BitVec.setWidth_eq]
                      simp [split]
                    · rw [whole]
                      exact ((filled.1.after_below storedBelow old).after_below storedBelow_1 old).after_below
                        exitBelow old
            """),
        ("""
                  case invariant => sorry -- invariant again at the loop head
                  case measure => sorry -- measure decreases over this iteration
            """,
            """
                  case invariant =>
                    simp only [invariant] at holds ⊢
                    obtain ⟨done, split, nonzero, counted, stopped, filled, apart⟩ := holds
                    have room : (copied (values1Head :: values1Tail)).length =
                        (copied values1Tail).length + 1 := by
                      simp [copied, branch2]
                    have old := wellFormed.form_bound argument1Form
                    have atCalled := (filled.after_below storedBelow old).after_confined confined
                      storedFrame.wellFormed (by
                        intro entry member
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                        subst member
                        right; left
                        simp [Reference.element_offset]
                        omega)
                    have atHead := atCalled.after_below storedBelow_1 old
                    rw [room] at atHead
                    refine ⟨done ++ [values1Head], by simp [split], by simpa using ⟨nonzero, Ne.symm branch2⟩,
                      ?_, stopped, atHead.extend returned (by omega), apart.slice values1Cut⟩
                    simp only [List.length_append, List.length_singleton, ← counted, BitVec.toNat_add]
                    simp
                    omega
                  case measure => simp [measure]
            """)]),
    // The first loop's exit enters the second loop, whose own invariant and measure the proof writes.
    ("DownThenUp", [
        ("def Precondition (value : W32) : Prop := sorry",
            "def Precondition (_ : W32) : Prop := True"),
        ("def Postcondition (value result : W32) : Prop := sorry",
            "def Postcondition (value result : W32) : Prop := result = value"),
        ("def invariant (value : W32) {home0 home1 : Reference} (state : State home0 home1) : Prop := sorry",
            "def invariant (_ : W32) {home0 home1 : Reference} (_ : State home0 home1) : Prop := True"),
        ("def measure (value : W32) {home0 home1 : Reference} (state : State home0 home1) : Nat := sorry",
            """
            def measure (_ : W32) {home0 home1 : Reference} (state : State home0 home1) : Nat :=
              state.values.1.toNat
            """),
        ("def invariant2 (value : W32) {home0 home1 : Reference} (state : State home0 home1) : Prop := sorry",
            """
            def invariant2 (value : W32) {home0 home1 : Reference} (state : State home0 home1) : Prop :=
              state.values.2.toNat ≤ value.toNat
            """),
        ("def measure2 (value : W32) {home0 home1 : Reference} (state : State home0 home1) : Nat := sorry",
            """
            def measure2 (value : W32) {home0 home1 : Reference} (state : State home0 home1) : Nat :=
              value.toNat - state.values.2.toNat
            """),
        ("    case invariant => sorry -- invariant at the first loop head",
            "    case invariant => trivial"),
        ("      case invariant => sorry -- invariant2 at loop 2's first head",
            "      case invariant => simp [invariant2]"),
        ("        sorry -- Postcondition at the return at Loops.cs:157",
            "        simp [Postcondition]"),
        ("""
                  cil_loop_recurse recurse (remaining, climbed + 1) [guard]
                  case invariant => sorry -- invariant again at the loop head
                  case measure => sorry -- measure decreases over this iteration
            """,
            """
                  cil_loop_recurse recurse (remaining, climbed + 1) [guard]
                  case invariant =>
                    simp only [invariant2] at holds ⊢
                    have below : climbed.toNat < value.toNat :=
                      Nat.lt_of_le_of_ne holds fun same => guard (BitVec.eq_of_toNat_eq same)
                    rw [BitVec.toNat_add_of_lt (by simp; omega)]
                    simp
                    omega
                  case measure =>
                    simp only [invariant2] at holds
                    have below : climbed.toNat < value.toNat :=
                      Nat.lt_of_le_of_ne holds fun same => guard (BitVec.eq_of_toNat_eq same)
                    simp only [measure2]
                    rw [BitVec.toNat_add_of_lt (by simp; omega)]
                    simp
                    omega
            """),
        ("""
                cil_loop_recurse recurse (remaining - 1, climbed) [guard]
                case invariant => sorry -- invariant again at the loop head
                case measure => sorry -- measure decreases over this iteration
            """,
            """
                cil_loop_recurse recurse (remaining - 1, climbed) [guard]
                case invariant => trivial
                case measure =>
                  have positive : remaining.toNat ≠ 0 := fun zero => guard (BitVec.eq_of_toNat_eq zero)
                  simp [measure, BitVec.toNat_sub]
                  omega
            """)]),
    // The overflow side is closed from the precondition, so only the fitting side is left.
    ("CheckedAdd", [
        ("def Precondition (x y : W32) : Prop := sorry",
            "def Precondition (x y : W32) : Prop := x.toNat + y.toNat < 2 ^ 32"),
        ("def Postcondition (x y result : W32) : Prop := sorry",
            "def Postcondition (x y result : W32) : Prop := result.toNat = x.toNat + y.toNat"),
        ("      sorry -- Postcondition of the returned value",
            """
                  simp only [Postcondition]
                  rw [BitVec.toNat_add, Nat.mod_eq_of_lt fits1]
            """)]),
    ("Log64", [
        ("def Precondition (value : W64) : Prop := sorry",
            "def Precondition (_ : W64) : Prop := True"),
        ("def Postcondition (value : W64) (result : W32) : Prop := sorry",
            """
            def Postcondition (value : W64) (result : W32) : Prop :=
              result = BitVec.ofNat 32 value.toNat.log2
            """),
        ("    sorry -- Postcondition of the returned value",
            "    rfl")]),
    ("AddSigned", [
        ("def Precondition (x y : W32) : Prop := sorry",
            "def Precondition (x y : W32) : Prop := -2 ^ 31 ≤ x.toInt + y.toInt ∧ x.toInt + y.toInt < 2 ^ 31"),
        ("def Postcondition (x y result : W32) : Prop := sorry",
            "def Postcondition (x y result : W32) : Prop := result.toInt = x.toInt + y.toInt"),
        ("      sorry -- Postcondition of the returned value",
            """
                  simp only [Postcondition]
                  rw [BitVec.toInt_add_of_not_saddOverflow]
                  simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.reduceSub]
                  omega
            """)]),
    ("Distance", [
        ("def Precondition (x y : W64) : Prop := sorry", "def Precondition (_ _ : W64) : Prop := True"),
        ("def Postcondition (x y result : W64) : Prop := sorry",
            "def Postcondition (x y result : W64) : Prop := result = if x < y then y - x else x - y"),
        ("      sorry -- Postcondition of the returned value where `branch1` holds",
            "      simp [Postcondition, branch1]"),
        ("      sorry -- Postcondition of the returned value where `branch1` fails",
            "      simp [Postcondition, branch1]")]),
    // A signed test splits on the words read through `toInt`.
    ("Larger", [
        ("def Precondition (x y : W32) : Prop := sorry", "def Precondition (_ _ : W32) : Prop := True"),
        ("def Postcondition (x y result : W32) : Prop := sorry",
            "def Postcondition (x y result : W32) : Prop := result = if x.toInt < y.toInt then y else x"),
        ("      sorry -- Postcondition of the returned value where `branch1` holds",
            "      simp [Postcondition, branch1]"),
        ("      sorry -- Postcondition of the returned value where `branch1` fails",
            "      simp [Postcondition, branch1]")]),
    // Every byte pattern of the by-value packet is accepted, including its padding and unused tag.
    ("PacketValue", [
        ("def Precondition (value : Vector (BitVec 8) 12) : Prop := sorry",
            "def Precondition (_ : Vector (BitVec 8) 12) : Prop := True"),
        ("def Postcondition (value : Vector (BitVec 8) 12) (result : W64) : Prop := sorry",
            "def Postcondition (_ : Vector (BitVec 8) 12) (result : W64) : Prop := result = 23"),
        ("sorry -- Postcondition of the returned value", "rfl")]),
    // The nested struct's explicit size includes padding after the word field.
    ("NestedLocal", [
        ("import CIL.Safety.SymbolicExecution",
            "import CIL.Safety.SymbolicExecution\nimport CIL.Safety.ByteRoundTrip"),
        ("def Precondition (value : W64) : Prop := sorry", "def Precondition (_ : W64) : Prop := True"),
        ("def Postcondition (value result : W64) : Prop := sorry",
            "def Postcondition (value result : W64) : Prop := result = value"),
        ("theorem correctness", "set_option maxHeartbeats 2000000 in\ntheorem correctness"),
        ("    sorry -- Postcondition of the returned value", """
            change BitVec.ofNat 64 (byteNumber (numberBytes value.toNat 8)) = value
            rw [byteNumber_numberBytes]
            apply BitVec.eq_of_toNat_eq
            simp [Nat.mod_eq_of_lt value.isLt]
        """)]),
    // A struct receiver's field store leaves its contents as `held1`, which is the postcondition.
    ("CounterAdd", [
        ("def Precondition (counter : Reference) (value counterValue : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ _ : W64) (_ : Memory) : Prop := True"),
        ("""
        def Postcondition (counter : Reference) (value counterValue : W64) (initial final : Memory)
            (result : W64) : Prop := sorry
        """,
            """
            def Postcondition (counter : Reference) (value counterValue : W64) (_ final : Memory)
                (result : W64) : Prop :=
              result = counterValue + value ∧ Contents final counter 8 [counterValue + value]
            """),
        ("  case postcondition => sorry", "  case postcondition => exact ⟨rfl, held1⟩")]),
    // Its field sits at offset 8, so the outline names it `odometer.element 1 8`.
    ("OdometerNext", [
        ("def Precondition (odometer : Reference) (odometerCount : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : W64) (_ : Memory) : Prop := True"),
        ("""
        def Postcondition (odometer : Reference) (odometerCount : W64) (initial final : Memory)
            (result : W64) : Prop := sorry
        """,
            """
            def Postcondition (odometer : Reference) (odometerCount : W64) (_ final : Memory)
                (result : W64) : Prop :=
              result = odometerCount + 1 ∧ Contents final (odometer.element 1 8) 8 [odometerCount + 1]
            """),
        ("  case postcondition => sorry", "  case postcondition => exact ⟨rfl, held1⟩")]),
    // The string the tag holds is named by the field it was loaded from, whether or not it is null.
    ("CopyTag", [
        ("def Precondition (target1 source : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (target1 source : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (target1 source : Reference) (initial final : Memory) : Prop :=\n" +
            "  Tagged.Tag.Holds final target1 (Tagged.Tag.of initial source)"),
        (storedHole, "exact held1")]),
    // A null test of the tag splits the proof; only the side where it is null stores.
    ("FillTag", [
        ("def Precondition (target1 source : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (target1 source : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (target1 source : Reference) (initial final : Memory) : Prop :=\n" +
            "  if Tagged.Tag.of initial target1 = .null then\n" +
            "    Tagged.Tag.Holds final target1 (Tagged.Tag.of initial source)\n" +
            "  else final = initial"),
        ("-- Postcondition of the returned value where `branch1` holds, with `held1` the stored fields\n" +
            "    sorry",
            "simp only [Postcondition, branch1, ↓reduceIte]\n    exact held1"),
        ("sorry -- Postcondition of the returned value where `branch1` fails",
            "simp only [Postcondition, branch1, ↓reduceIte]")]),
    // The returned word is computed from a comparison, so the proof chooses the Bool it encodes.
    ("HasTag", [
        ("def Precondition (item : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (item : Reference) (initial final : Memory) (result : Bool) : Prop := sorry",
            "def Postcondition (item : Reference) (initial final : Memory) (result : Bool) : Prop :=\n" +
            "  result = (Tagged.Tag.of initial item != .null) ∧ final = initial"),
        ("case result => sorry -- the Bool the returned word encodes",
            "case result => exact Tagged.Tag.of initial item != .null"),
        ("case encoded => sorry -- the returned word is that Bool's encoding",
            "case encoded => by_cases present : Tagged.Tag.of initial item = .null <;> simp [present]"),
        ("sorry -- Postcondition of the returned value", "exact ⟨rfl, rfl⟩")]),
    // A null store into a class field, after which the returned node must still form.
    ("Detach", [
        ("def Precondition (node : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (node : Reference) (initial final : Memory) (result : ManagedReference)\n" +
            "    : Prop := sorry",
            "def Postcondition (node : Reference) (initial final : Memory) (result : ManagedReference) : Prop :=\n" +
            "  result = Node.Next.of initial node ∧ Node.Next.Holds final node .null"),
        (storedHole, "exact ⟨nodeNextHeld.symm, held1⟩")]),
    // The element is named by the array and index it was loaded from, null or not.
    ("ArrayElement", [
        ("def Precondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (index : W32) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : W32) (_ : Memory) :\n" +
            "    Prop := True"),
        ("def Postcondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (index : W32) (initial final : Memory) (result : ManagedReference) : Prop := sorry",
            "def Postcondition (nodes : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (index : W32)\n" +
            "    (initial final : Memory) (result : ManagedReference) : Prop :=\n" +
            "  result = ReferenceArray.of initial nodes index.toNat ∧ final = initial"),
        ("sorry -- Postcondition of the returned value", "exact ⟨rfl, rfl⟩")]),
    ("ArrayLength", [
        ("def Precondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : Memory) : Prop :=\n" +
            "  True"),
        ("def Postcondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (initial final : Memory) (result : W32) : Prop :=\n" +
            "  result = BitVec.ofNat 32 nodesLength ∧ final = initial"),
        ("sorry -- Postcondition of the returned value",
            "exact ⟨BitVec.setWidth_ofNat_of_le (by decide) nodesLength, rfl⟩")]),
    // The statement leaves the covariance check of the stored shape as a premise, since a `Shape[]` may be an
    // array of any class derived from `Shape`.
    ("ArrayCovariance", [
        ("def Precondition (shapes : Reference) (shapesElement : CIL.Extraction.TypeExpr) (shapesLength : Nat)\n" +
            "    (index : W32) (shape : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : W32)\n" +
            "    (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (shapes : Reference) (shapesElement : CIL.Extraction.TypeExpr)\n" +
            "    (shapesLength : Nat) (index : W32) (shape : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (shapes : Reference) (shapesElement : CIL.Extraction.TypeExpr)\n" +
            "    (shapesLength : Nat) (index : W32) (shape : Reference) (_ final : Memory) : Prop :=\n" +
            "  ReferenceArray.Holds final shapes shapesElement shapesLength index.toNat (.address shape)"),
        (storedHole, "exact held1")]),
    // A string moves between a field and an element as the reference it is, never read through.
    ("TagStore", [
        ("def Precondition (tags : Reference) (tagsElement : CIL.Extraction.TypeExpr) (tagsLength : Nat)\n" +
            "    (index : W32) (tagged : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : W32)\n" +
            "    (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (tags : Reference) (tagsElement : CIL.Extraction.TypeExpr) (tagsLength : Nat)\n" +
            "    (index : W32) (tagged : Reference) (initial final : Memory) : Prop := sorry",
            "def Postcondition (tags : Reference) (tagsElement : CIL.Extraction.TypeExpr) (tagsLength : Nat)\n" +
            "    (index : W32) (tagged : Reference) (initial final : Memory) : Prop :=\n" +
            "  ReferenceArray.Holds final tags tagsElement tagsLength index.toNat\n" +
            "    (Tagged.Tag.of initial tagged)"),
        (storedHole, "exact held1")]),
    ("TagLoad", [
        ("def Precondition (tagged tags : Reference) (tagsElement : CIL.Extraction.TypeExpr)\n" +
            "    (tagsLength : Nat) (index : W32) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : W32)\n" +
            "    (_ : Memory) : Prop := True"),
        ("def Postcondition (tagged tags : Reference) (tagsElement : CIL.Extraction.TypeExpr)\n" +
            "    (tagsLength : Nat) (index : W32) (initial final : Memory) : Prop := sorry",
            "def Postcondition (tagged tags : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat)\n" +
            "    (index : W32) (initial final : Memory) : Prop :=\n" +
            "  Tagged.Tag.Holds final tagged (ReferenceArray.of initial tags index.toNat)"),
        (storedHole, "exact held1")]),
    // The load after two stores reads back the first element's old reference, carried across the store into
    // the other element.
    ("ElementShift", [
        ("def Precondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (node : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : Reference)\n" +
            "    (_ : Memory) : Prop := True"),
        ("def Postcondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (node : Reference) (initial final : Memory) (result : ManagedReference) : Prop := sorry",
            "def Postcondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (node : Reference) (initial final : Memory) (result : ManagedReference) : Prop :=\n" +
            "  result = ReferenceArray.of initial nodes 0 ∧\n" +
            "    ReferenceArray.Holds final nodes nodesElement nodesLength 0 (.address node) ∧\n" +
            "    ReferenceArray.Holds final nodes nodesElement nodesLength 1 (ReferenceArray.of initial nodes 0)"),
        ("sorry -- Postcondition of the returned value, with `held1`, `held2` the stored fields",
            "exact ⟨rfl, held2, nodesSlot2At2⟩")]),
    // The element keeps the stored node across the store into the node's own field.
    ("ElementInstall", [
        ("def Precondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (index : W32) (node : Reference) (value : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : W32)\n" +
            "    (_ : Reference) (_ : W64) (_ : Memory) : Prop := True"),
        ("def Postcondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (index : W32) (node : Reference) (value : W64) (initial final : Memory)\n" +
            "    (result : ManagedReference) : Prop := sorry",
            "def Postcondition (nodes : Reference) (nodesElement : CIL.Extraction.TypeExpr) (nodesLength : Nat)\n" +
            "    (index : W32) (node : Reference) (value : W64) (_ final : Memory)\n" +
            "    (result : ManagedReference) : Prop :=\n" +
            "  result = .address node ∧\n" +
            "    ReferenceArray.Holds final nodes nodesElement nodesLength index.toNat (.address node) ∧\n" +
            "    Node.Value.Holds final node value"),
        ("sorry -- Postcondition of the returned value, with `held1`, `held2` the stored fields",
            "exact ⟨rfl, nodesSlot1At2, held2⟩")]),
    // A string element copied after a field store forms and passes the covariance check as it did before it.
    ("ElementStamp", [
        ("def Precondition (tags : Reference) (tagsElement : CIL.Extraction.TypeExpr) (tagsLength : Nat)\n" +
            "    (tagged : Reference) (id : W64) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : CIL.Extraction.TypeExpr) (_ : Nat) (_ : Reference)\n" +
            "    (_ : W64) (_ : Memory) : Prop := True"),
        ("def Postcondition (tags : Reference) (tagsElement : CIL.Extraction.TypeExpr) (tagsLength : Nat)\n" +
            "    (tagged : Reference) (id : W64) (initial final : Memory) : Prop := sorry",
            "def Postcondition (tags : Reference) (tagsElement : CIL.Extraction.TypeExpr) (tagsLength : Nat)\n" +
            "    (tagged : Reference) (id : W64) (initial final : Memory) : Prop :=\n" +
            "  Tagged.Id.Holds final tagged id ∧\n" +
            "    ReferenceArray.Holds final tags tagsElement tagsLength 1 (ReferenceArray.of initial tags 0)"),
        ("sorry -- Postcondition of the returned value, with `held1`, `held2` the stored fields",
            "exact ⟨held1.after_confined framed2 (ReferenceArray.apart_single (show\n" +
            "      tagged.allocation ≠ tags.allocation from tagsLive1.field_ne held1.1.located rfl)), held2⟩")]),
    // The second node comes back, and the caller's memory is confined to nothing.
    ("FreshPair", [
        ("def Precondition (first second : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (first second : Reference) (initial final : Memory) (result : ManagedReference)\n" +
            "    : Prop := sorry",
            "def Postcondition (_ second : Reference) (_ _ : Memory) (result : ManagedReference) : Prop :=\n" +
            "  result = .address second"),
        ("sorry -- Postcondition of the returned value, with `held2`, `held3` the stored fields", "rfl")]),
    // A written span needs authority over its elements, not readable contents; the invariant states the
    // filled prefix from the span's own address.
    ("SpanFill", [
        .. spanFillSpecification,
        ("    case postcondition => sorry -- Postcondition at the return at Loops.cs:168",
            """
                case postcondition =>
                  dsimp only [invariant] at holds
                  intro base address
                  obtain ⟨done, total, -, filled⟩ := holds base address
                  rw [Nat.add_zero] at total
                  subst total
                  exact filled.complete.after_below exitBelow
                    (SpanView.allocation_below target1Valid wellFormed address)
            """),
        ("    case invariant => sorry -- invariant again at the loop head",
            """
                case invariant =>
                  dsimp only [invariant] at holds ⊢
                  intro base address
                  obtain ⟨done, total, place, filled⟩ := holds base address
                  rw [place] at target1Address
                  cases target1Address
                  refine ⟨done + 1, by omega, ?_, ?_⟩
                  · rw [SpanView.slice_reference _ _ _ _ _ _ place target1Cut, target1Span.elementWidth]
                    simp only [Reference.element, ManagedReference.address.injEq, Reference.mk.injEq,
                      true_and]
                    omega
                  · rw [List.replicate_succ']
                    exact filled.push (by simpa using target1Wrote)
            """)]),
    // A helper writes each element; the frame after its call keeps the filled prefix, apart from the lent span.
    ("SpanFillThrough", [
        .. spanFillSpecification,
        ("    case postcondition => sorry -- Postcondition at the return at Loops.cs:181",
            """
                case postcondition =>
                  dsimp only [invariant] at holds
                  intro base address
                  obtain ⟨done, total, -, filled⟩ := holds base address
                  rw [Nat.add_zero] at total
                  subst total
                  exact filled.complete.after_below exitBelow
                    (SpanView.allocation_below target1Valid wellFormed address)
            """),
        ("    case invariant => sorry -- invariant again at the loop head",
            """
                case invariant =>
                  dsimp only [invariant] at holds ⊢
                  intro base address
                  obtain ⟨done, total, place, filled⟩ := holds base address
                  refine ⟨done + 1, by omega, ?_, ?_⟩
                  · rw [SpanView.slice_reference _ _ _ _ _ _ place target1Cut, target1Span.elementWidth]
                    simp only [Reference.element, ManagedReference.address.injEq, Reference.mk.injEq,
                      true_and]
                    omega
                  · rw [List.replicate_succ']
                    refine (filled.after_confined confined frame.wellFormed ?_).extend
                      (returned _ place) (by simp)
                    intro entry member
                    simp only [SpanView.footprint, place, List.mem_singleton] at member
                    subst member
                    rw [target1Span.elementWidth, target1Span.length, List.length_replicate]
                    simpa using base.element_run_apart 4 (first := 0) (left := done) (second := done)
                      (right := target1Rest + 1) (Or.inl (by omega))
            """)]),
    // One store into a span outside a loop: an empty span throws, which the precondition rules out.
    ("SpanPut", [
        ("def Precondition (target1 : SpanView) (value : W32) (initial : Memory) : Prop := sorry",
            """
            def Precondition (target1 : SpanView) (_ : W32) (_ : Memory) : Prop := 0 < target1.length
            """),
        ("def Postcondition (target1 : SpanView) (value : W32) (initial final : Memory) : Prop := sorry",
            """
            def Postcondition (target1 : SpanView) (value : W32) (_ final : Memory) : Prop :=
              ∀ base, target1.reference = .address base → Contents final base 4 [value]
            """),
        ("    sorry -- Precondition excludes an empty `target1`",
            "    simp [Precondition, target1Count] at assumed"),
        ("    case postcondition => sorry", "    case postcondition => exact target1Filled")]),
    ("ArrayReadInt32", ArrayReadSpecification("W32", "")),
    ("ArrayReadUInt64", ArrayReadSpecification("W64", "")),
    ("ArrayRead", ArrayReadSpecification("W32", ", leaveFrame")),
    // An indexed loop over an array reads each element from the storage span's contents; the bound test reads
    // the array's length as a signed word, below 2^31 for a valid array.
    ("ArraySum", [
        // The outline states the null exclusion; only what else callers guarantee is left.
        ("  values1.reference ≠ .null ∧ sorry", "  values1.reference ≠ .null ∧ True"),
        ("""
        def Postcondition (values1 : ArrayView) (values1Elements : List W64) (initial final : Memory)
            (result : W64) : Prop := sorry
        """,
            """
            def Postcondition (_ : ArrayView) (values1Elements : List W64) (_ _ : Memory)
                (result : W64) : Prop := result = values1Elements.foldl (· + ·) 0
            """),
        ("""
        def invariant (values1 : ArrayView) (values1Elements : List W64)
            {memory : Memory} {home0 home1 : Reference} (state : State memory home0 home1) : Prop := sorry
        """,
            """
            def invariant (_ : ArrayView) (values1Elements : List W64)
                {memory : Memory} {home0 home1 : Reference} (state : State memory home0 home1) : Prop :=
              state.values.2.toNat ≤ values1Elements.length ∧
                state.values.1 = (values1Elements.take state.values.2.toNat).foldl (· + ·) 0
            """),
        ("""
        def measure (values1 : ArrayView) (values1Elements : List W64)
            {memory : Memory} {home0 home1 : Reference} (state : State memory home0 home1) : Nat := sorry
        """,
            """
            def measure (_ : ArrayView) (values1Elements : List W64)
                {memory : Memory} {home0 home1 : Reference} (state : State memory home0 home1) : Nat :=
              values1Elements.length - state.values.2.toNat
            """),
        ("    case invariant => sorry -- invariant at the first loop head", "    case invariant => simp [invariant]"),
        ("""
            case invariant => sorry -- invariant again at the loop head
            case measure => sorry -- measure decreases over this iteration
        """,
            """
                case invariant =>
                  have next : (index + 1).toNat = index.toNat + 1 := by
                    simp [BitVec.toNat_add]
                    omega
                  dsimp only [invariant] at holds ⊢
                  refine ⟨by omega, ?_⟩
                  rw [next, List.take_add_one, List.getElem?_eq_getElem values1Bound, List.foldl_append,
                    ← holds.2]
                  simp
                case measure =>
                  have next : (index + 1).toNat = index.toNat + 1 := by
                    simp [BitVec.toNat_add]
                    omega
                  simp only [measure]
                  omega
            """),
        ("      sorry -- Postcondition at the return at Loops.cs:188",
            """
                  dsimp only [invariant] at holds
                  simp (disch := omega) only [BitVec.toInt_eq_toNat_of_lt, toInt_ofNat_of_lt] at guard
                  simp only [Postcondition, holds.2]
                  rw [List.take_of_length_le (by omega)]
            """)]),
    // An indexed fill stores into the storage span by authority alone; the invariant states the filled prefix
    // from the array's own address.
    ("ArrayFill", [
        ("  values1.reference ≠ .null ∧ sorry", "  values1.reference ≠ .null ∧ True"),
        ("def Postcondition (values1 : ArrayView) (value : W32) (initial final : Memory) : Prop := sorry",
            """
            def Postcondition (values1 : ArrayView) (value : W32) (_ final : Memory) : Prop :=
              ∀ base, values1.reference = .address base →
                Contents final base 4 (List.replicate values1.length (value : BitVec (8 * 4)))
            """),
        ("    (state : State memory written home0) : Prop := sorry",
            """
                (state : State memory written home0) : Prop :=
              state.values.toNat ≤ values1.length ∧ ∀ base, values1.reference = .address base →
                Filled state.memory base 4 (List.replicate state.values.toNat (value : BitVec (8 * 4)))
                  (values1.length - state.values.toNat)
            """),
        ("def measure (values1 : ArrayView) (value : W32)", "def measure (values1 : ArrayView) (_ : W32)"),
        ("    (state : State memory written home0) : Nat := sorry",
            "    (state : State memory written home0) : Nat := values1.length - state.values.toNat"),
        ("    case invariant => sorry -- invariant at the first loop head",
            """
                case invariant =>
                  dsimp only [invariant]
                  refine ⟨by simp, ?_⟩
                  intro base address
                  simp only [ManagedReference.address.injEq] at address
                  subst address
                  have room := (values1Authority.writable values1Base rfl).after_confined
                    storedFrame.confined wellFormed
                  simpa [ArrayView.storage, CIL.ArrayElement.width] using Filled.start room
            """),
        ("""
            case invariant => sorry -- invariant again at the loop head
            case measure => sorry -- measure decreases over this iteration
        """,
            """
                case invariant =>
                  have next : (index + 1).toNat = index.toNat + 1 := by
                    simp [BitVec.toNat_add]
                    omega
                  dsimp only [invariant] at holds ⊢
                  refine ⟨by omega, ?_⟩
                  intro base address
                  simp only [ManagedReference.address.injEq] at address
                  subst address
                  have filled := holds.2 values1Base rfl
                  rw [show values1Length - index.toNat = (values1Length - (index.toNat + 1)) + 1 by omega]
                    at filled
                  rw [next, List.replicate_succ']
                  exact (filled.push (by simpa using values1Wrote)).after_below storedBelow values1Below
                case measure =>
                  have next : (index + 1).toNat = index.toNat + 1 := by
                    simp [BitVec.toNat_add]
                    omega
                  simp only [measure]
                  omega
            """),
        ("    case postcondition => sorry -- Postcondition at the return at Loops.cs:195",
            """
                case postcondition =>
                  dsimp only [invariant] at holds
                  simp only [Postcondition]
                  intro base address
                  simp only [ManagedReference.address.injEq] at address
                  subst address
                  simp (disch := omega) only [BitVec.toInt_eq_toNat_of_lt, toInt_ofNat_of_lt] at guard
                  have done : index.toNat = values1Length := by omega
                  have filled := holds.2 values1Base rfl
                  rw [done, Nat.sub_self] at filled
                  simpa using (filled.after_below exitBelow values1Below).complete
            """)]),
    ("SpanLocalSum", SpanLocalSumSpecification("SpanView", 220)),
    // A span over a whole array, null or not, holds the storage span's elements under the span's access mode.
    ("ArraySpanSum", SpanLocalSumSpecification("ArrayView", 207)),
    // A fill through a writable span over the array has authority over its storage span, as an indexed fill does.
    ("ArraySpanFill", [
        ("def Precondition (values1 : ArrayView) (value : W32) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : ArrayView) (_ : W32) (_ : Memory) : Prop := True"),
        ("def Postcondition (values1 : ArrayView) (value : W32) (initial final : Memory) : Prop := sorry",
            """
            def Postcondition (values1 : ArrayView) (value : W32) (_ final : Memory) : Prop :=
              ∀ base, values1.reference = .address base →
                Contents final base 4 (List.replicate values1.length (value : BitVec (8 * 4)))
            """),
        ("""
        def invariant (values1 : ArrayView) (value : W32)
            {memory : Memory} {written : List (Reference × Nat)} (state : State memory written)
            : Prop := sorry
        """,
            """
            def invariant (values1 : ArrayView) (value : W32)
                {memory : Memory} {written : List (Reference × Nat)} (state : State memory written)
                : Prop :=
              ∀ base, values1.reference = .address base → ∃ done,
                done + state.values.remaining = values1.length ∧
                state.values.view.reference = .address (base.element 4 done) ∧
                Filled state.memory base 4 (List.replicate done (value : BitVec (8 * 4)))
                  state.values.remaining
            """),
        ("""
        def measure (values1 : ArrayView) (value : W32) {memory : Memory} {written : List (Reference × Nat)}
            (state : State memory written) : Nat := sorry
        """,
            """
            def measure (_ : ArrayView) (_ : W32) {memory : Memory} {written : List (Reference × Nat)}
                (state : State memory written) : Nat := state.values.remaining
            """),
        ("    case invariant => sorry -- invariant at the first loop head",
            """
                case invariant =>
                  dsimp only [invariant]
                  intro base address
                  refine ⟨0, by simp, by simp [ArrayView.span, address], ?_⟩
                  have room := (values1Authority.writable base address).after_confined entryFrame.confined
                    wellFormed
                  simp only [ArrayView.storage, values1Type, CIL.ArrayElement.width] at room
                  simpa using Filled.start room
            """),
        ("    case measure => sorry -- measure decreases over this iteration",
            """
                case measure =>
                  simp only [measure]
                  omega
            """),
        ("    case postcondition => sorry -- Postcondition at the return at Loops.cs:232",
            """
                case postcondition =>
                  dsimp only [invariant] at holds
                  intro base address
                  obtain ⟨done, total, -, filled⟩ := holds base address
                  rw [Nat.add_zero] at total
                  subst total
                  exact filled.complete.after_below exitBelow
                    (SpanView.allocation_below (view := values1.storage) values1Valid wellFormed address)
            """),
        ("    case invariant => sorry -- invariant again at the loop head",
            """
                case invariant =>
                  dsimp only [invariant] at holds ⊢
                  intro base address
                  obtain ⟨done, total, place, filled⟩ := holds base address
                  rw [place] at restAddress
                  cases restAddress
                  refine ⟨done + 1, by omega, ?_, ?_⟩
                  · rw [SpanView.slice_reference _ _ _ _ _ _ place restCut, restSpan.elementWidth]
                    simp only [Reference.element, ManagedReference.address.injEq, Reference.mk.injEq,
                      true_and]
                    omega
                  · rw [List.replicate_succ']
                    exact filled.push (by simpa using restWrote)
            """)]),
    // A length of the array a field holds leaves memory as it was.
    ("SampleCount", [
        ("def Precondition (samples : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (samples : Reference) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (_ : Reference) (initial final : Memory) (_ : W32) : Prop := final = initial"),
        ("sorry -- Postcondition of the returned value", "rfl")]),
    // The field holds the array argument's origin.
    ("SampleRefill", [
        ("def Precondition (samples : Reference) (values1 : ArrayView) (values1Elements : List W32)\n" +
            "    (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : ArrayView) (_ : List W32) (_ : Memory) : Prop := True"),
        ("def Postcondition (samples : Reference) (values1 : ArrayView) (values1Elements : List W32)\n" +
            "    (initial final : Memory) : Prop := sorry",
            "def Postcondition (samples : Reference) (values1 : ArrayView) (_ : List W32) " +
            "(_ final : Memory) : Prop :=\n" +
            "  Samples.Values.Holds final samples values1.reference"),
        ("sorry -- Postcondition of the returned value, with `held1` the stored fields",
            "simpa only [Postcondition, leaveFrame, List.foldl_nil, values1Reference] using held1")]),
    // The returned view is of the array the field holds.
    ("SampleValues", [
        ("def Precondition (samples : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (samples : Reference) (initial final : Memory) (result : ArrayView)\n" +
            "    : Prop := sorry",
            "def Postcondition (samples : Reference) (initial final : Memory) (result : ArrayView) : Prop :=\n" +
            "  result.reference = Samples.Values.of initial samples ∧ final = initial"),
        ("sorry -- Postcondition of the returned value", "exact ⟨samplesValuesHeld.symm, rfl⟩")]),
    // The target's field holds what the source's held, whose length is read after the store.
    ("SampleShare", [
        ("def Precondition (source target1 : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (source target1 : Reference) (initial final : Memory) (result : W32)\n" +
            "    : Prop := sorry",
            "def Postcondition (source target1 : Reference) (initial final : Memory) (_ : W32) : Prop :=\n" +
            "  Samples.Values.Holds final target1 (Samples.Values.of initial source)"),
        ("sorry -- Postcondition of the returned value, with `held1` the stored fields",
            "rw [Postcondition, sourceValuesHeld]\n  exact held1")]),
    // A struct array's length leaves memory as it was.
    ("TilePairCount", [
        ("def Precondition (tiles : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (tiles : Reference) (initial final : Memory) (result : W32) : Prop := sorry",
            "def Postcondition (_ : Reference) (initial final : Memory) (_ : W32) : Prop := final = initial"),
        ("sorry -- Postcondition of the returned value", "rfl")]),
    // The field holds the vector array argument's origin.
    ("TileRelane", [
        ("def Precondition (tiles lanes : Reference) (lanesLength : Nat) (initial : Memory) : Prop := sorry",
            "def Precondition (_ _ : Reference) (_ : Nat) (_ : Memory) : Prop := True"),
        ("def Postcondition (tiles lanes : Reference) (lanesLength : Nat) (initial final : Memory)\n" +
            "    : Prop := sorry",
            "def Postcondition (tiles lanes : Reference) (_ : Nat) (_ final : Memory) : Prop :=\n" +
            "  Tiles.Lanes.Holds final tiles (.address lanes)"),
        ("sorry -- Postcondition of the returned value, with `held1` the stored fields", "exact held1")]),
    // The returned view is of the struct array the field holds.
    ("TilePairs", [
        ("def Precondition (tiles : Reference) (initial : Memory) : Prop := sorry",
            "def Precondition (_ : Reference) (_ : Memory) : Prop := True"),
        ("def Postcondition (tiles : Reference) (initial final : Memory) (result : ArrayView) : Prop := sorry",
            "def Postcondition (tiles : Reference) (initial final : Memory) (result : ArrayView) : Prop :=\n" +
            "  result.reference = Tiles.Pairs.of initial tiles ∧ final = initial"),
        ("sorry -- Postcondition of the returned value", "exact ⟨tilesPairsHeld.symm, rfl⟩")])
})
{
    if (!catalog.Any(entry => entry.Name == name))
        throw new InvalidOperationException("Filled outline absent from the catalog: " + name);
    if (!Selected(name)) continue;
    var source = File.ReadAllText(Path.Combine(outlineRoot, name, "Proof.lean"));
    foreach (var (hole, replacement) in fills)
    {
        if (Regex.Matches(source, Regex.Escape(hole)).Count != 1)
            throw new InvalidOperationException($"The {name} outline lacks the hole {hole}:\n{source}");
        source = source.Replace(hole, replacement, StringComparison.Ordinal);
    }
    if (Regex.IsMatch(source, @"(?<![`\w])sorry(?![`\w])"))
        throw new InvalidOperationException($"The {name} outline has a hole the test does not fill:\n{source}");
    var filledOutline = Path.Combine(outlineRoot, name, "Filled.lean");
    File.WriteAllText(filledOutline, source);
    var verified = Execute(Cli("verify", OutlineExtraction(name), "--proof", filledOutline));
    if (verified.Code != 0 || !verified.Stdout.StartsWith("Verified: ExampleProof.correctness"))
        throw new InvalidOperationException($"The filled {name} outline did not verify:\n{verified.Output}");
}
Console.WriteLine($"PASS filled {group} outlines verify with only their specification written");

if (Selected("PacketValue"))
{
    // The same filled packet proof must reject a changed stored value for all initial byte patterns.
    var wrongPacket = Path.Combine(outlineRoot, "WrongPacket.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Arguments").Methods.Single(method => method.Name == "Struct");
        method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Ldc_I4_S).Operand = (sbyte)24;
        module.Write(wrongPacket);
    }
    var wrongPacketOutput = Path.Combine(outlineRoot, "WrongPacket");
    Run(Extract("extract", wrongPacket, "Examples", "Arguments::Struct(Examples.Packet)", wrongPacketOutput));
    var wrongPacketResult = Execute(Cli("verify", wrongPacketOutput, "--proof",
        Path.Combine(outlineRoot, "PacketValue", "Filled.lean")));
    if (wrongPacketResult.Code == 0 || !wrongPacketResult.Output.Contains("Stage: proof checking") ||
        File.Exists(Path.Combine(wrongPacketOutput, "verified.json")))
        throw new InvalidOperationException("The filled packet outline accepted a wrong stored value:\n" +
            wrongPacketResult.Output);
    Console.WriteLine("PASS the filled packet outline rejects a wrong stored value");

    // A source parameter named index must remain the byte vector, not a generated byte-index binder.
    var indexedPacket = Path.Combine(outlineRoot, "IndexedPacket.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Arguments").Methods.Single(method => method.Name == "Struct");
        method.Parameters[0].Name = "index";
        module.Write(indexedPacket);
    }
    var indexedPacketOutput = Path.Combine(outlineRoot, "IndexedPacket");
    Run(Extract("extract", indexedPacket, "Examples", "Arguments::Struct(Examples.Packet)", indexedPacketOutput));
    var indexedPacketProof = Path.Combine(outlineRoot, "IndexedPacket.lean");
    Run(Cli("new-proof", indexedPacketOutput, indexedPacketProof));
    var indexedPacketSource = File.ReadAllText(indexedPacketProof)
        .Replace("def Precondition (index : Vector (BitVec 8) 12) : Prop := sorry",
            "def Precondition (_ : Vector (BitVec 8) 12) : Prop := True", StringComparison.Ordinal)
        .Replace("def Postcondition (index : Vector (BitVec 8) 12) (result : W64) : Prop := sorry",
            "def Postcondition (_ : Vector (BitVec 8) 12) (result : W64) : Prop := result = 23",
            StringComparison.Ordinal)
        .Replace("sorry -- Postcondition of the returned value", "rfl", StringComparison.Ordinal);
    File.WriteAllText(indexedPacketProof, indexedPacketSource);
    Run(Cli("verify", indexedPacketOutput, "--proof", indexedPacketProof));
    Console.WriteLine("PASS a struct parameter named index is bound without capture");
}

if (Selected("FillWords"))
{
    // A written footprint that leaves out the element a loop writes is an error at the write, never an admission.
    var narrowed = Path.Combine(outlineRoot, "FillWords", "Narrowed.lean");
    File.WriteAllText(narrowed, File.ReadAllText(Path.Combine(outlineRoot, "FillWords", "Filled.lean"))
        .Replace("  [(destination, 8 * count.toNat)]", "  []", StringComparison.Ordinal));
    var outside = Execute(Cli("verify", OutlineExtraction("FillWords"), "--proof", narrowed));
    if (outside.Code == 0 || !outside.Output.Contains("cil_loop_obligation could not prove"))
        throw new InvalidOperationException("verify did not reject a write outside the footprint:\n" + outside.Output);
    Console.WriteLine("PASS a loop write outside its written footprint is an error at the write");
}

if (Selected("ArraySum"))
{
    // The loop reads the array's length, so its outline must show the null exclusion where the author writes the
    // precondition, and a precondition without it must fail naming null, not an unexplained `False`.
    var sumOutline = File.ReadAllText(Path.Combine(outlineRoot, "ArraySum", "Proof.lean"));
    if (!sumOutline.Contains("""
              -- `values1` is not null: `values.Length` throws on a null array.
              values1.reference ≠ .null ∧ sorry
            """, StringComparison.Ordinal) ||
        // The header wraps where its text falls, so the sentence is matched across line breaks.
        !Regex.Replace(sumOutline, @"\s+", " ").Contains("The C# parameter `values` is bound as `values1`",
            StringComparison.Ordinal))
        throw new InvalidOperationException("The ArraySum outline does not show its null exclusion or its renamed " +
            "parameter:\n" + sumOutline);
    var nullable = Path.Combine(outlineRoot, "ArraySum", "Nullable.lean");
    File.WriteAllText(nullable, File.ReadAllText(Path.Combine(outlineRoot, "ArraySum", "Filled.lean"))
        .Replace("  values1.reference ≠ .null ∧ True", "  True", StringComparison.Ordinal));
    var admitsNull = Execute(Cli("verify", OutlineExtraction("ArraySum"), "--proof", nullable));
    if (admitsNull.Code == 0 || !admitsNull.Output.Contains("Stage: proof checking") ||
        !admitsNull.Output.Contains("Precondition must exclude null: `values1.reference ≠ .null`"))
        throw new InvalidOperationException("verify did not name the null array a precondition admits:\n" +
            admitsNull.Output);
    Console.WriteLine("PASS an indexed loop's outline states the null exclusion, and a precondition without it " +
        "fails naming null");
}

if (Selected("ReceiverArraySum"))
{
    // An array beside the receiver of a class instance method keeps its element view, so the indexed loop steps.
    var receiverSum = File.ReadAllText(Path.Combine(outlineRoot, "ReceiverArraySum", "Proof.lean"));
    if (receiverSum.Contains("-- not outlined:", StringComparison.Ordinal) ||
        !receiverSum.Contains("  readings.reference ≠ .null ∧ sorry", StringComparison.Ordinal) ||
        !receiverSum.Contains(".array_load", StringComparison.Ordinal))
        throw new InvalidOperationException("The ReceiverArraySum outline does not step its indexed loop:\n" +
            receiverSum);
    Console.WriteLine("PASS an indexed loop over an array beside a class receiver is outlined with no path left");
}

// A helper's contract is proved, never assumed: a `post` the helper's body does not meet fails in its `Holds`
// theorem, whether that steps words alone or the fields of an object, and one the caller's postcondition does not
// follow from fails at the caller.
foreach (var (helper, label, stated, wrong) in new[]
{
    ("HelperResult", "a post its helper does not meet", "final = initial ∧ result.toInt = min value.toInt limit.toInt",
        "final = initial ∧ result.toInt = max value.toInt limit.toInt"),
    ("HelperResult", "a postcondition its helper's post does not give", $"  result.toInt = {smallerLevel}",
        "  result = Gauge.Level.of initial gauge"),
    ("HelperObject", "a post its object helper does not meet",
        "final = initial ∧ result.toInt = min value.toInt (Gauge.Limit.of initial gauge).toInt",
        "final = initial ∧ result.toInt = max value.toInt (Gauge.Limit.of initial gauge).toInt")
})
{
    if (!Selected(helper)) continue;
    var helperFilled = File.ReadAllText(Path.Combine(outlineRoot, helper, "Filled.lean"));
    if (!helperFilled.Contains(stated, StringComparison.Ordinal))
        throw new InvalidOperationException($"The {helper} proof lacks the text of {label}");
    var wrongProof = Path.Combine(outlineRoot, helper, "Wrong.lean");
    File.WriteAllText(wrongProof, helperFilled.Replace(stated, wrong, StringComparison.Ordinal));
    var rejected = Execute(Cli("verify", OutlineExtraction(helper), "--proof", wrongProof));
    if (rejected.Code == 0 || !rejected.Output.Contains("Stage: proof checking") ||
        File.Exists(Path.Combine(OutlineExtraction(helper), "verified.json")))
        throw new InvalidOperationException($"verify accepted {label}:\n{rejected.Output}");
    Console.WriteLine($"PASS a helper's contract is proved: {label} is rejected");
}

// A `pre` that admits the side where the helper throws leaves that side unproved: an error that says the path
// must be ruled out, never a hole, whether the helper is over words or reads an object.
foreach (var (helper, bound, admitting) in new[]
{
    ("HelperThrows", "memory => value.toInt ≤ limit.toInt", "memory => True"),
    ("HelperObjectThrows", "gauge ∧ value.toInt ≤ (Gauge.Limit.of memory gauge).toInt", "gauge ∧ True")
})
{
    if (!Selected(helper)) continue;
    var filledThrow = File.ReadAllText(Path.Combine(outlineRoot, helper, "Filled.lean"));
    if (!filledThrow.Contains(bound, StringComparison.Ordinal))
        throw new InvalidOperationException($"The {helper} proof lacks the precondition that excludes its throw");
    var open = Path.Combine(outlineRoot, helper, "Open.lean");
    File.WriteAllText(open, filledThrow.Replace(bound, admitting, StringComparison.Ordinal)
        .Replace("    exact assumed", "    trivial", StringComparison.Ordinal));
    var admitsThrow = Execute(Cli("verify", OutlineExtraction(helper), "--proof", open));
    if (admitsThrow.Code == 0 || !admitsThrow.Output.Contains("Stage: proof checking") ||
        !admitsThrow.Output.Contains("cil_loop_obligation could not prove") ||
        !admitsThrow.Output.Contains("state what rules it out"))
        throw new InvalidOperationException($"verify accepted a {helper} precondition that admits its throw:\n" +
            admitsThrow.Output);
    Console.WriteLine($"PASS a {helper} precondition that admits the side where it throws is rejected in its proof");
}

// One hole left, an obligation or a path the outline could not step, keeps an outline from certifying:
// verify refuses it for `sorryAx` and removes the report the filled proof left.
var unfinished = new List<(string Name, string Source)>();
if (Selected("SpanSum"))
    unfinished.Add(("SpanSum", File.ReadAllText(Path.Combine(outlineRoot, "SpanSum", "Filled.lean"))
        .Replace("case measure => simp [measure]", "case measure => sorry")));
var unstepped = outlined.Select(entry => entry.Name).FirstOrDefault(name => File.ReadAllText(
    Path.Combine(outlineRoot, name, "Proof.lean")).Contains("-- not outlined:", StringComparison.Ordinal));
if (unstepped is not null)
    unfinished.Add((unstepped, File.ReadAllText(Path.Combine(outlineRoot, unstepped, "Proof.lean"))));
foreach (var (name, source) in unfinished)
{
    var partial = Path.Combine(outlineRoot, name, "Unfinished.lean");
    File.WriteAllText(partial, source);
    var refused = Execute(Cli("verify", OutlineExtraction(name), "--proof", partial));
    if (refused.Code == 0 || !refused.Output.Contains("Unapproved proof axioms: sorryAx") ||
        refused.Output.Contains(": error") || File.Exists(Path.Combine(OutlineExtraction(name), "verified.json")))
        throw new InvalidOperationException($"verify did not refuse the unfinished {name} outline:\n{refused.Output}");
}
if (unfinished.Count > 0) Console.WriteLine(unstepped is null
    ? "PASS verify refuses an outline with one obligation left; no outline leaves a path not outlined"
    : $"PASS verify refuses an outline with one obligation left and the {unstepped} outline's path not outlined");

string OutlineExtraction(string name) => Path.Combine(outlineRoot, name, "Extraction");

if (group == "control")
{
    // LeanCIL's own closure that lays out a static word's bytes: its outline states the getter's contract
    // and steps through it, and the checked-in proof fills only the outline's holes and verifies.
    var wordByte = Path.Combine(outlineRoot, "WordByte");
    var wordByteExtraction = Path.Combine(wordByte, "Extraction");
    Run(Cli("extract", At("Extractor/bin/Nethermind.LeanCIL.dll"),
        "Nethermind.LeanCIL.StaticValues/<>c__DisplayClass10_0::<Bytes>b__0(System.Int32)", wordByteExtraction));
    var wordByteOutline = Path.Combine(wordByte, "Proof.lean");
    Run(Cli("new-proof", wordByteExtraction, wordByteOutline));
    var wordByteSource = File.ReadAllText(wordByteOutline);
    if (wordByteSource.Contains("-- not outlined:", StringComparison.Ordinal) ||
        !wordByteSource.Contains("theorem get_Bits_holds", StringComparison.Ordinal))
        throw new InvalidOperationException("The closure outline does not step its getter call:\n" + wordByteSource);
    static string Statement(string source) =>
        Regex.Match(source.ReplaceLineEndings("\n"), @"^theorem correctness .*?:= by$",
            RegexOptions.Singleline | RegexOptions.Multiline).Value;
    var wordByteProof = At("Tests/Outlines/WordByte.lean");
    var outlineStatement = Statement(wordByteSource);
    if (outlineStatement.Length == 0 || outlineStatement != Statement(File.ReadAllText(wordByteProof)))
        throw new InvalidOperationException("Tests/Outlines/WordByte.lean no longer states the outline's theorem:\n" +
            outlineStatement);
    var wordByteVerified = Execute(Cli("verify", wordByteExtraction, "--proof", wordByteProof));
    if (wordByteVerified.Code != 0 || !wordByteVerified.Stdout.StartsWith("Verified: ExampleProof.correctness"))
        throw new InvalidOperationException("The closure's filled outline did not verify:\n" + wordByteVerified.Output);
    Console.WriteLine("PASS the outline of LeanCIL's own byte-layout closure, filled, verifies its little-endian byte");
}
