#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/LibraryAudit.cs

using System.Text.Json;

var listsOnly = args is ["--lists-only"];
if (!listsOnly) Run(["dotnet", "run", "--file", "Tests/ConsumerInspection.cs"]);
using var verification = new Program();
var root = At("artifacts/OleanAudit");
if (Directory.Exists(root)) Directory.Delete(root, true);
Directory.CreateDirectory(root);

if (!listsOnly)
{
// Each proof below certifies the addition contract for the subtraction method, so any acceptance is unsound.
var assembly = At("Examples/Assembly/bin/Examples.dll");
const string wrongAdd = "System.UInt64 Examples.Arithmetic::WrongAdd(System.UInt64,System.UInt64)";
var addProof = File.ReadAllText(At("Examples/Proofs/Add.lean"));
// The addition contract, proved for any program from an unapproved axiom.
const string axiomProof = """
    import Extracted
    import CIL.Safety.Execution

    open CIL
    namespace ExampleProof
    axiom bogus : False
    theorem correctness (x y : W64) :
        ∃ result : W64,
          (CIL.Safety.invoke Extracted.program 4 0
            [.scalar (.i64 x), .scalar (.i64 y)] CIL.Safety.Memory.empty).map Prod.snd =
              .ok [.scalar (.i64 result)] ∧
          result.toNat = (x.toNat + y.toNat) % 2^64 := bogus.elim
    end ExampleProof

    """;
const string forgedAudit = "'ExampleProof.correctness' does not depend on any axioms";

void Forged(string name, string proof, string marker)
{
    var output = Path.Combine(root, name);
    var path = Path.Combine(root, name + ".lean");
    File.WriteAllText(path, proof);
    try { verification.Verify(assembly, "Examples", wrongAdd, path, output); }
    catch (InvalidOperationException error) when (error.Message.Contains(marker, StringComparison.Ordinal))
    {
        if (File.Exists(Path.Combine(output, "verified.json"))) throw new InvalidOperationException("Rejected proof left a certificate: " + name);
        Console.WriteLine("PASS forged audit rejected: " + name);
        return;
    }
    throw new InvalidOperationException("Forged theorem audit certified WrongAdd: " + name);
}

// An imported elaborator rewrites the `#print axioms` command an elaborated audit would run.
Forged("elab-rules", axiomProof.Replace("import Extracted\n", "import Extracted\nimport Lean\n") + $$"""

    open Lean Elab Command in
    elab_rules : command
      | `(#print axioms $id) => logInfo m!"'{id.getId}' does not depend on any axioms"
    """, "Unapproved proof axioms: ExampleProof.bogus");

// An initializer runs whenever an elaborated audit imports the proof, and can forge its whole output.
Forged("initialize", axiomProof + $$"""

    initialize do
      IO.println "{{forgedAudit}}"
      IO.Process.exit (α := Unit) 0
    """, "Unapproved proof axioms: ExampleProof.bogus");

// Building the proof runs its code, which can rewrite any audit source written next to it.
Forged("run-cmd-audit", axiomProof.Replace("import Extracted\n", "import Extracted\nimport Lean\n") + $$"""

    open Lean Elab Command in
    run_cmd do
      let dir := ((← getFileName) : System.FilePath).parent.get!
      IO.FS.writeFile (dir / "Audit.lean") "#eval IO.println \"{{forgedAudit}}\"\n"
    """, "Unapproved proof axioms: ExampleProof.bogus");

// The build swaps in the addition program and its honest proof, then exits before writing its own olean.
// Kernel replay then accepts the substitutes, so only binding the replayed bytes to the extraction rejects it.
var honest = Path.Combine(root, "honest");
Run(Extract("extract", assembly, "Examples", "Arithmetic::Add(ulong,ulong)", honest));
var substitutes = Path.Combine(root, "substitutes");
Directory.CreateDirectory(substitutes);
File.Copy(Path.Combine(honest, "Extracted.lean"), Path.Combine(substitutes, "Extracted.lean"));
File.WriteAllText(Path.Combine(substitutes, "Proof.lean"), addProof);
var forgedRoot = substitutes.Replace('\\', '/');
Forged("substituted-oleans", $$"""
    import Extracted
    import Lean
    open Lean Elab Command in
    run_cmd do
      let dir := ((← getFileName) : System.FilePath).parent.get!
      let lean := (← IO.appPath).toString
      for module in ["Extracted", "Proof"] do
        let args := #["--root={{forgedRoot}}", "-o", (dir / s!"{module}.olean").toString, s!"{{forgedRoot}}/{module}.lean"]
        let out ← IO.Process.output { cmd := lean, args }
        unless out.exitCode == 0 do throwError m!"{out.stdout}{out.stderr}"
      IO.Process.exit (α := Unit) 0
    """, "Compiled artifacts changed during verification");
}

// Checker-level cases: modules compiled directly, audited without elaborating any source.
var fixtures = Path.Combine(root, "fixtures");
Directory.CreateDirectory(fixtures);
verification.Library(Inputs(At("CIL.lean")));
var fixtureSearch = fixtures + Path.PathSeparator + Path.Combine(verification.library!, ".lake/build/lib/lean");
var environment = new Dictionary<string, string> { ["LEAN_SYSROOT"] = verification.Toolchain };
void Compile(string module, string source)
{
    var path = Path.Combine(fixtures, module.Replace('.', Path.DirectorySeparatorChar) + ".lean");
    Directory.CreateDirectory(Path.GetDirectoryName(path)!);
    File.WriteAllText(path, source);
    Run([verification.LeanExecutable, "--root=" + fixtures, "-o", Path.ChangeExtension(path, ".olean"), path],
        fixtures, fixtureSearch, environment: environment);
}
string Elaborated(string source)
{
    var path = Path.Combine(fixtures, "Elaborated.lean");
    File.WriteAllText(path, source);
    return Run([verification.LeanExecutable, "--root=" + fixtures, path], fixtures, fixtureSearch,
        environment: environment);
}
AuditedOleans Audit(string module, AuditRequest[] theorems, AuditConstantRequest[]? constants = null) =>
    verification.AuditOleans(fixtures, [module], theorems, constants);
void Rejected(AuditedTheorem audited, string marker)
{
    try { AuditedAxioms(audited); }
    catch (InvalidOperationException error) when (error.Message.Contains(marker, StringComparison.Ordinal)) { return; }
    throw new InvalidOperationException($"Expected audit rejection ({marker}): {JsonSerializer.Serialize(audited)}");
}
object Const(string name, params int[] levels) => new { @const = name, levels };
object App(params object[] parts) => new { app = parts };
object Nat(int n) => new { nat = n };

object ListPattern(object type, object level, params object[] items) => new { list = new { type, level, items } };
object NestedList(object type, int level, params object[] items) =>
    items.Reverse().Aggregate(App(Const("List.nil", level), type),
        (tail, item) => App(Const("List.cons", level), type, item, tail));
var listNat = Const("Nat");
Compile("Lists", """
    def Lists.empty : List Nat := []
    def Lists.single : List Nat := [1]
    def Lists.many : List Nat := [1, 2, 3]
    def Lists.alias : List Nat := Lists.many
    def Lists.append : List Nat := [1] ++ [2, 3]
    def Lists.types : List Type := [Nat, Bool]
    """);
var listCases = new (string Name, object Pattern, bool Accept)[]
{
    ("empty", ListPattern(listNat, 0), true),
    ("single", ListPattern(listNat, 0, Nat(1)), true),
    ("many", ListPattern(listNat, 0, Nat(1), Nat(2), Nat(3)), true),
    ("types", ListPattern(new { sort = 1 }, 1, Const("Nat"), Const("Bool")), true),
    ("many", ListPattern(Const("Bool"), 0, Nat(1), Nat(2), Nat(3)), false),
    ("many", ListPattern(listNat, 1, Nat(1), Nat(2), Nat(3)), false),
    ("many", ListPattern(listNat, 0, Nat(2), Nat(1), Nat(3)), false),
    ("many", ListPattern(listNat, 0, Nat(1), Nat(2)), false),
    ("many", ListPattern(listNat, 0, Nat(1), Nat(2), Nat(3), Nat(4)), false),
    ("many", ListPattern(listNat, 0, Nat(1), Nat(2), Nat(4)), false),
    ("empty", ListPattern(Const("Bool"), 0), false),
    ("empty", ListPattern(listNat, 1), false),
    ("alias", ListPattern(listNat, 0, Nat(1), Nat(2), Nat(3)), false),
    ("append", ListPattern(listNat, 0, Nat(1), Nat(2), Nat(3)), false)
};
var listResults = Audit("Lists", [], [.. listCases.Select(test =>
    new AuditConstantRequest("Lists." + test.Name, test.Pattern))]).constants;
for (var index = 0; index < listCases.Length; index++)
    if ((listResults[index].error is null) != listCases[index].Accept)
        throw new InvalidOperationException("List structural audit: " + JsonSerializer.Serialize(listResults[index]));

// These expressions exercise constructor shape independently of Lean's type checker.
string Expected(object pattern) => "(Json.parse " + LeanString(JsonSerializer.Serialize(pattern)) +
    ").toOption.get!";
var flat = Expected(ListPattern(listNat, 0, new { lit = 1 }, "_"));
var nestedList = Expected(NestedList(listNat, 0, new { lit = 1 }, "_"));
var flatAnyType = Expected(ListPattern("_", 0, new { lit = 1 }, "_"));
var nestedAnyType = Expected(NestedList("_", 0, new { lit = 1 }, "_"));
var malformedPatterns = new object[]
{
    new { list = new { level = 0, items = Array.Empty<object>() } },
    new { list = new { type = listNat, items = Array.Empty<object>() } },
    new { list = new { type = listNat, level = 0 } },
    new { list = new { type = listNat, level = "bad", items = Array.Empty<object>() } },
    new { list = new { type = listNat, level = 0, items = "bad" } },
    new { list = new { type = 42, level = 0, items = Array.Empty<object>() } }
};
var malformedChecks = string.Join("\n", malformedPatterns.Select(pattern =>
    "  unless (LeanCILAudit.fits " + Expected(pattern) +
    " nil).toOption.isNone do throw <| IO.userError \"fields\""));
Elaborated($$"""
    import CIL.OleanAudit
    open Lean
    #eval show IO Unit from do
      let ty := mkConst ``Nat
      let nil := mkApp (mkConst ``List.nil [.zero]) ty
      let cons := fun ty head tail => mkApp3 (mkConst ``List.cons [.zero]) ty head tail
      let one := mkRawNatLit 1
      let two := mkRawNatLit 2
      let good := cons ty one (cons ty two nil)
      let bad := #[nil, cons ty one nil, cons ty two (cons ty one nil),
        cons (mkConst ``Bool) one (cons ty two nil),
        cons ty one (cons (mkConst ``Bool) two nil),
        cons ty one (cons ty two (mkApp (mkConst ``List.nil [.zero]) (mkConst ``Bool))),
        mkApp3 (mkConst ``List.cons [.succ .zero]) ty one (cons ty two nil),
        mkApp3 (mkConst ``List.cons []) ty one (cons ty two nil),
        mkApp3 (mkConst ``List.cons [.zero, .zero]) ty one (cons ty two nil),
        cons ty one (cons ty two (mkApp (mkConst ``List.nil [.succ .zero]) ty)),
        cons ty one (cons ty two (mkApp (mkConst ``List.nil []) ty)),
        cons ty one (cons ty two (mkApp (mkConst ``List.nil [.zero, .zero]) ty)),
        mkApp good one, mkApp2 (mkConst ``List.cons [.zero]) ty one,
        cons ty one (cons ty two (mkConst ``List.nil [.zero])),
        cons ty one (cons ty two (mkApp nil one)),
        mkMData {} good]
      unless (LeanCILAudit.fits {{flat}} good).toOption == some true do throw <| IO.userError "good"
      for expr in bad do
        unless (LeanCILAudit.fits {{flat}} expr).toOption == some false do throw <| IO.userError "shape"
      for expr in bad.push good do
        unless (LeanCILAudit.fits {{flat}} expr).toOption ==
            (LeanCILAudit.fits {{nestedList}} expr).toOption do
          throw <| IO.userError "nested equivalence"
        unless (LeanCILAudit.fits {{flatAnyType}} expr).toOption ==
            (LeanCILAudit.fits {{nestedAnyType}} expr).toOption do
          throw <| IO.userError "wildcard type equivalence"
    {{malformedChecks}}
    """);
Console.WriteLine("PASS flat lists check every constructor type, universe, item, arity and exact tail");

int previousRequestSize = 0;
Compile("StrictBinding.Image", """
    namespace StrictBinding
    structure PinnedImage where
      identity : String
      image : Nat
    end StrictBinding
    """);
int? requestDepth = null;
int Depth(JsonElement element) => element.ValueKind switch
{
    JsonValueKind.Array => 1 + element.EnumerateArray().Select(Depth).DefaultIfEmpty().Max(),
    JsonValueKind.Object => 1 + element.EnumerateObject().Select(property => Depth(property.Value))
        .DefaultIfEmpty().Max(),
    _ => 0
};
foreach (var count in new[] { 16, 128, 1024 })
{
    BindingImagePin[] pins = [.. Enumerable.Range(0, count).Select(index =>
        new BindingImagePin("Identity" + index,
            Sha256Digest.Parse((index % 2).ToString("x16") + new string('0', 48), "a test pin"), []))];
    BindingPlan plan = new("", pins, 0);
    foreach (var pin in pins.DistinctBy(pin => pin.Module))
        Compile(pin.Module, "def " + pin.Module + ".image : Nat := 0\n");
    Compile(ImagesModule, ImagesModuleSource(plan));
    AuditedAxioms(Audit(ImagesModule, [BindingRequests(plan)[1].Audit]).theorems[0]);
    var serialized = JsonSerializer.Serialize(BindingRequests(plan).Select(request => request.Audit), AuditJson);
    using var parsed = JsonDocument.Parse(serialized);
    var depth = Depth(parsed.RootElement);
    requestDepth ??= depth;
    if (depth != requestDepth) throw new InvalidOperationException("Binding request depth grows with pin count");
    var items = parsed.RootElement[1].GetProperty("type").GetProperty("app")[3]
        .GetProperty("list").GetProperty("items");
    if (items.GetArrayLength() != count ||
        items.EnumerateArray().Where((item, index) =>
            item.GetProperty("app")[1].GetProperty("str").GetString() != pins[index].Identity ||
            item.GetProperty("app")[2].GetProperty("const").GetString() != pins[index].Module + ".image").Any() ||
        previousRequestSize != 0 && serialized.Length > previousRequestSize * 9)
        throw new InvalidOperationException("Binding list serialization growth or order");
    previousRequestSize = serialized.Length;
    var module = "ListScale" + count;
    Compile(module, "set_option maxRecDepth 10000\ndef " + module + ".values : List Nat := " +
        string.Concat(Enumerable.Range(0, count).Select(index => "@List.cons Nat " + index + " (")) +
        "@List.nil Nat" + new string(')', count) + "\n");
    var audited = Audit(module, [], [new(module + ".values",
        ListPattern(listNat, 0, [.. Enumerable.Range(0, count).Select(Nat)]))]);
    if (audited.constants[0].error is not null)
        throw new InvalidOperationException("Large list audit: " + audited.constants[0].error);
    Console.WriteLine($"PASS {count} pins: {serialized.Length} characters, depth {depth}, list audited");
}
Console.WriteLine(Elaborated("""
    import CIL.OleanAudit
    open Lean
    #eval show IO Unit from do
      let ty := mkConst ``Nat
      let nil := mkApp (mkConst ``List.nil [.zero]) ty
      let cons := fun head tail => mkApp3 (mkConst ``List.cons [.zero]) ty head tail
      let mut previous := 0
      let mut iterations := 1
      let mut baseline := 0
      let minimumNanos := 25000000
      for count in [16, 128, 1024] do
        let mut tail := nil
        for index in [:count - 1] do tail := cons (mkNatLit index) tail
        let pattern := Json.mkObj [("list", Json.mkObj [
          ("type", Json.mkObj [("const", toJson "Nat")]), ("level", toJson (0 : Nat)),
          ("items", toJson (Array.replicate count (Json.str "_")))])]
        let started <- IO.getNumHeartbeats
        for iteration in [:1000] do
          unless (LeanCILAudit.fits pattern (cons (mkNatLit iteration) tail)).toOption == some true do
            throw <| IO.userError "matcher scaling result"
        let used := (<- IO.getNumHeartbeats) - started
        IO.println s!"PASS list matcher {count}: {used} heartbeats for 1000 matches"
        if previous > 0 && used > previous * 12 then
          throw <| IO.userError "list matcher growth exceeds linear allowance"
        previous := used
        let measure := fun repeats => do
          let mut best := 1000000000000
          for _ in [:5] do
            let start <- IO.monoNanosNow
            for iteration in [:repeats] do
              let result := LeanCILAudit.fits pattern (cons (mkNatLit iteration) tail)
              unless result.toOption == some true do
                throw <| IO.userError "matcher timing result"
            best := min best ((<- IO.monoNanosNow) - start)
          return best
        let mut elapsed <- measure iterations
        if count == 16 then
          while elapsed < minimumNanos do
            iterations := iterations * 2
            elapsed <- measure iterations
          baseline := elapsed
        -- Allocation-free quadratic traversal costs 4096x at 64x items, above the 256x bound.
        if count == 1024 && elapsed > baseline * 256 then
          throw <| IO.userError "list matcher time exceeds linear allowance"
        IO.println s!"PASS list matcher {count}: {elapsed} ns for {iterations} matches"
    """));
if (listsOnly) return;

// These fixtures elaborate successfully, so rejection exercises the audit rather than a syntax error.
Compile("Overrides", """
    import Lean
    axiom Overrides.bogus : 1 = 2
    theorem Overrides.claimed : 1 = 2 := Overrides.bogus
    open Lean Elab Command in
    elab_rules : command
      | `(#print axioms $id) => logInfo m!"'{id.getId}' does not depend on any axioms"
    """);
if (!Elaborated("import Overrides\n#print axioms Overrides.claimed\n").Contains("'Overrides.claimed' does not depend on any axioms"))
    throw new InvalidOperationException("The #print axioms override no longer fools an elaborated audit");
var overridden = Audit("Overrides", [ProofTheorem("Overrides.claimed")]).theorems[0];
if (overridden.axioms is not ["Overrides.bogus"]) throw new InvalidOperationException("Override hid the axiom closure");
Rejected(overridden, "Unapproved proof axioms: Overrides.bogus");
Compile("Initializes", """
    axiom Initializes.bogus : 1 = 2
    theorem Initializes.claimed : 1 = 2 := Initializes.bogus
    initialize do
      IO.println "'Initializes.claimed' does not depend on any axioms"
      IO.Process.exit (α := Unit) 0
    """);
if (Elaborated("import Initializes\n#print axioms Initializes.claimed\n").Trim() != "'Initializes.claimed' does not depend on any axioms")
    throw new InvalidOperationException("The initializer no longer forges an elaborated audit");
Rejected(Audit("Initializes", [ProofTheorem("Initializes.claimed")]).theorems[0], "Unapproved proof axioms: Initializes.bogus");
Console.WriteLine("PASS imported elaborators and initializers neither run nor hide axioms");

// A proof environment can retarget a numeral, so the printed statement `0 = 1` means `1 = 1`.
Compile("Retargets", "instance (priority := high) Retargets.zero : OfNat Nat 0 := ⟨1⟩\ntheorem Retargets.claim : (0 : Nat) = 1 := rfl\n");
Compile("Canonical", "theorem Canonical.claim : (1 : Nat) = 1 := rfl\n");
if (!Elaborated("import Retargets\n#check Retargets.claim\n").Contains("Retargets.claim : 0 = 1"))
    throw new InvalidOperationException("The retargeted numeral no longer prints as the canonical one");
AuditRequest Equation(string theorem, int left, int right) =>
    new(theorem, App(Const("Eq", 1), Const("Nat"), Nat(left), Nat(right)), ApprovedAxioms);
Rejected(Audit("Retargets", [Equation("Retargets.claim", 0, 1)]).theorems[0], "Theorem statement mismatch: Retargets.claim");
AuditedAxioms(Audit("Canonical", [Equation("Canonical.claim", 1, 1)]).theorems[0]);
Console.WriteLine("PASS retargeted numeral instance fails the structural statement check");

// A same-named predicate of another module is no contract, so stating it is no refutation.
Compile("Shapes", """
    def Shapes.value : Nat := 3
    theorem Shapes.wild : (3 : Nat) = 3 := rfl
    namespace CIL.Safety.MethodContract def Refuted (n : Nat) : Prop := n = 1 end CIL.Safety.MethodContract
    theorem Shapes.refuted : CIL.Safety.MethodContract.Refuted 1 := rfl
    """);
var shapes = Audit("Shapes", [ProofTheorem("Shapes.value"), ProofTheorem("Shapes.missing"),
    new("Shapes.wild", App(Const("Eq", 1), "_", "_", "_"), ApprovedAxioms),
    new("Shapes.wild", App(Const("Eq", 1), Const("Nat"), Nat(3), Nat(4)), ApprovedAxioms),
    ProofTheorem("Shapes.refuted"), ProofTheorem("Shapes.wild")],
    [new("Shapes.value", Nat(3)), new("Shapes.value", Nat(4)), new("Shapes.wild", "_")]);
Rejected(shapes.theorems[0], "Expected a theorem");
Rejected(shapes.theorems[1], "Expected a theorem");
AuditedAxioms(shapes.theorems[2]);
Rejected(shapes.theorems[3], "Theorem statement mismatch");
if (shapes.theorems[4].refutes is not null || shapes.theorems[5].refutes is not null)
    throw new InvalidOperationException("A same-named predicate counted as a refutation: " +
        JsonSerializer.Serialize(shapes.theorems[4]));
if (shapes.constants[0].error is not null || shapes.constants[1].error is null || shapes.constants[2].error is null)
    throw new InvalidOperationException("Constant value checks: " + JsonSerializer.Serialize(shapes.constants));
Console.WriteLine("PASS theorem kind, structural wildcards, constant values and same-named predicates");

// Only the library's counterexample predicate is a refutation. A requested theorem stating the
// negation of a contract is refused, since a run the model does not cover proves it; a lemma
// stating it that is not requested is checked like any other.
const string RefutationSource = """
    import CIL.Safety.MethodContract
    open CIL.Safety
    /-- Promises a return from any memory. -/
    def Refutations.returns : MethodContract Unit :=
      { args := fun _ => [], pre := fun _ _ => True, footprint := fun _ => [], post := fun _ _ _ _ => True }
    theorem Refutations.refuted : Refutations.returns.Refuted [] 0 :=
      .of_fault (input := ()) (initial := Memory.empty) (observed := 1)
        (fault := ⟨0, 0, .invalidState⟩) trivial (by decide) rfl
    theorem Refutations.negated : ¬ Refutations.returns.Holds [] 0 := Refutations.refuted.not_holds
    theorem Refutations.uses : True := (fun _ : ¬ Refutations.returns.Holds [] 0 => trivial) Refutations.negated
    """;
Compile("Refutations", RefutationSource);
var refutedLine = Array.FindIndex(RefutationSource.Split('\n'), line => line.StartsWith("theorem Refutations.refuted",
    StringComparison.Ordinal)) + 1;
var refutations = verification.AuditOleans(fixtureSearch, ["Refutations"], [ProofTheorem("Refutations.refuted"),
    ProofTheorem("Refutations.negated"), ProofTheorem("Refutations.uses")]);
AuditedAxioms(refutations.theorems[0]);
// The audit reports the program only as a constant, so the empty list names none, and the method as its numeral.
if (refutations.theorems[0].refutes is not
        { contract: "CIL.Safety.MethodContract.Holds", program: null, method: 0, column: 8 } refutes ||
    refutes.line != refutedLine)
    throw new InvalidOperationException("Refutation not located: " +
        JsonSerializer.Serialize(refutations.theorems[0]));
Rejected(refutations.theorems[1], "which a run the model does not cover can prove");
AuditedAxioms(refutations.theorems[2]);
if (refutations.theorems[2].refutes is not null)
    throw new InvalidOperationException("A theorem using a negated contract counted as a refutation");
Console.WriteLine("PASS counterexample refutations are located, negated contracts refused, lemmas stating them " +
    "unchanged");

// Builtin notation such as `-1`, `/` and `bif` has formatters only in unloaded imports; printing
// it must fall back to the raw expression instead of failing the audit or evaluating imports.
Compile("Notation", """
    theorem Notation.negative : (-1 : BitVec 32) = 0xFFFFFFFF#32 := by decide
    theorem Notation.quotient : (1 / 2 : Int) = 0 := by decide
    theorem Notation.branch : (bif true then 1 else 2 : Nat) = 1 := rfl
    axiom Notation.bogus : False
    theorem Notation.forged : (-1 : Int) = 1 := Notation.bogus.elim
    """);
var notation = Audit("Notation", [ProofTheorem("Notation.negative"), ProofTheorem("Notation.quotient"),
    ProofTheorem("Notation.branch"), ProofTheorem("Notation.forged")]);
const string rawQuotient = "Notation.quotient : Eq.{1} Int (HDiv.hDiv.{0, 0, 0} Int Int Int " +
    "(instHDiv.{0} Int Int.instDiv) (OfNat.ofNat.{0} Int 1 (instOfNat 1)) (OfNat.ofNat.{0} Int 2 (instOfNat 2))) " +
    "(OfNat.ofNat.{0} Int 0 (instOfNat 0))";
if (notation.theorems[1].statement != rawQuotient ||
    notation.theorems.Zip(["Notation.negative : Eq.{1} ", "", "Notation.branch : Eq.{1} Nat (cond.{1} ",
        "Notation.forged : Eq.{1} Int (Neg.neg.{0} "]).Any(pair => pair.First.statement?.StartsWith(pair.Second) != true))
    throw new InvalidOperationException("Raw statements: " + JsonSerializer.Serialize(notation.theorems));
foreach (var audited in notation.theorems.Take(3)) AuditedAxioms(audited);
// The printed text must not stand in for the axiom check it precedes.
Rejected(notation.theorems[3], "Unapproved proof axioms: Notation.bogus");
Console.WriteLine("PASS unformattable notation prints raw; unapproved axioms still fail");

// Axioms are collected from declaration bodies across modules and private names, not from olean summaries.
Compile("Hidden", "axiom Hidden.ax : False\nprivate theorem secret : 1 = 2 := Hidden.ax.elim\ntheorem Hidden.exposed : 1 = 2 := secret\n");
Compile("Uses", "import Hidden\ntheorem Uses.claim : 1 = 2 := Hidden.exposed\n");
Rejected(Audit("Uses", [ProofTheorem("Uses.claim")]).theorems[0], "Unapproved proof axioms: Hidden.ax");
Console.WriteLine("PASS axioms behind imported private declarations are collected");

// The audit does not type-check: it is sound only on bytes that kernel replay accepted.
Compile("Unchecked", """
    import Lean
    set_option debug.skipKernelTC true
    run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
      name := `Unchecked.forged, levelParams := [], type := Lean.mkConst ``False, value := Lean.mkConst ``True.intro })
    """);
AuditedAxioms(Audit("Unchecked", [ProofTheorem("Unchecked.forged")]).theorems[0]);
var leanchecker = Path.Combine(verification.Toolchain, "bin", OperatingSystem.IsWindows() ? "leanchecker.exe" : "leanchecker");
if (Execute([leanchecker, "Unchecked"], fixtures, fixtures, environment: environment).Code == 0)
    throw new InvalidOperationException("Kernel replay accepted an unchecked declaration");
Console.WriteLine("PASS unchecked declarations pass the audit alone, so it runs only after kernel replay");

// Namespace audits count every theorem a listed module declares under a prefix, private ones by their user name.
AuditedNamespaces Allowing(string[] axioms, string module, params string[] prefixes) =>
    verification.AuditOleans(fixtures, [module], [], namespaces: new(prefixes, axioms)).namespaces!;
AuditedNamespaces Namespaces(string module, params string[] prefixes) => Allowing(ApprovedAxioms, module, prefixes);
Compile("SpacesBase", "theorem Pfx.imported : True := trivial\n");
Compile("Spaces", """
    import SpacesBase
    theorem Pfx.visible : 1 = 1 := rfl
    private theorem Pfx.secret : 2 = 2 := rfl
    def Pfx.value : Nat := 3
    theorem Other.claim : True := trivial
    theorem Pfxs.near : True := trivial
    theorem Pfx.classical (p : Prop) : p ∨ ¬p := Classical.em p
    """);
var spaces = Namespaces("Spaces", "Pfx.");
// The approved axioms reach the audit: the classical theorem passes and reports them.
if (spaces is not { error: null, count: 3, rejected: [] } || spaces.prefixes["Pfx"] != 3 || spaces.modules["Spaces"] != 3 ||
    !spaces.axioms.Order(StringComparer.Ordinal).SequenceEqual(["Classical.choice", "Quot.sound", "propext"]))
    throw new InvalidOperationException("Namespace audit scope: " + JsonSerializer.Serialize(spaces));
var nested = Namespaces("Spaces", "Pfx.", "Pfx.visible");
if (nested is not { error: null, count: 3 } || nested.prefixes["Pfx"] != 3 || nested.prefixes["Pfx.visible"] != 1)
    throw new InvalidOperationException("Nested namespace prefixes: " + JsonSerializer.Serialize(nested));
var duplicate = Namespaces("Spaces", "Pfx.", "Pfx");
if (duplicate is not { error: null, count: 3 } || duplicate.prefixes.Count != 1 || duplicate.prefixes["Pfx"] != 3)
    throw new InvalidOperationException("Duplicate namespace prefixes: " + JsonSerializer.Serialize(duplicate));
// A prefix that matches nothing is an error even beside one that matches, so a typo cannot pass silently.
if (Namespaces("Spaces", "Pfx", "Missing").error is not { } typo || !typo.Contains("Missing", StringComparison.Ordinal) ||
    Namespaces("Spaces", "Pf").error is null)
    throw new InvalidOperationException("Unmatched namespace prefixes were accepted");
Compile("Planted", "axiom Pfx.bogus : False\ntheorem Pfx.fine : True := trivial\ntheorem Pfx.forged : 1 = 2 := Pfx.bogus.elim\n");
var planted = Namespaces("Planted", "Pfx");
if (planted.error is null || planted.count != 2 || planted.rejected is not [{ name: "Pfx.forged", axioms: ["Pfx.bogus"] }] ||
    !planted.axioms.Contains("Pfx.bogus"))
    throw new InvalidOperationException("Planted axiom passed the namespace audit: " + JsonSerializer.Serialize(planted));
// The request's allowed list replaces the default: allowing the planted axiom passes, omitting Classical.choice fails.
if (Allowing(["Pfx.bogus"], "Planted", "Pfx") is not { error: null, count: 2, rejected: [] } allowed || !allowed.axioms.SequenceEqual(["Pfx.bogus"]) ||
    Allowing(["propext", "Quot.sound"], "Spaces", "Pfx").rejected is not [{ name: "Pfx.classical" }])
    throw new InvalidOperationException("Namespace audit ignored its allowed axioms");
Console.WriteLine("PASS namespace audits count module theorems, reject unmatched prefixes and planted axioms");

// The CLI path builds a package, replays its modules and audits those bytes; replay rejects what the audit alone would pass.
var package = Path.Combine(root, "library");
Directory.CreateDirectory(Path.Combine(package, "Lib"));
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
File.WriteAllText(Path.Combine(package, "lakefile.toml"), "name = \"lib\"\n\n[[lean_lib]]\nname = \"Lib\"\n");
File.WriteAllText(Path.Combine(package, "Lib.lean"), "import Lib.Core\ntheorem Lib.top : Lib.base = 1 := Core.fact\n");
void Core(string source) => File.WriteAllText(Path.Combine(package, "Lib", "Core.lean"), source);
// The planted axiom and the theorem using it lie outside the prefix in an imported module, so only the closure walk finds it.
Core("def Lib.base : Nat := 1\naxiom bogus : False\ntheorem Core.fact : Lib.base = 1 := bogus.elim\n");
var library = verification.AuditLibrary(package, ["Lib"], ["Lib."], ApprovedAxioms);
if (library.Result is not { error: not null, count: 1, rejected: [{ name: "Lib.top", axioms: ["bogus"] }] } ||
    !library.Modules.SequenceEqual(["Lib", "Lib.Core"]) || !library.Replayed.SequenceEqual(library.Modules))
    throw new InvalidOperationException("Library audit accepted a planted axiom: " + JsonSerializer.Serialize(library));
// The CLI reports an unmatched prefix as invalid with exit code 1 and still writes its results.
var cliResults = Path.Combine(root, "library-results.json");
var cli = Execute(["dotnet", ExtractorPath, "audit-library", "--project", package, "--module", "Lib", "--prefix", "Missing",
    "--results", cliResults]);
if (cli.Code != 1 || !WithoutStageProgress(cli.Stderr).StartsWith("Invalid: Library audit failed: No theorems under namespace prefixes: Missing", StringComparison.Ordinal) ||
    !File.Exists(cliResults) || JsonDocument.Parse(File.ReadAllText(cliResults)).RootElement.GetProperty("count").GetInt32() != 0)
    throw new InvalidOperationException($"audit-library CLI exit {cli.Code}: {cli.Output}");
Core("""
    import Lean
    def Lib.base : Nat := 1
    set_option debug.skipKernelTC true
    run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
      name := `Lib.Core.fact, levelParams := [], type := Lean.mkConst ``False, value := Lean.mkConst ``True.intro })
    """);
try
{
    verification.AuditLibrary(package, ["Lib.Core"], ["Lib"], ApprovedAxioms);
    throw new InvalidDataException("Library audit accepted an unchecked declaration");
}
catch (InvalidOperationException error) when (error.Message.Contains("Kernel replay rejected Lib.Core", StringComparison.Ordinal)) { }
// A certified CIL proof skips replay only while every module it imports still matches the certified library.
var certifiedParts = new SortedDictionary<string, string>
{
    ["CIL/Memory.olean"] = "m", ["CIL/Memory.olean.hash"] = "mh", ["CIL/MemoryLemmas.olean"] = "l", ["CIL/MemoryLemmas.olean.hash"] = "lh"
};
var importGraph = new Dictionary<string, string[]> { ["CIL.MemoryLemmas"] = ["Init", "CIL.Memory"], ["CIL.Memory"] = ["Init"], ["Lib"] = ["CIL.MemoryLemmas"] };
SortedDictionary<string, SortedDictionary<string, string>> Packaged(string memory) => new(StringComparer.Ordinal)
{
    ["CIL.Memory"] = new() { [".olean"] = memory }, ["CIL.MemoryLemmas"] = new() { [".olean"] = "l" }, ["Lib"] = new() { [".olean"] = "x" }
};
if (!ReusableCertified(importGraph, Packaged("m"), certifiedParts).SetEquals(["CIL.Memory", "CIL.MemoryLemmas"]) ||
    ReusableCertified(importGraph, Packaged("changed"), certifiedParts).Count != 0)
    throw new InvalidOperationException("A certified module skipped replay against changed imports");
// The certified library's own oleans, in the shape ModuleArtifacts records them, are all reusable.
verification.Library(Inputs(At("CIL.lean")));
var sessionOleans = Path.Combine(verification.library!, ".lake/build/lib/lean");
var sessionParts = new SortedDictionary<string, SortedDictionary<string, string>>(
    Directory.EnumerateFiles(sessionOleans, "*.olean", SearchOption.AllDirectories).ToDictionary(
        path => ModuleName(Path.GetRelativePath(sessionOleans, path).Replace('\\', '/')), ConsumerModuleParts), StringComparer.Ordinal);
var cilModules = sessionParts.Keys.Where(module => module == "CIL" || module.StartsWith("CIL.", StringComparison.Ordinal)).ToArray();
if (cilModules.Length == 0 || !ReusableCertified(new(), sessionParts, verification.certifiedModules!).IsSupersetOf(cilModules))
    throw new InvalidOperationException("The certified library's own CIL modules were not reusable");
Console.WriteLine("PASS library audits replay the package and stale certified imports before auditing, and reject planted axioms");

// A statement crosses audits as a term. The kernel accepts a theorem at it by unfolding definitions,
// refuses a weaker one, and refuses a same-named constant that another module declares.
Compile("StatementBase", "def StatementBase.zero : Nat := 0\n");
Compile("StatementProduction", """
    import StatementBase
    def Production.one : Nat := 1
    theorem Production.claim (n : Nat) : n + StatementBase.zero = n := rfl
    theorem Production.base : StatementBase.zero = 0 := rfl
    theorem Production.inlined : Production.one = 1 := rfl
    theorem Production.big : (1180591620717411303425 : Nat) = 1180591620717411303425 := rfl
    """);
Compile("StatementVariant", """
    import StatementBase
    def Variant.zero : Nat := 0
    theorem Variant.claim (m : Nat) : m + Variant.zero = m := rfl
    theorem Variant.weaker (n : Nat) (_ : n = 0) : n + StatementBase.zero = n := rfl
    theorem Variant.one : (1 : Nat) = 1 := rfl
    theorem Variant.big : (1180591620717411303425 : Nat) = 1180591620717411303425 := rfl
    theorem Variant.near : (1180591620717411303424 : Nat) = 1180591620717411303424 := rfl
    """);
Compile("StatementForged", """
    namespace StatementBase
    def zero : Nat := 1
    end StatementBase
    theorem Forged.refuted : ¬ StatementBase.zero = 0 := by decide
    """);
Compile("StatementLone", "theorem Lone.claim (n : Nat) : n + 0 = n := rfl\n");
var production = Audit("StatementProduction", [.. new[]
        { "Production.claim", "Production.base", "Production.inlined", "Production.big" }
    .Select(name => new StatementRequest(true).Apply(ProofTheorem(name)))]).theorems;
if (production.Any(theorem => theorem.term is null || theorem.termError is not null))
    throw new InvalidOperationException("Statement terms: " + JsonSerializer.Serialize(production));
AuditedTheorem Compared(string module, string theorem, AuditedTheorem expected, bool refuted = false) =>
    Audit(module, [new StatementRequest(false, expected.term!.Value.GetRawText(), refuted)
        .Apply(ProofTheorem(theorem))])
        .theorems[0];
var unfolded = Compared("StatementVariant", "Variant.claim", production[0]);
var weaker = Compared("StatementVariant", "Variant.weaker", production[0]);
var inlined = Compared("StatementVariant", "Variant.one", production[2]);
var forged = Compared("StatementForged", "Forged.refuted", production[1], refuted: true);
// A numeral above 2^64 crosses Lean and C# JSON exactly, so only the equal literal matches.
var big = Compared("StatementVariant", "Variant.big", production[3]);
var near = Compared("StatementVariant", "Variant.near", production[3]);
var lone = Compared("StatementLone", "Lone.claim", production[0]);
if (unfolded.matches != true || weaker.matches != false || inlined.matches != true || forged.matches != false ||
    forged.mismatch?.Contains("declares it in StatementForged", StringComparison.Ordinal) != true ||
    big.matches != true || near.matches != false || lone.matches != false ||
    lone.mismatch?.Contains("does not declare StatementBase.zero", StringComparison.Ordinal) != true)
    throw new InvalidOperationException("Statement comparisons: " +
        JsonSerializer.Serialize(new[] { unfolded, weaker, inlined, forged, big, near, lone }));
// A comparison states whether it is with the counterexample predicate: a missing or non-boolean flag would compare
// a refutation request with Holds, so the audit refuses it.
foreach (object expected in new object[]
    {
        new { term = production[0].term!.Value }, new { term = production[0].term!.Value, refuted = "true" }
    })
    Rejected(Audit("StatementVariant", [ProofTheorem("Variant.claim") with { expected = expected }]).theorems[0],
        "expected.refuted");
Rejected(Audit("StatementVariant", [ProofTheorem("Variant.claim") with { expected = new { refuted = false } }])
    .theorems[0], "expected.term");
var extraField = new { term = production[0].term!.Value, refuted = false, negated = true };
Rejected(Audit("StatementVariant", [ProofTheorem("Variant.claim") with { expected = extraField }]).theorems[0],
    "negated");

void RejectDuplicate(string key, string json)
{
    var request = Path.Combine(root, $"duplicate-{key}.json");
    var result = Path.ChangeExtension(request, ".result.json");
    File.WriteAllText(request, json);
    var audit = Execute([verification.CheckedAuditExecutable(), request, result], fixtures, fixtures,
        environment: environment);
    if (audit.Code == 0 || !audit.Stderr.Contains($"Duplicate JSON key: {key}", StringComparison.Ordinal))
        throw new InvalidOperationException($"Duplicate {key}: audit exited {audit.Code}. {audit.Output}");
}
RejectDuplicate("refuted", $$"""
    { "modules": ["StatementVariant"], "theorems": [{
      "name": "Variant.claim",
      "expected": { "term": {{production[0].term!.Value.GetRawText()}}, "refuted": true, "refuted": false }
    }] }
    """);
RejectDuplicate("modules", """{ "modules": ["StatementVariant"], "modul\u0065s": ["StatementVariant"] }""");
Console.WriteLine(Run([verification.LeanExecutable, At("Tests/AuditKeyScaling.lean")],
    fixtures, fixtureSearch, environment: environment));
Console.WriteLine("PASS the kernel compares statements by unfolding, refuses weaker ones and forged constants");

// A user module cannot replace a toolchain module on the audit's search path.
Compile("Init", "prelude\n");
var resolved = verification.AuditOleans(fixtures, ["Init"], []).modules["Init"];
if (!Path.GetFullPath(resolved).StartsWith(Path.GetFullPath(verification.Toolchain), StringComparison.OrdinalIgnoreCase))
    throw new InvalidOperationException("User module shadowed the toolchain: " + resolved);
Console.WriteLine("PASS toolchain modules precede user modules on the audit search path");
