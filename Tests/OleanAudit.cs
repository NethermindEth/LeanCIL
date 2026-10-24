#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/ConsumerVerification.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/LibraryAudit.cs

using System.Text.Json;

using var verification = new Program();
var root = At("artifacts/OleanAudit");
if (Directory.Exists(root)) Directory.Delete(root, true);
Directory.CreateDirectory(root);

// Each proof below certifies the addition contract for the subtraction method, so any acceptance is unsound.
var assembly = At("Examples/Assembly/bin/Examples.dll");
const string wrongAdd = "System.UInt64 Examples.Arithmetic::WrongAdd(System.UInt64,System.UInt64)";
var addProof = File.ReadAllText(At("Examples/Proofs/Add.lean"));
// The addition contract, proved for any program from an unapproved axiom.
const string axiomProof = """
    import Extracted
    import Examples.Support

    open CIL
    namespace ExampleProof
    axiom bogus : False
    theorem correctness (x y : W64) :
        ∃ result : W64,
          (CIL.Safety.invoke Extracted.program 4 0
            [.scalar (.i64 x), .scalar (.i64 y)] Examples.empty).map Prod.snd =
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

// Checker-level cases: modules compiled directly, audited without elaborating any source.
var fixtures = Path.Combine(root, "fixtures");
Directory.CreateDirectory(fixtures);
var environment = new Dictionary<string, string> { ["LEAN_SYSROOT"] = verification.Toolchain };
void Compile(string module, string source)
{
    var path = Path.Combine(fixtures, module + ".lean");
    File.WriteAllText(path, source);
    Run([verification.LeanExecutable, "--root=" + fixtures, "-o", Path.Combine(fixtures, module + ".olean"), path], fixtures, fixtures, environment: environment);
}
string Elaborated(string source)
{
    var path = Path.Combine(fixtures, "Elaborated.lean");
    File.WriteAllText(path, source);
    return Run([verification.LeanExecutable, "--root=" + fixtures, path], fixtures, fixtures, environment: environment);
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

// The elaborated audits are really fooled, so these fixtures exercise the attacks rather than a typo.
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

var refutationLine = 4;
Compile("Shapes", """
    def Shapes.value : Nat := 3
    theorem Shapes.wild : (3 : Nat) = 3 := rfl
    namespace CIL.Safety.MethodContract def Holds (n : Nat) : Prop := n = 0 end CIL.Safety.MethodContract
    theorem Shapes.refuted : ¬ CIL.Safety.MethodContract.Holds 1 := Nat.succ_ne_zero 0
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
if (shapes.theorems[4].refutes is not { contract: "CIL.Safety.MethodContract.Holds", column: 8 } refutes || refutes.line != refutationLine ||
    shapes.theorems[5].refutes is not null || !AuditText(shapes.theorems[4]).Contains($"LeanCIL refutes: CIL.Safety.MethodContract.Holds at {refutationLine}:8\n"))
    throw new InvalidOperationException("Refutation not located: " + JsonSerializer.Serialize(shapes.theorems[4]));
if (shapes.constants[0].error is not null || shapes.constants[1].error is null || shapes.constants[2].error is null)
    throw new InvalidOperationException("Constant value checks: " + JsonSerializer.Serialize(shapes.constants));
Console.WriteLine("PASS theorem kind, structural wildcards, constant values and refutation locations");

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
if (cli.Code != 1 || !cli.Stderr.StartsWith("Invalid: Library audit failed: No theorems under namespace prefixes: Missing", StringComparison.Ordinal) ||
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
var sessionOleans = Path.Combine(verification.Library(Inputs(At("CIL.lean"))), ".lake/build/lib/lean");
var sessionParts = new SortedDictionary<string, SortedDictionary<string, string>>(
    Directory.EnumerateFiles(sessionOleans, "*.olean", SearchOption.AllDirectories).ToDictionary(
        path => ModuleName(Path.GetRelativePath(sessionOleans, path).Replace('\\', '/')), ConsumerModuleParts), StringComparer.Ordinal);
var cilModules = sessionParts.Keys.Where(module => module == "CIL" || module.StartsWith("CIL.", StringComparison.Ordinal)).ToArray();
if (cilModules.Length == 0 || !ReusableCertified(new(), sessionParts, verification.certifiedModules!).IsSupersetOf(cilModules))
    throw new InvalidOperationException("The certified library's own CIL modules were not reusable");
Console.WriteLine("PASS library audits replay the package and stale certified imports before auditing, and reject planted axioms");

// A user module cannot replace a toolchain module on the audit's search path.
Compile("Init", "prelude\n");
var resolved = verification.AuditOleans(fixtures, ["Init"], []).modules["Init"];
if (!Path.GetFullPath(resolved).StartsWith(Path.GetFullPath(verification.Toolchain), StringComparison.OrdinalIgnoreCase))
    throw new InvalidOperationException("User module shadowed the toolchain: " + resolved);
Console.WriteLine("PASS toolchain modules precede user modules on the audit search path");
