#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

// PDB names and locations only locate: extraction is byte-identical without a PDB, a proof
// naming locals by scope survives an inserted local, and diagnostics gain `file:line:column`.
using var verification = new Program();
var root = At("artifacts/DebugNames");
const string Selector = "Calls::Sum(uint,uint)";
const string Sum = "System.UInt32 Names.Calls::Sum(System.UInt32,System.UInt32)";

foreach (var import in new[] { "import ExtractedSymbols", "  import ExtractedSymbols -- names\r\n",
    "import ExtractedSymbols /- names -/", "public meta import all ExtractedSymbols -- names" })
    if (!ImportsSymbols(import)) throw new InvalidOperationException("Missed PDB import: " + import);
foreach (var import in new[] { "-- import ExtractedSymbols", "import ExtractedSymbolsExtra",
    "import ExtractedSymbols.Other", "import ExtractedSymbols'" })
    if (ImportsSymbols(import)) throw new InvalidOperationException("Spurious PDB import: " + import);

string Source(string inserted) => string.Join("\n",
    "namespace Names;",
    "public static class Calls",
    "{",
    "    public static uint Mix(uint x, uint y) => x & y;",
    "    public static ulong Wide(uint x, uint y) => (ulong)x * y;",
    "    public static uint Sum(uint x, uint y)",
    "    {",
    "        uint total = 0;",
    "        " + inserted,
    "        { uint carry = Mix(x, y); total += carry; total += carry >> 1; }",
    "        { ulong carry = Wide(x, y); total ^= (uint)carry; total ^= (uint)(carry >> 32); }",
    "        return total;",
    "    }",
    "    public static uint Fail(uint x)",
    "    {",
    "        if (x == 0) return (uint)new float[x].Length;",
    "        return x;",
    "    }",
    "}");

string Build(string name, string inserted, string debugType)
{
    var source = Path.Combine(root, name);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Names.csproj"), $"""
    <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize><DebugType>{debugType}</DebugType></PropertyGroup></Project>
    """);
    File.WriteAllText(Path.Combine(source, "Names.cs"), Source(inserted));
    Run(["dotnet", "build", Path.Combine(source, "Names.csproj"), "-c", "Release"]);
    return Path.Combine(source, "bin/Names.dll");
}

var original = Build("Original", "", "portable");
var stripped = Build("Stripped", "", "none");
var inserted = Build("Inserted", "uint pad = x * 3; total += pad; total += pad >> 2;", "portable");

string Extraction(string name, string assembly)
{
    var folder = Path.Combine(root, name + "-Extraction");
    Run(Extract("extract", assembly, "Names", Selector, folder));
    return folder;
}
var withSymbols = Extraction("Original", original);
var withoutSymbols = Extraction("Stripped", stripped);
if (File.ReadAllText(Path.Combine(withSymbols, "Extracted.lean")) != File.ReadAllText(Path.Combine(withoutSymbols, "Extracted.lean")))
    throw new InvalidOperationException("Extracted.lean depends on the PDB.");
if (!File.Exists(Path.Combine(withSymbols, "Symbols.lean")) || File.Exists(Path.Combine(withoutSymbols, "Symbols.lean")))
    throw new InvalidOperationException("Symbols.lean must exist exactly when a matching PDB does.");
Console.WriteLine("PASS Extracted.lean is byte-identical with and without the PDB; Symbols.lean only with it");

string Proof(string name, string[] slots, string imports = "  import ExtractedSymbols -- PDB names for this proof\n")
{
    var path = Path.Combine(root, name + ".lean");
    File.WriteAllText(path, $$"""
    import Extracted
    {{imports}}import CIL.StructuralLabels

    open CIL
    namespace ExampleProof

    bind_method sum sumBody := "{{Sum}}"
    bind_callee mix mixBody := "System.UInt32 Names.Calls::Mix(System.UInt32,System.UInt32)" from sumBody
    bind_callee wide wideBody := "System.UInt64 Names.Calls::Wide(System.UInt32,System.UInt32)" from sumBody
    bind_call atMix := mix from sumBody
    bind_call atWide := wide from sumBody

    -- Each block stores its call's result in its own `carry`, and the second block reads its own back.
    theorem correctness :
        sumBody.code[atMix + 1]? = some (.setLocal {{slots[0]}}) ∧
        sumBody.code[atWide + 1]? = some (.setLocal {{slots[1]}}) ∧
        sumBody.code[atWide + 2]? = some (.local {{slots[2]}}) :=
      ⟨rfl, rfl, rfl⟩

    end ExampleProof
    """);
    return path;
}

var named = Proof("Named", ["(local_named sum \"carry\" at (atMix + 1))", "(local_named sum \"carry\" at (atWide + 1))", "(local_named sum \"carry\" at (atWide + 2))"]);
foreach (var (name, assembly) in new[] { ("Original", original), ("Inserted", inserted) })
{
    verification.Verify(assembly, "Names", Selector, named, Path.Combine(root, name + "-Named"));
    Console.WriteLine($"PASS {name}: locals named by scope verify unedited");
}

bool Fails(string assembly, string proof, string output, string marker)
{
    try { verification.Verify(assembly, "Names", Selector, proof, Path.Combine(root, output)); }
    catch (InvalidOperationException error) when (error.Message.Contains(marker, StringComparison.Ordinal)) { return true; }
    return false;
}

// Slot numbers from the original build break once a local is declared before the blocks.
var numbered = Proof("Numbered", ["0", "1", "1"], "");
verification.Verify(original, "Names", Selector, numbered, Path.Combine(root, "Original-Numbered"));
if (!Fails(inserted, numbered, "Inserted-Numbered", "rfl"))
    throw new InvalidOperationException("Numbered slots survived an inserted local; the fixture does not move them.");
Console.WriteLine("PASS numbered slots break on an inserted local; scoped names do not");

// `carry` names two slots, so it needs a scope; and names need the PDB.
if (!Fails(original, Proof("Unscoped", ["(local_named sum \"carry\")", "1", "1"]), "Original-Unscoped", "local \"carry\" names 2 slots"))
    throw new InvalidOperationException("An ambiguous local name resolved without a scope.");
if (!Fails(stripped, named, "Stripped-Named", "extraction found no matching portable PDB"))
    throw new InvalidOperationException("A proof importing ExtractedSymbols ran without a PDB.");
Console.WriteLine("PASS ambiguous names need `at`; ExtractedSymbols needs a PDB");

// A failing binding names the source line of the first differing pc.
var wrong = Path.Combine(root, "WrongBody.lean");
File.WriteAllText(wrong, $$"""
    import Extracted
    import ExtractedSymbols
    import CIL.StructuralLabels
    import CIL.MethodBinding
    namespace ExampleProof
    bind_method sum sumBody := "{{Sum}}"
    theorem correctness : Extracted.program[sum]? = some { sumBody with code := sumBody.code.set (sumBody.code.length - 1) .nop } := by cil_body
    end ExampleProof
    """);
var lines = Source("").Split('\n');
var returnLine = Array.FindIndex(lines, l => l.Contains("return total;")) + 1;
if (!Fails(original, wrong, "Original-Wrong", $"Names.cs:{returnLine}:"))
    throw new InvalidOperationException("cil_body did not report the source line of the differing instruction.");
Console.WriteLine($"PASS cil_body reports Names.cs:{returnLine} for the differing pc");

// Extraction errors gain the source location, and only when a PDB is present.
var unsupportedLine = Array.FindIndex(lines, l => l.Contains("new float[x]")) + 1;
foreach (var (name, assembly, located) in new[] { ("Original", original, true), ("Stripped", stripped, false) })
{
    var result = Execute(Extract("extract", assembly, "Names", "Calls::Fail(uint)", Path.Combine(root, name + "-Fail")));
    var source = $"  Source: Names.cs:{unsupportedLine}:";
    if (result.Code == 0 || !result.Output.Contains("Unsupported instruction") || result.Output.Contains(source) != located ||
        (!located && result.Output.Contains("  Source: ")))
        throw new InvalidOperationException($"Unexpected extraction diagnostic for {name}:\n{result.Output}");
}
Console.WriteLine($"PASS unsupported instructions report Names.cs:{unsupportedLine} with a PDB and no source without one");
