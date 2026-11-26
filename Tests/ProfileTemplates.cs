#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

using System.Text.Json;

var directory = At("artifacts/ProfileTemplates");
var source = Path.Combine(directory, "Assembly");
var shared = Path.Combine(directory, "Shared");
Directory.CreateDirectory(source);
File.WriteAllText(Path.Combine(source, "Dispatch.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup>
<TargetFramework>net11.0</TargetFramework><Optimize>true</Optimize><AllowUnsafeBlocks>true</AllowUnsafeBlocks>
</PropertyGroup></Project>
""");
File.WriteAllText(Path.Combine(source, "Dispatch.cs"), """
using System.Runtime.Intrinsics.X86;
public static class Dispatch
{
    static uint Identity(uint value) => value;
    static T Echo<T>(T value) where T : unmanaged => value;
    public static ulong Generic(uint left, ulong right) => Echo(left) + Echo(right);
    static void Touch(ref uint value) { }
    public static uint Choose(uint left, uint right)
    {
        if (Avx2.IsSupported) return Identity(left);
        if (Sse42.IsSupported) return right;
        return left;
    }
    public static uint Wrapper(uint left, uint right) => Choose(left, right);
    public static uint Home(uint value)
    {
        if (Avx2.IsSupported) Touch(ref value);
        return value;
    }
}
public sealed class Blank { }
public static class StaticDispatch
{
    public static readonly uint Bias = 7;
    public static uint Read() => Bias;
}
public abstract class Slot { public abstract uint Value(); }
public sealed class Single : Slot { public override uint Value() => 1; }
public sealed class Double : Slot { public override uint Value() => 2; }
// Each method names other methods only on the branch of one feature, so a profile without it leaves them out.
public static unsafe class Kinds
{
    static uint Bump(uint value) => value + 1;
    static uint Twice(uint value) => value * 2;
    public static void Register(delegate* managed<uint, uint>[] table) { table[0] = &Bump; table[1] = &Twice; }
    public static uint Virtual(Slot slot) { if (Avx2.IsSupported) return slot.Value(); return 0; }
    public static uint Address(uint value)
    {
        if (Avx2.IsSupported) return ((delegate* managed<uint, uint>)&Bump)(value);
        return value;
    }
    public static uint Indirect(delegate* managed<uint, uint>[] table, int index, uint value)
    {
        if (Avx2.IsSupported) return table[index](value);
        return value;
    }
    public static uint Initial()
    {
        var scaled = Scaling.Scaled;
        if (Avx2.IsSupported) return Bump(scaled);
        return scaled;
    }
}
public static class Scaling
{
    static uint Scale(uint value) => value;
    public static readonly uint Scaled = Scale(3);
}
""");
Run(["dotnet", "build", Path.Combine(source, "Dispatch.csproj"), "-c", "Release"]);
var assembly = Path.Combine(source, "bin/Dispatch.dll");
var profiles = new[] { "scalar", "x64-sse42", "x64-v3" };
var extractions = profiles.Select(profile => Path.Combine(directory, profile)).ToArray();
for (var index = 0; index < profiles.Length; index++)
    Run(Extract("extract", assembly, "Dispatch", "Dispatch::Choose(uint,uint)", extractions[index], profiles[index]));
var wrapper = Path.Combine(directory, "Wrapper");
Run(Extract("extract", assembly, "Dispatch", "Dispatch::Wrapper(uint,uint)", wrapper, "x64-v3"));
Run(["dotnet", ExtractorPath, "templates", shared, .. extractions, wrapper]);
var templates = File.ReadAllText(Path.Combine(shared, "Templates.lean"));
if (templates.Split("code := cil_template_code%").Length != 4 ||
    !templates.Contains("(sse42 : Bool) (avx2 : Bool) (callee0 : Nat)", StringComparison.Ordinal) ||
    !templates.Contains("cil_instruction_equations method0", StringComparison.Ordinal))
    throw new InvalidOperationException("Expected one generated body per method with flags, callees and equations.");
if (!templates.Contains("cil_decoded_method method0 := Method.ofClosed?", StringComparison.Ordinal) ||
    !templates.Contains("code := cil_template_code%", StringComparison.Ordinal) ||
    !templates.Contains("=> callee0 | index => index)).links", StringComparison.Ordinal) ||
    !templates.Contains("theorem method0_input0_links", StringComparison.Ordinal))
    throw new InvalidOperationException("The Choose template needs decoded code and a parameterized call link.");
var renamed = File.ReadAllText(Path.Combine(shared, "TemplateBindings3.lean"));
if (!renamed.Contains("Templates.method0 Extracted.profile Extracted.environment true true 2",
        StringComparison.Ordinal))
    throw new InvalidOperationException("Wrapper extraction did not exercise changed managed callee indices.");
var library = args switch
{
    [] => FixtureLeanPath(),
    ["--framework", var framework] => Path.Combine(Path.GetFullPath(framework), ".lake/build/lib/lean"),
    _ => throw new ArgumentException("Usage: ProfileTemplates.cs [--framework <compiled checkout>]")
};
var sharedPath = shared + Path.PathSeparator + library;

void Compile(string root, string name, string path)
{
    var output = Run(["lean", "--root=" + root, "-o", Path.Combine(root, name + ".olean"),
        Path.Combine(root, name + ".lean")], leanPath: path, progress: "Checking " + name);
    if (output.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException("Admitted declaration in " + name);
    File.WriteAllText(Path.Combine(root, name + ".log"), output);
}

Compile(shared, "Templates", sharedPath);
File.Copy(At("Tests/ProfileTemplatesProof.lean"), Path.Combine(shared, "TemplateProof.lean"), overwrite: true);
Compile(shared, "TemplateProof", sharedPath);
Console.WriteLine("PASS one proof over generated template for all selected flag combinations");

for (var index = 0; index <= profiles.Length; index++)
{
    var extracted = index == profiles.Length ? wrapper : extractions[index];
    var path = extracted + Path.PathSeparator + sharedPath;
    Compile(extracted, "Extracted", path);
    var binding = "TemplateBindings" + index;
    File.Copy(Path.Combine(shared, binding + ".lean"), Path.Combine(extracted, binding + ".lean"), overwrite: true);
    Compile(extracted, binding, path);
    var avx = index >= 2;
    var sse = index != 0;
    var entry = index == 3 ? 1 : 0;
    var callee = index == 3 ? 2 : avx ? 1 : 0;
    var helper = avx ? $"(fun _ => TemplateBindings.method{callee}_template)" :
        "(by intro impossible; cases impossible)";
    File.WriteAllText(Path.Combine(extracted, "Consumer.lean"), $$"""
import {{binding}}
import TemplateProof

/-! The same template proof binds to this independently extracted profile. -/
namespace Consumer
open CIL
/-- The extracted helper returns the value selected by its actual feature profile. -/
theorem selected_result (memory : Safety.Memory) (left right : W32) :
    Safety.invoke Extracted.program 30 {{entry}} [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 {{(index == 1 ? "right" : "left")}})]) :=
  TemplateProof.choose_returns Extracted.program {{entry}} {{callee}} Extracted.profile Extracted.environment
    {{(sse ? "true" : "false")}} {{(avx ? "true" : "false")}} rfl rfl (by decide)
    TemplateBindings.method{{entry}}_template {{helper}} memory left right
#print axioms selected_result
end Consumer
""");
    Compile(extracted, "Consumer", path);
    File.WriteAllText(Path.Combine(extracted, "Replay.lean"), """
import Consumer
open Lean in
run_cmd do
  let start ← IO.getNumHeartbeats
  let mut count : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    unless ["Extracted.", "Templates.", "TemplateProof.", "TemplateBindings.", "Consumer."].any
        (fun namespacePrefix => name.toString.startsWith namespacePrefix) do continue
    let .thmInfo declaration := info | continue
    let proof := Expr.letE `checked declaration.type declaration.value (.bvar 0) false
    match Kernel.check (← getEnv) {} proof with
    | .error _ => throwError "Kernel rejected {name}"
    | .ok _ => count := count + 1
  logInfo m!"Replayed {count} declarations; {(← IO.getNumHeartbeats) - start} raw heartbeats"
""");
    Compile(extracted, "Replay", path);
    Console.WriteLine("PASS exact binding, consumer theorem and independent kernel replay: " + extracted);
}

// Calls through a virtual slot, a method address, a callable pointer catalog and a static initializer name their
// methods by the template's callee parameters, which must elaborate and bind to each profile's own indices.
var kinds = new (string Name, string Selector, string Spelling)[]
{
    ("Virtual", "Kinds::Virtual(Slot)", ".virtual [("),
    ("Address", "Kinds::Address(uint)", ": Link := .address "),
    ("Indirect", "Kinds::Indirect(method System.UInt32 *(System.UInt32)[],System.Int32,System.UInt32)",
        ".indirect [{ identity := "),
    ("Initial", "Kinds::Initial()", "initializer := some { method := callee1")
};
foreach (var (name, selector, spelling) in kinds)
{
    var kindProfiles = new[] { "scalar", "x64-v3" };
    var kindExtractions = kindProfiles.Select(profile => Path.Combine(directory, name + "-" + profile)).ToArray();
    for (var index = 0; index < kindProfiles.Length; index++)
        Run([.. Extract("extract", assembly, "Dispatch", selector, kindExtractions[index], kindProfiles[index]),
            "--assume-initialized", "Scaling"]);
    var kindShared = Path.Combine(directory, name + "Shared");
    Run(["dotnet", ExtractorPath, "templates", kindShared, .. kindExtractions]);
    var kindTemplates = File.ReadAllText(Path.Combine(kindShared, "Templates.lean"));
    if (!kindTemplates.Contains(spelling, StringComparison.Ordinal) ||
        !kindTemplates.Contains("(callee0 : Nat)", StringComparison.Ordinal))
        throw new InvalidOperationException($"The {name} template does not name its method by a callee parameter:\n" +
            kindTemplates);
    var kindPath = kindShared + Path.PathSeparator + library;
    Compile(kindShared, "Templates", kindPath);
    for (var index = 0; index < kindProfiles.Length; index++)
    {
        var extracted = kindExtractions[index];
        var path = extracted + Path.PathSeparator + kindPath;
        if (name == "Initial") RequireDecodedEntry(extracted);
        Compile(extracted, "Extracted", path);
        var binding = "TemplateBindings" + index;
        File.Copy(Path.Combine(kindShared, binding + ".lean"), Path.Combine(extracted, binding + ".lean"),
            overwrite: true);
        Compile(extracted, binding, path);
    }
    if (name == "Address")
    {
        File.WriteAllText(Path.Combine(kindShared, "AddressTarget.lean"), """
            import Templates
            open CIL

            /-- Taking Bump's address names the target index supplied by the template caller. -/
            theorem address_target (profile : FeatureProfile) (environment : LayoutEnvironment)
                (bump twice : Nat) :
                (Templates.method0 profile environment true bump twice).linkAt 2 =
                  some (.address bump) := rfl
            #print axioms address_target
            """);
        Compile(kindShared, "AddressTarget", kindPath);
        using Program verifier = new();
        verifier.ReplayCheckedModules(["Templates", "AddressTarget"], kindPath,
            "Kernel replay of the decoded method-address template");
    }
    Console.WriteLine($"PASS a {name} template elaborates and binds to each profile's own method indices");
}

void RejectLean(string name, string text, string path, string diagnostic = "Not a definitional equality")
{
    var file = Path.Combine(directory, name + ".lean");
    File.WriteAllText(file, text);
    var result = Execute(["lean", file], leanPath: path);
    if (result.Code == 0 || !result.Output.Contains(diagnostic, StringComparison.OrdinalIgnoreCase))
        throw new InvalidOperationException($"""
            Expected {diagnostic} checking {name}.
            {result.Output}
            """);
    Console.WriteLine("PASS rejection: " + name);
}

const string BindingMismatch = "cil_kernel_rfl: the kernel does not accept the two sides as equal";
var widePath = extractions[2] + Path.PathSeparator + sharedPath;
var wideBinding = File.ReadAllText(Path.Combine(shared, "TemplateBindings2.lean"));
RejectLean("WrongFlag", wideBinding.Replace("true true 1", "false false 1", StringComparison.Ordinal),
    widePath, BindingMismatch);
RejectLean("WrongCallee", wideBinding.Replace("true true 1", "true true 0", StringComparison.Ordinal),
    widePath, BindingMismatch);
RejectLean("WrongProfile", wideBinding.Replace("Extracted.profile", "FeatureProfile.scalar",
    StringComparison.Ordinal), widePath, BindingMismatch);
RejectLean("WrongEquation", """
import Templates
example (profile : CIL.FeatureProfile) (environment : CIL.LayoutEnvironment) (callee : Nat) :
    (Templates.method0 profile environment true true callee).code[1]? = some (.brfalse 6) := by rfl
""", sharedPath, "is not definitionally equal to the right-hand side");
var wrongBranch = templates.Replace("Input2.method0.code)", "(Input2.method0.code.set 1 (.brfalse 6)))",
    StringComparison.Ordinal);
RejectLean("WrongBranch", wrongBranch, sharedPath);
var wrongLinks = templates.Split('\n').Select(line => line.StartsWith("  links := ", StringComparison.Ordinal)
    ? line.Replace("=> callee0 ", "=> callee0 + 1 ", StringComparison.Ordinal) : line);
RejectLean("WrongRelocatedLinks", string.Join('\n', wrongLinks), sharedPath);
RejectLean("UnequalTemplateLengths", """
    import CIL.Extraction.TemplateCode
    example (flag : Bool) : List CIL.Instruction := cil_template_code% (if flag then [.ret] else [])
    """, sharedPath, "template alternatives have different lengths");
RejectLean("OpenTemplateCode", """
    import CIL.Extraction.TemplateCode
    example (body : CIL.Method) : List CIL.Instruction := cil_template_code% body.code
    """, sharedPath, "a template alternative must have a closed instruction list");

var original = File.ReadAllText(Path.Combine(extractions[0], "Extracted.lean"));
try
{
    File.AppendAllText(Path.Combine(extractions[0], "Extracted.lean"), "\n-- changed source\n");
    var rejected = Execute(["dotnet", ExtractorPath, "templates", Path.Combine(directory, "Stale"), extractions[0]]);
    if (rejected.Code == 0 || !rejected.Output.Contains("failed exact extraction checking", StringComparison.Ordinal))
        throw new InvalidOperationException("Stale extraction was accepted as template input.");
    if (File.Exists(Path.Combine(directory, "Stale/Templates.lean")))
        throw new InvalidOperationException("Failed extraction check emitted a template.");
}
finally
{
    File.WriteAllText(Path.Combine(extractions[0], "Extracted.lean"), original);
}
Console.WriteLine("PASS changed extraction source invalidates template generation");

var homes = new[] { "scalar", "x64-v3" }.Select(profile => Path.Combine(directory, "Homes-" + profile)).ToArray();
for (var index = 0; index < homes.Length; index++)
    Run(Extract("extract", assembly, "Dispatch", "Dispatch::Home(uint)", homes[index],
        index == 0 ? "scalar" : "x64-v3"));
var incompatible = Execute(["dotnet", ExtractorPath, "templates", Path.Combine(directory, "Incompatible"), .. homes]);
if (incompatible.Code == 0 ||
    !incompatible.Output.Contains("metadata or instruction count differs", StringComparison.Ordinal))
    throw new InvalidOperationException("Profile-dependent parameter homes were accepted without an exact template.");
Console.WriteLine("PASS incompatible profile-dependent metadata rejected");

var generic = Path.Combine(directory, "Generic");
var genericShared = Path.Combine(directory, "GenericShared");
Run(Extract("extract", assembly, "Dispatch", "Dispatch::Generic(uint,ulong)", generic));
Run(["dotnet", ExtractorPath, "templates", genericShared, generic]);
using var identities = JsonDocument.Parse(File.ReadAllText(Path.Combine(genericShared, "templates.json")));
var signatures = identities.RootElement.GetProperty("methods").EnumerateArray()
    .Select(method => method.GetProperty("signature").GetString()!).ToArray();
if (!signatures.Any(signature => signature.Contains("::Echo<System.UInt32>", StringComparison.Ordinal)) ||
    !signatures.Any(signature => signature.Contains("::Echo<System.UInt64>", StringComparison.Ordinal)))
    throw new InvalidOperationException("Closed generic specializations lost their distinct managed identities.");
var genericPath = generic + Path.PathSeparator + genericShared + Path.PathSeparator + library;
Compile(genericShared, "Templates", genericPath);
Compile(generic, "Extracted", genericPath);
File.Copy(Path.Combine(genericShared, "TemplateBindings0.lean"), Path.Combine(generic, "TemplateBindings0.lean"),
    overwrite: true);
Compile(generic, "TemplateBindings0", genericPath);
Console.WriteLine("PASS distinct closed generic callee identities and exact bindings");

// A class constructor calls the System.Object constructor with no link. The template steps that call through its
// runtime model, so a proof over the template needs no fact an extraction states.
var constructed = Path.Combine(directory, "Constructor");
Run(Extract("extract", assembly, "Dispatch", "Blank::.ctor()", constructed));
var constructorShared = Path.Combine(directory, "ConstructorShared");
Run(["dotnet", ExtractorPath, "templates", constructorShared, constructed]);
var constructorPath = constructed + Path.PathSeparator + constructorShared + Path.PathSeparator + library;
Compile(constructorShared, "Templates", constructorPath);
File.WriteAllText(Path.Combine(constructorShared, "ConstructorProof.lean"), """
    import Templates
    import CIL.Safety.SymbolicExecution
    import CIL.Safety.ObjectSteps

    /-! A proof over a generated constructor template. -/
    namespace ConstructorProof
    open CIL CIL.Safety

    example (profile : FeatureProfile) (environment : LayoutEnvironment) :
        (Templates.method0 profile environment).links = [] := rfl

    example (profile : FeatureProfile) (environment : LayoutEnvironment) :
        (Templates.method0 profile environment).code[1]? = some (.call {
          owner := .atom Extraction.runtimeScope "System.Object" .classType, name := name!".ctor",
          hasThis := true, genericArity := 0, returnType := .void, parameters := [],
          methodArguments := [] } {}) := rfl

    /-- The template constructor of a class deriving from `System.Object` returns, for any profile. -/
    theorem constructs (program : Program) (index : Nat) (profile : FeatureProfile)
        (environment : LayoutEnvironment)
        (found : program[index]? = some (Templates.method0 profile environment))
        (memory : Safety.Memory) (object : Reference)
        (formed : formObject memory (.address object) = .ok (.object (.address object))) :
        invoke program 10 index [.object (.address object)] memory = .ok (memory, []) := by
      cil_checked_steps [formed]
    #print axioms constructs
    end ConstructorProof
    """);
Compile(constructorShared, "ConstructorProof", constructorPath);
Compile(constructed, "Extracted", constructorPath);
File.Copy(Path.Combine(constructorShared, "TemplateBindings0.lean"),
    Path.Combine(constructed, "TemplateBindings0.lean"), overwrite: true);
Compile(constructed, "TemplateBindings0", constructorPath);
Console.WriteLine("PASS a constructor template steps its unlinked System.Object constructor call");

var staticOutputs = new[] { "scalar", "x64-v3" }.Select(profile =>
    Path.Combine(directory, "Static-" + profile)).ToArray();
for (var index = 0; index < staticOutputs.Length; index++)
    Run(["dotnet", ExtractorPath, "extract", assembly, "StaticDispatch::Read()", staticOutputs[index],
        index == 0 ? "scalar" : "x64-v3", "--assume-initialized", "StaticDispatch"]);
var staticShared = Path.Combine(directory, "StaticShared");
Run(["dotnet", ExtractorPath, "templates", staticShared, .. staticOutputs]);
var staticTemplate = File.ReadAllText(Path.Combine(staticShared, "Templates.lean"));
if (!staticTemplate.Contains("name := name!\"Bias\" }", StringComparison.Ordinal))
    throw new InvalidOperationException("Static template omitted its field identity.");
var staticFiles = Directory.GetFiles(staticShared).ToDictionary(path => Path.GetFileName(path)!, File.ReadAllText);
Run(["dotnet", ExtractorPath, "templates", staticShared, .. staticOutputs]);
if (Directory.GetFiles(staticShared).Any(path => File.ReadAllText(path) != staticFiles[Path.GetFileName(path)]))
    throw new InvalidOperationException("Static template closure is not deterministic.");
Compile(staticShared, "Templates", staticShared + Path.PathSeparator + library);
for (var index = 0; index < staticOutputs.Length; index++)
{
    var path = staticOutputs[index] + Path.PathSeparator + staticShared + Path.PathSeparator + library;
    RequireDecodedEntry(staticOutputs[index]);
    Compile(staticOutputs[index], "Extracted", path);
    var binding = "TemplateBindings" + index;
    File.Copy(Path.Combine(staticShared, binding + ".lean"), Path.Combine(staticOutputs[index], binding + ".lean"),
        overwrite: true);
    Compile(staticOutputs[index], binding, path);
}
void RequireDecodedEntry(string directory)
{
    if (!File.ReadLines(Path.Combine(directory, "Extracted.lean"))
        .Any(line => line.StartsWith("cil_decoded_method method0 ", StringComparison.Ordinal)))
        throw new InvalidOperationException($"The static entry in {directory} has no decoder equation.");
}

var staticBinding = File.ReadAllText(Path.Combine(staticShared, "TemplateBindings0.lean"));
var staticPath = staticOutputs[0] + Path.PathSeparator + library;
var changedStatic = Path.Combine(directory, "ChangedStatic");
Directory.CreateDirectory(changedStatic);
var siteStart = staticTemplate.IndexOf("staticSites := [", StringComparison.Ordinal);
if (siteStart < 0) throw new InvalidOperationException("Static template has no descriptor list.");
var codeStart = staticTemplate.IndexOf("  code := cil_template_code%", siteStart, StringComparison.Ordinal);
var descriptors = staticTemplate[siteStart..codeStart];
var changedField = descriptors.Replace("name := name!\"Bias\" }, bytes", "name := name!\"Changed\" }, bytes",
    StringComparison.Ordinal);
if (descriptors == changedField) throw new InvalidOperationException("Missing static field identity.");
File.WriteAllText(Path.Combine(changedStatic, "Templates.lean"),
    $"""{staticTemplate[..siteStart]}{changedField}{staticTemplate[codeStart..]}""");
Compile(changedStatic, "Templates", changedStatic + Path.PathSeparator + library);
RejectLean("ChangedStaticIdentity", staticBinding, changedStatic + Path.PathSeparator + staticPath, BindingMismatch);
var missingStatic = Path.Combine(directory, "MissingStatic");
Directory.CreateDirectory(missingStatic);
File.WriteAllText(Path.Combine(missingStatic, "Templates.lean"),
    $"""{staticTemplate[..siteStart]}staticSites := [],{"\n"}{staticTemplate[codeStart..]}""");
Compile(missingStatic, "Templates", missingStatic + Path.PathSeparator + library);
RejectLean("MissingStaticMetadata", staticBinding, missingStatic + Path.PathSeparator + staticPath, BindingMismatch);
Console.WriteLine("PASS deterministic static metadata, exact profile bindings " +
    "and changed/missing descriptor rejection");
