#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;

var directory = At("artifacts/ProfileTemplates");
var source = Path.Combine(directory, "Assembly");
var shared = Path.Combine(directory, "Shared");
Directory.CreateDirectory(source);
File.WriteAllText(Path.Combine(source, "Dispatch.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup>
<TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize><AllowUnsafeBlocks>true</AllowUnsafeBlocks>
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
if (templates.Split("@[cil_code] def method").Length != 4 ||
    !templates.Contains("(sse42 : Bool) (avx2 : Bool) (callee0 : Nat)", StringComparison.Ordinal) ||
    !templates.Contains("cil_instruction_equations method0", StringComparison.Ordinal))
    throw new InvalidOperationException("Expected one generated body per method with flags, callees and equations.");
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
    ("Virtual", "Kinds::Virtual(Slot)", ".callVirtual [("),
    ("Address", "Kinds::Address(uint)", ".managed (.address { identity := "),
    ("Indirect", "Kinds::Indirect(method System.UInt32 *(System.UInt32)[],System.Int32,System.UInt32)",
        ".managed (.call "),
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
        Compile(extracted, "Extracted", path);
        var binding = "TemplateBindings" + index;
        File.Copy(Path.Combine(kindShared, binding + ".lean"), Path.Combine(extracted, binding + ".lean"),
            overwrite: true);
        Compile(extracted, binding, path);
    }
    Console.WriteLine($"PASS a {name} template elaborates and binds to each profile's own method indices");
}

void RejectLean(string name, string text, string path)
{
    var file = Path.Combine(directory, name + ".lean");
    File.WriteAllText(file, text);
    var result = Execute(["lean", file], leanPath: path);
    if (result.Code == 0 || !result.Output.Contains("rfl", StringComparison.Ordinal))
        throw new InvalidOperationException("Expected exact equality rejection: " + name + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + name);
}

var widePath = extractions[2] + Path.PathSeparator + sharedPath;
var wideBinding = File.ReadAllText(Path.Combine(shared, "TemplateBindings2.lean"));
RejectLean("WrongFlag", wideBinding.Replace("true true 1", "false false 1", StringComparison.Ordinal), widePath);
RejectLean("WrongCallee", wideBinding.Replace("true true 1", "true true 0", StringComparison.Ordinal), widePath);
RejectLean("WrongProfile", wideBinding.Replace("Extracted.profile", "FeatureProfile.scalar",
    StringComparison.Ordinal), widePath);
RejectLean("WrongEquation", """
import Templates
example (profile : CIL.FeatureProfile) (environment : CIL.LayoutEnvironment) (callee : Nat) :
    (Templates.method0 profile environment true true callee).code[1]? = some (.brfalse 6) := by rfl
""", sharedPath);
var changed = Path.Combine(directory, "ChangedBranch");
Directory.CreateDirectory(changed);
File.WriteAllText(Path.Combine(changed, "Templates.lean"),
    templates.Replace(".brfalse 5", ".brfalse 6", StringComparison.Ordinal));
Compile(changed, "Templates", changed + Path.PathSeparator + library);
RejectLean("WrongBranch", wideBinding, changed + Path.PathSeparator + widePath);

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

var staticOutputs = new[] { "scalar", "x64-v3" }.Select(profile =>
    Path.Combine(directory, "Static-" + profile)).ToArray();
for (var index = 0; index < staticOutputs.Length; index++)
    Run(["dotnet", ExtractorPath, "extract", assembly, "StaticDispatch::Read()", staticOutputs[index],
        index == 0 ? "scalar" : "x64-v3", "--assume-initialized", "StaticDispatch"]);
var staticShared = Path.Combine(directory, "StaticShared");
Run(["dotnet", ExtractorPath, "templates", staticShared, .. staticOutputs]);
var staticTemplate = File.ReadAllText(Path.Combine(staticShared, "Templates.lean"));
if (!staticTemplate.Contains("fieldName := \"System.UInt32 StaticDispatch::Bias\"", StringComparison.Ordinal))
    throw new InvalidOperationException("Static template omitted its field identity.");
var staticFiles = Directory.GetFiles(staticShared).ToDictionary(path => Path.GetFileName(path)!, File.ReadAllText);
Run(["dotnet", ExtractorPath, "templates", staticShared, .. staticOutputs]);
if (Directory.GetFiles(staticShared).Any(path => File.ReadAllText(path) != staticFiles[Path.GetFileName(path)]))
    throw new InvalidOperationException("Static template closure is not deterministic.");
Compile(staticShared, "Templates", staticShared + Path.PathSeparator + library);
for (var index = 0; index < staticOutputs.Length; index++)
{
    var path = staticOutputs[index] + Path.PathSeparator + staticShared + Path.PathSeparator + library;
    Compile(staticOutputs[index], "Extracted", path);
    var binding = "TemplateBindings" + index;
    File.Copy(Path.Combine(staticShared, binding + ".lean"), Path.Combine(staticOutputs[index], binding + ".lean"),
        overwrite: true);
    Compile(staticOutputs[index], binding, path);
}
var staticBinding = File.ReadAllText(Path.Combine(staticShared, "TemplateBindings0.lean"));
var staticPath = staticOutputs[0] + Path.PathSeparator + library;
var changedStatic = Path.Combine(directory, "ChangedStatic");
Directory.CreateDirectory(changedStatic);
File.WriteAllText(Path.Combine(changedStatic, "Templates.lean"),
    staticTemplate.Replace("StaticDispatch::Bias", "StaticDispatch::Changed", StringComparison.Ordinal));
Compile(changedStatic, "Templates", changedStatic + Path.PathSeparator + library);
RejectLean("ChangedStaticIdentity", staticBinding, changedStatic + Path.PathSeparator + staticPath);
var siteStart = staticTemplate.IndexOf("staticSites := [", StringComparison.Ordinal);
var siteEnd = staticTemplate.IndexOf("], declared := ", siteStart, StringComparison.Ordinal);
if (siteStart < 0 || siteEnd < 0) throw new InvalidOperationException("Static template has no descriptor list.");
var missingStatic = Path.Combine(directory, "MissingStatic");
Directory.CreateDirectory(missingStatic);
File.WriteAllText(Path.Combine(missingStatic, "Templates.lean"),
    staticTemplate[..siteStart] + "staticSites := [" + staticTemplate[siteEnd..]);
Compile(missingStatic, "Templates", missingStatic + Path.PathSeparator + library);
RejectLean("MissingStaticMetadata", staticBinding, missingStatic + Path.PathSeparator + staticPath);
Console.WriteLine("PASS deterministic static metadata, exact profile bindings " +
    "and changed/missing descriptor rejection");
