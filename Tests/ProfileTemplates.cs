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
<TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize>
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
if (!renamed.Contains("Templates.method0 Extracted.profile true true 2", StringComparison.Ordinal))
    throw new InvalidOperationException("Wrapper extraction did not exercise changed managed callee indices.");
var library = FixtureLeanPath();
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
  TemplateProof.choose_returns Extracted.program {{entry}} {{callee}} Extracted.profile
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
example (profile : CIL.FeatureProfile) (callee : Nat) :
    (Templates.method0 profile true true callee).code[1]? = some (.brzero 6) := by rfl
""", sharedPath);
var changed = Path.Combine(directory, "ChangedBranch");
Directory.CreateDirectory(changed);
File.WriteAllText(Path.Combine(changed, "Templates.lean"),
    templates.Replace(".brzero 5", ".brzero 6", StringComparison.Ordinal));
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
