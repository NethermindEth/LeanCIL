#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Reflection;
using System.Text.Json;

var assembly = Assembly.LoadFrom(ExtractorPath);
var emitter = assembly.GetType("Nethermind.LeanCIL.TemplateEmitter", true)!;
var variantType = emitter.GetNestedType("Variant", BindingFlags.NonPublic)!;
var run = emitter.GetMethod("Run", BindingFlags.Static | BindingFlags.NonPublic)!;
var root = Path.GetFullPath(At("artifacts/TemplateIndexes"));
var first = Path.Combine(root, "First");
var second = Path.Combine(root, "Second");
var output = Path.Combine(root, "Shared");
object Variant(string path, bool avx, object[] methods) => JsonSerializer.Deserialize(JsonSerializer.Serialize(new
{
    Directory = path, AssemblyHash = "same", Profile = new
    {
        Name = avx ? "x64-v3" : "scalar", Architecture = avx ? "x64" : "scalar", NativeWidth = 64,
        LittleEndian = true, Avx2 = avx
    }, Methods = methods
}), variantType)!;
object Method(string identity, params string[] ops) => new
{
    Identity = identity, Metadata = "locals := [], returnsValue := false", Ops = ops, HasStaticSites = false
};
var variants = new Dictionary<string, object>(StringComparer.Ordinal)
{
    [first] = Variant(first, false, [Method("Caller", ".feature .avx2", ".nop", ".ret")]),
    [second] = Variant(second, true,
        [Method("Helper", ".ret"), Method("Caller", ".feature .avx2", ".call 0 0", ".ret")])
};
var read = typeof(Program).GetMethod(nameof(ReadVariants), BindingFlags.Static | BindingFlags.NonPublic)!
    .MakeGenericMethod(variantType).Invoke(null, [variants]);
void Emit(params string[] options) => EmitTo(output, options);
void EmitTo(string target, params string[] options) =>
    run.Invoke(null, [(string[])[target, first, second, .. options], read]);
// The emitter's own exceptions arrive wrapped by the reflective call.
string Rejected(Action action)
{
    try { action(); }
    catch (TargetInvocationException error) when (error.InnerException is InvalidDataException or ArgumentException)
    {
        return error.InnerException!.Message;
    }
    throw new Exception("An invalid template option or stale output was accepted");
}
Emit();
var templates = File.ReadAllText(Path.Combine(output, "Templates.lean"));
var firstBinding = File.ReadAllText(Path.Combine(output, "TemplateBindings0.lean"));
var secondBinding = File.ReadAllText(Path.Combine(output, "TemplateBindings1.lean"));
if (!templates.Contains("if avx2 then (.call callee0 0) else (.nop)", StringComparison.Ordinal) ||
    !firstBinding.Contains("Templates.method0 Extracted.profile false 0", StringComparison.Ordinal) ||
    !secondBinding.Contains("Templates.method1 Extracted.profile)", StringComparison.Ordinal) ||
    !secondBinding.Contains("Templates.method0 Extracted.profile true 0", StringComparison.Ordinal))
    throw new Exception("Template ordering, method remapping or excluded-callee placeholder changed");
var expected = Directory.GetFiles(output).ToDictionary(path => Path.GetFileName(path)!, File.ReadAllText);
Emit();
if (Directory.GetFiles(output).Any(path => File.ReadAllText(path) != expected[Path.GetFileName(path)]))
    throw new Exception("Template output is not deterministic");
if (Directory.GetFiles(output).Any(path => File.ReadAllText(path).Contains('\r')))
    throw new Exception("Template output has a CR line ending");
Emit("--check");
var shared = Path.Combine(output, "Templates.lean");
File.WriteAllText(shared, templates.Replace("end Templates", "end Changed"));
if (!Rejected(() => Emit("--check")).Contains("Template output differs: " + shared) ||
    File.ReadAllText(shared).Contains("end Templates"))
    throw new Exception("--check accepted a changed template, or repaired it");
Emit();
var extra = Path.Combine(output, "TemplateBindings2.lean");
File.WriteAllText(extra, firstBinding);
if (!Rejected(() => Emit("--check")).Contains("Template output has no input: " + extra))
    throw new Exception("--check accepted a binding with no input extraction");
File.Delete(extra);
File.Delete(Path.Combine(output, "templates.json"));
if (!Rejected(() => Emit("--check")).Contains("Template output missing"))
    throw new Exception("--check accepted missing template output");
Emit();

var shaped = Path.Combine(root, "Shaped");
var module = Path.Combine(shaped, "Proofs", "Shared.lean");
EmitTo(shaped, "--namespace", "Proofs.Bodies", "--omit-equations", "--module", module);
var shapedTemplates = File.ReadAllText(module);
var shapedBinding = File.ReadAllText(Path.Combine(shaped, "TemplateBindings1.lean"));
using var shapedManifest = JsonDocument.Parse(File.ReadAllText(Path.Combine(shaped, "templates.json")));
if (File.Exists(Path.Combine(shaped, "Templates.lean")) ||
    !shapedTemplates.StartsWith("import CIL.InstructionEquations\n", StringComparison.Ordinal) ||
    !shapedTemplates.Contains("namespace Proofs.Bodies\n") || !shapedTemplates.Contains("end Proofs.Bodies\n") ||
    shapedTemplates.Contains("cil_instruction_equations") || shapedTemplates.Contains("_instruction") ||
    shapedTemplates.Replace("Proofs.Bodies", "Templates") != templates.Replace(
        "cil_instruction_equations method0\n#print axioms method0_instruction2\n", "")
        .Replace("cil_instruction_equations method1\n#print axioms method1_instruction0\n", "") ||
    !shapedBinding.Contains("import Proofs.Shared\n") || !shapedBinding.Contains("some (Proofs.Bodies.method0 ") ||
    shapedManifest.RootElement.GetProperty("module").GetString() != "Proofs.Shared" ||
    shapedManifest.RootElement.GetProperty("instructionEquations").GetBoolean() ||
    shapedManifest.RootElement.GetProperty("methods")[0].GetProperty("name").GetString() != "Proofs.Bodies.method0")
    throw new Exception("The namespace, module or equation options changed more than they name:\n" +
        shapedTemplates + "\n" + shapedBinding);
EmitTo(shaped, "--namespace", "Proofs.Bodies", "--omit-equations", "--module", module, "--check");
if (!Rejected(() => EmitTo(shaped, "--module", Path.Combine(root, "Outside.lean"))).Contains("--module") ||
    !Rejected(() => EmitTo(shaped, "--namespace", "Bad Name")).Contains("--namespace"))
    throw new Exception("A module outside the output or an invalid namespace was accepted");
Console.WriteLine("PASS template --check, LF output, namespace, module and omitted equations");

variants[second] = Variant(second, true, [Method("Caller", ".ret"), Method("Caller", ".ret")]);
try { Emit(); throw new Exception("Duplicate managed identity was accepted"); }
catch (TargetInvocationException error) when (error.InnerException is InvalidDataException rejected &&
    rejected.Message == "Template inputs contain ambiguous managed method identities.") { }
Console.WriteLine("PASS template order, reordered callees, absent-callee placeholders and duplicate rejection");

partial class Program
{
    static Func<string, T> ReadVariants<T>(Dictionary<string, object> variants) => path => (T)variants[path];
}
