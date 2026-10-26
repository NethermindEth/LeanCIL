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
void Emit() => run.Invoke(null, [new[] { output, first, second }, read]);
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
variants[second] = Variant(second, true, [Method("Caller", ".ret"), Method("Caller", ".ret")]);
try { Emit(); throw new Exception("Duplicate managed identity was accepted"); }
catch (TargetInvocationException error) when (error.InnerException is InvalidDataException rejected &&
    rejected.Message == "Template inputs contain ambiguous managed method identities.") { }
Console.WriteLine("PASS template order, reordered callees, absent-callee placeholders and duplicate rejection");

partial class Program
{
    static Func<string, T> ReadVariants<T>(Dictionary<string, object> variants) => path => (T)variants[path];
}
