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
Type Model(string name) => assembly.GetType("Nethermind.LeanCIL." + name, true)!;
object Create(string name, params object?[] arguments) => Activator.CreateInstance(Model(name), arguments)!;
Array Typed(Type element, IEnumerable<object> items)
{
    var values = items.ToArray();
    var array = Array.CreateInstance(element, values.Length);
    for (var index = 0; index < values.Length; index++) array.SetValue(values[index], index);
    return array;
}
object Listed(Type element, IEnumerable<object> items) =>
    Activator.CreateInstance(Model("ValueList`1").MakeGenericType(element), Typed(element, items))!;
object Variant(string path, bool avx, object[] methods) => Activator.CreateInstance(variantType, path, "same",
    JsonSerializer.Deserialize(JsonSerializer.Serialize(new
    {
        Name = avx ? "x64-v3" : "scalar", Architecture = avx ? "x64" : "scalar", NativeWidth = 64,
        LittleEndian = true, Avx2 = avx
    }), Model("FeatureProfile"))!, Typed(emitter.GetNestedType("Method", BindingFlags.NonPublic)!, methods))!;
// The only operations the fixtures need: a feature test, a nop, a return and a static call.
object Operation(object operation) => operation is not string text ? operation : text switch
{
    ".feature .avx2" => Create("FeatureTest", Enum.Parse(Model("Feature"), "Avx2")),
    ".nop" => Create("StackOperation", Enum.Parse(Model("StackOpcode"), "Nop")),
    ".ret" => Create("Return", [null]),
    ".call 0 0" => Create("Call", Enum.Parse(Model("CallKind"), "Static"), 0, 0),
    ".tailCall 0 0" => Create("Call", Enum.Parse(Model("CallKind"), "Tail"), 0, 0),
    ".tailCall 1 0" => Create("Call", Enum.Parse(Model("CallKind"), "Tail"), 1, 0),
    _ => throw new ArgumentException("Unmodelled fixture operation: " + text)
};
object FrameOf(bool returnsValue, params object[] sites) => Create("FrameMetadata", returnsValue,
    Listed(Model("InitialValue"), []), Listed(Model("LocalKind"), []), Listed(typeof(int), []),
    Listed(Model("ParameterHome"), []), Listed(Model("StaticSite"), sites));
object MethodIn(string identity, object frame, params object[] ops) => Activator.CreateInstance(
    emitter.GetNestedType("Method", BindingFlags.NonPublic)!, identity, frame,
    Typed(Model("Operation"), ops.Select(Operation)))!;
object Method(string identity, params object[] ops) => MethodIn(identity, FrameOf(false), ops);
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

// A tail call names its callee by the template's parameter too, whatever index each profile gives it.
var tailRoot = Path.Combine(root, "Tail");
var (tailFirst, tailSecond, tailOutput) = (Path.Combine(tailRoot, "First"), Path.Combine(tailRoot, "Second"),
    Path.Combine(tailRoot, "Shared"));
variants[tailFirst] = Variant(tailFirst, false, [Method("Target", ".ret"), Method("Tail", ".tailCall 0 0")]);
variants[tailSecond] = Variant(tailSecond, true, [Method("Tail", ".tailCall 1 0"), Method("Target", ".ret")]);
run.Invoke(null, [(string[])[tailOutput, tailFirst, tailSecond], read]);
if (!File.ReadAllText(Path.Combine(tailOutput, "Templates.lean")).Contains(".tailCall callee0 0",
    StringComparison.Ordinal))
    throw new Exception("A tail call kept its profile's callee index in the template");
Console.WriteLine("PASS template tail calls take the callee parameter of the profile-specific index");

// A virtual dispatch, a callable pointer and a static initializer name their methods by the template's callee
// parameters too, whatever index each profile gives them.
object Entry(string identity, int method) => Create("ManagedTarget", identity, method);
object InitializedSite(int initializer) => Create("StaticSite", 0, Create("StaticIdentityRecord", "id", "asm", "fld"),
    "fld", Listed(typeof(byte), []), Create("InitializedStaticValue", null, initializer, Listed(typeof(string), []),
        null, false));
string SharedBody(string name, Func<int, object> caller)
{
    var directory = Path.Combine(root, name);
    var (one, two, shared) = (Path.Combine(directory, "First"), Path.Combine(directory, "Second"),
        Path.Combine(directory, "Shared"));
    variants[one] = Variant(one, false, [Method("Target", ".ret"), caller(0)]);
    variants[two] = Variant(two, true, [caller(1), Method("Target", ".ret")]);
    run.Invoke(null, [(string[])[shared, one, two], read]);
    return File.ReadAllText(Path.Combine(shared, "Templates.lean"));
}
var numbered = new (string Name, Func<int, object> Caller, string Expected)[]
{
    ("CallVirtual", target => Method("Caller", Create("CallVirtual", Listed(typeof((string, int)),
        [("Class", target)]), 1), ".ret"), ".callVirtual [(Class, callee0)] 1"),
    ("MethodAddress", target => Method("Caller", Create("MethodAddress", Entry("ID", target), "SIG"), ".ret"),
        ".managed (.address { identity := ID, method := callee0 } SIG)"),
    ("IndirectCall", target => Method("Caller", Create("IndirectCall", "SIG", Listed(Model("ManagedTarget"),
        [Entry("ID", target)]), false), ".ret"), ".managed (.call SIG [{ identity := ID, method := callee0 }] false)"),
    ("Initializer", target => MethodIn("Caller", FrameOf(false, InitializedSite(target)), ".ret"),
        "initializer := some { method := callee0, arguments := []")
};
foreach (var (name, caller, spelling) in numbered)
    if (!SharedBody("Numbered" + name, caller).Contains(spelling, StringComparison.Ordinal))
        throw new Exception($"A {name} kept its profile's method index in the template");
Console.WriteLine("PASS template dispatch, callable pointer and initializer methods take callee parameters");

// Records that render the same Lean are equal, so profiles whose instructions differ only in what the text
// leaves out merge; a real difference still fails at its instruction.
string Merge(string identity, object[] left, object[] right)
{
    var directory = Path.Combine(root, "Merge" + identity);
    var (one, two, shared) = (Path.Combine(directory, "First"), Path.Combine(directory, "Second"),
        Path.Combine(directory, "Shared"));
    variants[one] = Variant(one, false, [Method(identity, left)]);
    variants[two] = Variant(two, true, [Method(identity, right)]);
    run.Invoke(null, [(string[])[shared, one, two], read]);
    return File.ReadAllText(Path.Combine(shared, "Templates.lean"));
}
object Scalar(string function, int width, bool signed, int result, int arguments) => Create("ScalarIntrinsic",
    Named(Model("ScalarFunction"), function), width, signed, result, arguments);
object Named(Type type, string value) => Enum.Parse(type, value);
object ClassWord(bool store, int width, bool signed) => Create("ClassField", Create("ClassViews+FieldOperation",
    store, "T", 0, Named(Model("ClassViews+FieldKind"), "Word"), width, signed, null));
var merged = new (string Identity, object Left, object Right, string Expected)[]
{
    ("BigMul", Scalar("BigMul32", 32, true, 32, 2), Scalar("BigMul32", 64, true, 32, 2),
        ".intrinsic (.scalar (.bigMul32 true)) 2"),
    ("PopCount", Scalar("PopCount", 32, true, 32, 1), Scalar("PopCount", 32, false, 32, 1),
        ".intrinsic (.scalar (.popCount 32 .word32)) 1"),
    ("Store", ClassWord(true, 4, true), ClassWord(true, 4, false), ".memory (.setObjectField (T) 0 4)")
};
foreach (var (identity, left, right, spelling) in merged)
    if (!Merge(identity, [left, ".ret"], [right, ".ret"]).Contains(spelling, StringComparison.Ordinal))
        throw new Exception($"A {identity} instruction that renders the same in both profiles did not merge");
if (!Rejected(() => Merge("Rotate", [Scalar("RotateLeft", 32, false, 32, 2), ".ret"],
        [Scalar("RotateLeft", 64, false, 32, 2), ".ret"]))
    .Contains("Profiles with identical observed flags emit different instructions: Rotate at pc 0"))
    throw new Exception("Profiles that render a rotate differently merged");
Console.WriteLine("PASS template merge accepts what the Lean text equates and names the instruction that differs");

// Profiles must agree on the frame and the instruction count before any instruction is compared.
string Differing(string identity, object leftFrame, object[] left, object rightFrame, object[] right)
{
    var directory = Path.Combine(root, "Differing" + identity);
    var (one, two, shared) = (Path.Combine(directory, "First"), Path.Combine(directory, "Second"),
        Path.Combine(directory, "Shared"));
    variants[one] = Variant(one, false, [MethodIn(identity, leftFrame, left)]);
    variants[two] = Variant(two, true, [MethodIn(identity, rightFrame, right)]);
    return Rejected(() => run.Invoke(null, [(string[])[shared, one, two], read]));
}
if (!Differing("Frame", FrameOf(false), [".ret"], FrameOf(true), [".ret"])
        .Contains("Template metadata or instruction count differs between profiles: Frame") ||
    !Differing("Count", FrameOf(false), [".ret"], FrameOf(false), [".nop", ".ret"])
        .Contains("Template metadata or instruction count differs between profiles: Count") ||
    !Differing("Leaf", FrameOf(false), [".nop", ".ret"], FrameOf(false), [".ret", ".ret"])
        .Contains("Profiles with identical observed flags emit different instructions: Leaf at pc 0"))
    throw new Exception("Profiles that differ in frame, length or an unflagged instruction were merged");
Console.WriteLine("PASS template merge rejects differing frames, lengths and unflagged instructions");

// The template merge and renderer are linear in a method's instructions: four times the code must cost far less
// than the sixteen times a quadratic pass over it would.
TimeSpan EmitTime(int length)
{
    var scaleRoot = Path.Combine(root, "Scale" + length);
    var (one, two) = (Path.Combine(scaleRoot, "First"), Path.Combine(scaleRoot, "Second"));
    string[] ops = [.. Enumerable.Repeat(".nop", length), ".ret"];
    variants[one] = Variant(one, false, [Method("Long", ops)]);
    variants[two] = Variant(two, true, [Method("Long", ops)]);
    var best = TimeSpan.MaxValue;
    for (var attempt = 0; attempt < 3; attempt++)
    {
        var clock = System.Diagnostics.Stopwatch.StartNew();
        run.Invoke(null, [(string[])[Path.Combine(scaleRoot, "Out" + attempt), one, two], read]);
        best = TimeSpan.FromTicks(Math.Min(best.Ticks, clock.Elapsed.Ticks));
    }
    return best;
}
var (small, large) = (EmitTime(20_000), EmitTime(80_000));
if (large.TotalMilliseconds > 8 * Math.Max(small.TotalMilliseconds, 5))
    throw new Exception($"Template emission grew faster than linearly: {small.TotalMilliseconds:F0} ms for 20000 " +
        $"instructions, {large.TotalMilliseconds:F0} ms for 80000");
Console.WriteLine("PASS template emission is linear in the instructions " +
    $"({small.TotalMilliseconds:F0} ms, {large.TotalMilliseconds:F0} ms)");

partial class Program
{
    static Func<string, T> ReadVariants<T>(Dictionary<string, object> variants) => path => (T)variants[path];
}
