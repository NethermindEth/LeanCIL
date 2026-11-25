#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

using System.Reflection;
using System.Text.Json;

var assembly = Assembly.LoadFrom(ExtractorPath);
// The reflected CLI reads its bundled verification sources beside the extractor executable.
var savedBase = AppContext.GetData("APP_CONTEXT_BASE_DIRECTORY");
try
{
    AppContext.SetData("APP_CONTEXT_BASE_DIRECTORY", Path.GetDirectoryName(assembly.Location) +
        Path.DirectorySeparatorChar);
    System.Runtime.CompilerServices.RuntimeHelpers.RunClassConstructor(assembly.GetType("Program", true)!.TypeHandle);
}
finally { AppContext.SetData("APP_CONTEXT_BASE_DIRECTORY", savedBase); }
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
Dictionary<object, string> bodies = new(ReferenceEqualityComparer.Instance);
object Variant(string path, bool avx, object[] methods)
{
    var profile = JsonSerializer.Deserialize(JsonSerializer.Serialize(new
    {
        Name = avx ? "x64-v3" : "scalar", Architecture = avx ? "x64" : "scalar", NativeWidth = 64,
        LittleEndian = true, Avx2 = avx
    }), Model("FeatureProfile"))!;
    var variant = Activator.CreateInstance(variantType, path, "same", profile,
        Typed(emitter.GetNestedType("Method", BindingFlags.NonPublic)!, methods))!;
    var inputs = string.Concat(methods.Select((method, index) => $"def method{index} : Method := {bodies[method]}\n"));
    variantType.GetField("DecoderInputs", BindingFlags.Instance | BindingFlags.NonPublic)!.SetValue(variant, inputs);
    return variant;
}
FixtureSite Site(object instruction) => instruction switch
{
    FixtureSite site => site,
    "call 0" => new(".call (.arity 0)", ".direct 0"),
    "tail call 0" => new(".call (.arity 0) { tail := true }", ".direct 0"),
    "tail call 1" => new(".call (.arity 0) { tail := true }", ".direct 1"),
    string code => new(code),
    _ => throw new ArgumentException("Unrecognised template fixture instruction")
};
object FrameOf(bool returnsValue, params object[] sites) => Create("FrameMetadata", returnsValue,
    Listed(Model("InitialValue"), []), Listed(Model("LocalKind"), []), Listed(typeof(int), []),
    Listed(Model("ParameterHome"), []), Listed(Model("StaticSite"), sites),
    "{ parameters := [], returnType := .void }");
object MethodIn(string identity, object frame, int[] linked, params object[] ops)
{
    var sites = ops.Select(Site).ToArray();
    var features = sites.Select(site => site.Feature).OfType<string>().Distinct(StringComparer.Ordinal)
        .Select(feature => Named(Model("Feature"), feature)).ToArray();
    var method = Activator.CreateInstance(emitter.GetNestedType("Method", BindingFlags.NonPublic)!,
        identity, frame, Typed(Model("Feature"), features), new int[sites.Length], linked)!;
    var links = string.Join(", ", sites.Index().Where(pair => pair.Item.Link is not null)
        .Select(pair => $"({pair.Index}, {pair.Item.Link})"));
    var firstOther = Array.FindIndex(sites, site => site.Code != ".nop");
    var prefix = firstOther < 0 ? sites.Length : firstOther;
    var code = "[" + string.Join(", ", sites.Skip(prefix).Select(site => site.Code)) + "]";
    if (prefix > 0) code = $"List.replicate {prefix} .nop ++ " + code;
    bodies.Add(method, $"{{ code := {code}, locals := [], returnsValue := false, links := [{links}] }}");
    return method;
}
object Method(string identity, params object[] ops) => MethodIn(identity, FrameOf(false), [], ops);
object Linked(string identity, int target, params object[] ops) => MethodIn(identity, FrameOf(false), [target], ops);
var avx2Getter = new FixtureSite(".call { owner := .atom Extraction.intrinsicsScope \"System.Runtime.Intrinsics.X86.Avx2\", " +
    "name := name!\"get_IsSupported\", hasThis := false, genericArity := 0, returnType := .primitive .boolean, parameters := [] }", Feature: "Avx2");
var variants = new Dictionary<string, object>(StringComparer.Ordinal)
{
    [first] = Variant(first, false, [Method("Caller", avx2Getter, ".nop", ".ret")]),
    [second] = Variant(second, true,
        [Method("Helper", ".ret"), Linked("Caller", 0, avx2Getter, "call 0", ".ret")])
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
if (!templates.Contains("if avx2 then (Input1.method1.code) else (Input0.method0.code)", StringComparison.Ordinal) ||
    !templates.Contains("(Input1.method1.reindexLinks (fun | 0 => callee0 | index => index)).links",
        StringComparison.Ordinal) ||
    !firstBinding.Contains("Templates.method0 Extracted.profile Extracted.environment false 0",
        StringComparison.Ordinal) ||
    !secondBinding.Contains("Templates.method1 Extracted.profile Extracted.environment)", StringComparison.Ordinal) ||
    !secondBinding.Contains("Templates.method0 Extracted.profile Extracted.environment true 0",
        StringComparison.Ordinal))
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

// A tail call's link names its callee by the template's parameter too, whatever index each profile gives it.
var tailRoot = Path.Combine(root, "Tail");
var (tailFirst, tailSecond, tailOutput) = (Path.Combine(tailRoot, "First"), Path.Combine(tailRoot, "Second"),
    Path.Combine(tailRoot, "Shared"));
variants[tailFirst] = Variant(tailFirst, false, [Method("Target", ".ret"), Linked("Tail", 0, "tail call 0")]);
variants[tailSecond] = Variant(tailSecond, true, [Linked("Tail", 1, "tail call 1"), Method("Target", ".ret")]);
run.Invoke(null, [(string[])[tailOutput, tailFirst, tailSecond], read]);
var tailTemplate = File.ReadAllText(Path.Combine(tailOutput, "Templates.lean"));
if (!tailTemplate.Contains("cil_template_code% (Input0.method1.code)", StringComparison.Ordinal) ||
    !tailTemplate.Contains("links := (Input0.method1.reindexLinks (fun | 0 => callee0 | index => index)).links",
        StringComparison.Ordinal) ||
    !tailTemplate.Contains("(Input1.method0.reindexLinks (fun | 1 => callee0 | index => index)).links := rfl",
        StringComparison.Ordinal))
    throw new Exception("A tail call kept its profile's callee index in the template or lost its link");
Console.WriteLine("PASS template tail calls take the callee parameter of the profile-specific index");

// A virtual dispatch, a callable pointer and a static initializer name their methods by the template's callee
// parameters too, whatever index each profile gives them.
const string managedId = "{ owner := \"ID\", token := 1, arguments := [] }";
const string managedSignature = "{ result := .void, parameters := [] }";
object InitializedSite(int initializer) => Create("StaticSite", 0, Create("StaticIdentityRecord", "id", "asm", "fld"),
    Create("FieldRef", "T", 0, "U", ValueName()), Listed(typeof(byte), []),
    Create("InitializedStaticValue", null, initializer, Listed(typeof(string), []), null, false));
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
const string relocatedTarget = "(Input1.method0.reindexLinks (fun | 1 => callee0 | index => index)).links := rfl";
var numbered = new (string Name, Func<int, object> Caller, string Expected)[]
{
    ("CallVirtual", target => Linked("Caller", target,
        new FixtureSite(".callvirt (.arity 0)", $".virtual [(.void, {target})]"), ".ret"), relocatedTarget),
    ("MethodAddress", target => Linked("Caller", target,
        new FixtureSite($".ldftn {managedId} {managedSignature}", $".address {target}"), ".ret"),
        relocatedTarget),
    ("IndirectCall", target => Linked("Caller", target, new FixtureSite($".calli {managedSignature} false",
        $".indirect [{{ identity := {managedId}, method := {target} }}]"), ".ret"), relocatedTarget),
    ("Initializer", target => MethodIn("Caller", FrameOf(false, InitializedSite(target)), [], ".ret"),
        "initializer := some { method := callee0, arguments := []")
};
foreach (var (name, caller, spelling) in numbered)
    if (!SharedBody("Numbered" + name, caller).Contains(spelling, StringComparison.Ordinal))
        throw new Exception($"A {name} kept its profile's method index in the template");
Console.WriteLine("PASS template dispatch, callable pointer and initializer methods take callee parameters");

var dispatchDifference = Rejected(() => SharedBody("DifferentReceiver", target =>
    Linked("Caller", target, ".nop", new FixtureSite(".callvirt (.arity 0)",
        $".virtual [(.atom \"Fixture\" \"Receiver{target}\", {target})]"), ".ret")));
if (!dispatchDifference.Contains("different instructions: Caller at pc 1", StringComparison.Ordinal))
    throw new Exception("Equal call instructions with different receiver tables were merged: " + dispatchDifference);
Console.WriteLine("PASS differing dispatch metadata names the call pc after target renumbering");

// Canonical templates compare the decoded method operands.
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
object Named(Type type, string value) => Enum.Parse(type, value);
object ValueName() => Model("MetadataName").GetMethod("OfText", BindingFlags.Static | BindingFlags.NonPublic)!
    .Invoke(null, ["value"])!;
// Both template alternatives bind the closed runtime member that the compiled call names.
string ScalarCall(string owner, string name, string result, params string[] parameters)
{
    static string Word(string primitive) => $".primitive .{primitive}";
    return $$""".call { owner := .atom Extraction.runtimeScope "System.{{owner}}", name := name!"{{name}}", hasThis := false, genericArity := 0, returnType := {{Word(result)}}, parameters := [{{string.Join(", ", parameters.Select(Word))}}] }""";
}
var merged = new (string Identity, string Code)[]
{
    ("BigMul", ScalarCall("Math", "BigMul", "int64", "int32", "int32")),
    ("PopCount", ScalarCall("Numerics.BitOperations", "PopCount", "int32", "uint32"))
};
foreach (var (identity, code) in merged)
{
    var body = Merge(identity, [code, ".ret"], [$"id ({code} : Instruction)", ".ret"]);
    if (!body.Contains("cil_template_code% (Input0.method0.code)", StringComparison.Ordinal))
        throw new Exception($"The {identity} alternatives must share one decoded body.");
}
// A decoded field reference carries the whole operand, including its metadata name.
string Store(int index, string name) =>
    $".stfld {{ owner := .object \"Fixture\" \"Owner\", index := {index}, " +
    $"type := .primitive .uint32, name := name!\"{name}\" }}";
var store = Store(0, "word");
var sharedStore = Merge("Store", [".nop", store, ".ret"], [".nop", $"id ({store} : Instruction)", ".ret"]);
if (!sharedStore.Contains("cil_template_code% (Input0.method0.code)", StringComparison.Ordinal))
    throw new Exception("Equal decoded field stores failed to share a template body.");
foreach (var (identity, different) in new[] { ("FieldIndex", Store(1, "word")), ("FieldName", Store(0, "other")) })
    if (!Rejected(() => Merge(identity, [".nop", store, ".ret"], [".nop", different, ".ret"]))
        .Contains($"Profiles with identical observed flags emit different instructions: {identity} at pc 1"))
        throw new Exception("A store to a different field shared the template body.");
if (!Rejected(() => Merge("Rotate",
        [ScalarCall("Numerics.BitOperations", "RotateLeft", "uint32", "uint32", "int32"), ".ret"],
        [ScalarCall("Numerics.BitOperations", "RotateLeft", "uint64", "uint64", "int32"), ".ret"]))
    .Contains("Profiles with identical observed flags emit different instructions: Rotate at pc 0"))
    throw new Exception("Profiles that render a rotate differently merged");
Console.WriteLine("PASS template merge accepts what the Lean text equates and names the instruction that differs");

// Profiles must agree on the frame and the instruction count before any instruction is compared.
string Differing(string identity, object leftFrame, object[] left, object rightFrame, object[] right)
{
    var directory = Path.Combine(root, "Differing" + identity);
    var (one, two, shared) = (Path.Combine(directory, "First"), Path.Combine(directory, "Second"),
        Path.Combine(directory, "Shared"));
    variants[one] = Variant(one, false, [MethodIn(identity, leftFrame, [], left)]);
    variants[two] = Variant(two, true, [MethodIn(identity, rightFrame, [], right)]);
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

// At 64x instructions, a quadratic merge or renderer costs 4096x, above the 256x bound.
TimeSpan EmitTime(int length, ref int iterations, bool calibrate)
{
    var scaleRoot = Path.Combine(root, "Scale" + length);
    var (one, two) = (Path.Combine(scaleRoot, "First"), Path.Combine(scaleRoot, "Second"));
    string[] ops = [.. Enumerable.Repeat(".nop", length - 1), ".ret"];
    variants[one] = Variant(one, false, [Method("Long", ops)]);
    variants[two] = Variant(two, true, [Method("Long", ops)]);
    TimeSpan Measure(int repeats)
    {
        var best = TimeSpan.MaxValue;
        for (var attempt = 0; attempt < 3; attempt++)
        {
            var clock = System.Diagnostics.Stopwatch.StartNew();
            for (var iteration = 0; iteration < repeats; iteration++)
                run.Invoke(null, [(string[])[Path.Combine(scaleRoot, "Out" + attempt), one, two], read]);
            best = TimeSpan.FromTicks(Math.Min(best.Ticks, clock.Elapsed.Ticks));
        }
        return best;
    }
    var elapsed = Measure(iterations);
    const double minimumMilliseconds = 25;
    while (calibrate && elapsed.TotalMilliseconds < minimumMilliseconds)
    {
        iterations = checked(iterations * 2);
        elapsed = Measure(iterations);
    }
    return elapsed;
}
var iterations = 1;
var small = EmitTime(1_250, ref iterations, calibrate: true);
var large = EmitTime(80_000, ref iterations, calibrate: false);
if (large.TotalMilliseconds > 256 * small.TotalMilliseconds)
    throw new Exception($"Template emission grew faster than linearly: {small.TotalMilliseconds:F0} ms for 1250 " +
        $"instructions, {large.TotalMilliseconds:F0} ms for 80000");
Console.WriteLine("PASS template emission is linear in the instructions " +
    $"({small.TotalMilliseconds:F0} ms, {large.TotalMilliseconds:F0} ms for {iterations} emissions)");

sealed record FixtureSite(string Code, string? Link = null, string? Feature = null);

partial class Program
{
    static Func<string, T> ReadVariants<T>(Dictionary<string, object> variants) => path => (T)variants[path];
}
