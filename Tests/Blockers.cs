#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Reflection;
using System.Text.Json;

// Admission report: shared blockers are deduplicated with every chain, excluded branches stay silent.
var directory = At("artifacts/Blockers");
var source = Path.Combine(directory, "Assembly");
Directory.CreateDirectory(source);
File.WriteAllText(Path.Combine(source, "Fixture.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
""");
var fixture = """
using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics.X86;

public static class Fixture
{
    public static ulong Admitted(ulong x, ulong y) => x + y;

    [MethodImpl(MethodImplOptions.NoInlining)]
    static int Helper(int x) => System.GC.GetGeneration(new float[x]);

    public static int First(int x) => Helper(x);

    public static int Second(int x) => Helper(x) + 1;

    public static int External(int x) => x + System.Environment.ProcessorCount;

    public static int Size<T>() where T : unmanaged => Unsafe.SizeOf<T>();

    public static ulong Excluded(ulong x, ulong y)
    {
        if (Avx2.IsSupported) return (ulong)System.GC.GetGeneration(new double[(int)x]);
        return x + y;
    }
}

public struct Pair
{
    public int First;
    public long Second;
}

public sealed class Counter
{
    int total;

    public int Add(int x)
    {
        total += x;
        return new decimal[x].Length;
    }
}

public static class Signatures
{
    public static int Measure(string text, int x) => new decimal[x].Length;
}

public struct Point
{
    public int X { get; init; }
}

public static class Views
{
    static int value;

    public static ref readonly int Peek(int x)
    {
        value = new decimal[x].Length;
        return ref value;
    }
}

public struct Cell<T>
{
    public int Twice(int x) => new decimal[x].Length + x;
}

public static class Seeded
{
    public static readonly int Seed = System.Environment.TickCount;
}
""";
File.WriteAllText(Path.Combine(source, "Fixture.cs"), fixture);
Run(["dotnet", "build", Path.Combine(source, "Fixture.csproj"), "-c", "Release"]);
var assembly = Path.Combine(source, "bin/Fixture.dll");
int LineOf(string text) => fixture.Split('\n').Select((line, index) => (line, index)).Single(l => l.line.Contains(text)).index + 1;

var manifest = Path.Combine(directory, "manifest.json");
File.WriteAllText(manifest, JsonSerializer.Serialize(new
{
    entries = new object[]
    {
        new { signature = "Fixture::Admitted(ulong,ulong)", profile = "scalar" },
        new { signature = "Fixture::First(int)", profile = "scalar" },
        new { signature = "Fixture::Second(int)", profile = "scalar" },
        new { signature = "Fixture::Excluded(ulong,ulong)", profile = "scalar" },
        new { signature = "Fixture::Excluded(ulong,ulong)", profile = "x64-v3" },
        new { signature = "Fixture::Missing(int)", profile = "scalar" },
        new { signature = "Fixture::Admitted(ulong,ulong)", profile = "x64-unknown" },
        new { signature = "Fixture::External(int)", profile = "scalar" },
        new { signature = "Fixture::Size()", profile = "scalar", typeArguments = new[] { "Pair" } },
        new { signature = "Fixture::Size()", profile = "scalar", typeArguments = new[] { "System.String" } },
        new { signature = "Fixture::Size()", profile = "scalar", typeArguments = "Pair" },
        new { signature = "Counter::Add(int)", profile = "scalar" },
        new { signature = "Signatures::Measure(string,int)", profile = "scalar" },
        new { signature = "Point::set_X(int)", profile = "scalar" },
        new { signature = "Cell`1::Twice(int)", profile = "scalar" },
        new { signature = "Seeded::.cctor()", profile = "scalar" },
        new { signature = "Views::Peek(int)", profile = "scalar" }
    }
}));
var report = Path.Combine(directory, "blockers.json");
var summary = Run(["dotnet", ExtractorPath, "blockers", assembly, "--manifest", manifest, "--output", report]);
var json = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(report));
var entries = json.GetProperty("entries").EnumerateArray().ToArray();
var blockers = json.GetProperty("blockers").EnumerateArray().ToArray();
var checks = 0;

void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message + "\n" + summary + "\n" + File.ReadAllText(report));
    checks++;
}
string[] Ids(int index) => entries[index].GetProperty("blockers").EnumerateArray().Select(e => e.GetString()!).ToArray();

string[] expected = ["admitted", "blocked", "blocked", "admitted", "blocked", "notChecked", "notChecked", "blocked",
    "admitted", "notChecked", "notChecked", "blocked", "blocked", "admitted", "blocked", "blocked", "blocked"];
Require(entries.Select(e => e.GetProperty("status").GetString()).SequenceEqual(expected), "Wrong entry classification");
Require(entries[0].GetProperty("method").GetString() == "System.UInt64 Fixture::Admitted(System.UInt64,System.UInt64)" &&
    entries[0].GetProperty("reachableMethods").GetInt32() == 1, "Admitted entry lost its resolved method");


// Validation continues past the first construct, and each construct is one blocker however many sites and entries reach it.
const string helper = "System.Int32 Fixture::Helper(System.Int32)";
const string excluded = "System.UInt64 Fixture::Excluded(System.UInt64,System.UInt64)";
JsonElement Blocker(string construct) => blockers.Single(b => b.GetProperty("construct").GetString() == construct);
string[] Reached(JsonElement blocker) => blocker.GetProperty("entries").EnumerateArray()
    .Select(e => e.GetProperty("profile").GetString() + " " + string.Join(" -> ", e.GetProperty("chains").EnumerateArray().Single().EnumerateArray().Select(m => m.GetString())))
    .Order(StringComparer.Ordinal).ToArray();
string Id(JsonElement blocker) => blocker.GetProperty("id").GetString()!;
Require(blockers.Select(b => b.GetProperty("construct").GetString()).Order(StringComparer.Ordinal)
    .SequenceEqual([
        "Custom modifiers are unsupported in method returns, except " +
            "modreq(System.Runtime.CompilerServices.IsExternalInit) directly on System.Void: " +
            "System.Int32& modreq(System.Runtime.InteropServices.InAttribute)",
        "Rejected external call: System.Int32 System.Environment::get_ProcessorCount()",
        "Rejected external call: System.Int32 System.Environment::get_TickCount()",
        "Rejected external call: System.Int32 System.GC::GetGeneration(System.Object)",
        "Unsupported aggregate layout: Counter",
        "Unsupported class instance method",
        "Unsupported instruction: newarr System.Decimal",
        "Unsupported instruction: newarr System.Double",
        "Unsupported instruction: newarr System.Single",
        "Unsupported method metadata: member of an open generic type",
        "Unsupported static field load: System.Int32 Views::value",
        "Unsupported static field store: stsfld System.Int32 Seeded::Seed",
        "Unsupported static field store: stsfld System.Int32 Views::value",
        "Unsupported static initialisation: static constructors are never extracted",
        "Unsupported type: System.String"]),
    "Expected one blocker per unsupported construct");
var allocation = Blocker("Unsupported instruction: newarr System.Single");
var generation = Blocker("Rejected external call: System.Int32 System.GC::GetGeneration(System.Object)");
Require(Reached(allocation).SequenceEqual([
    $"scalar System.Int32 Fixture::First(System.Int32) -> {helper}",
    $"scalar System.Int32 Fixture::Second(System.Int32) -> {helper}"]), "Wrong call chains: " + string.Join("; ", Reached(allocation)));
Require(Reached(generation).SequenceEqual([
    $"scalar System.Int32 Fixture::First(System.Int32) -> {helper}",
    $"scalar System.Int32 Fixture::Second(System.Int32) -> {helper}",
    $"x64-v3 {excluded}"]),
    "GetGeneration not shared across methods and profiles: " + string.Join("; ", Reached(generation)));
Require(generation.GetProperty("sites").EnumerateArray().Select(s => s.GetProperty("method").GetString())
    .Order(StringComparer.Ordinal)
    .SequenceEqual([helper, excluded]), "GetGeneration sites not kept per method");
Require(Ids(1).Order(StringComparer.Ordinal)
    .SequenceEqual(new[] { Id(allocation), Id(generation) }.Order(StringComparer.Ordinal)) &&
    Ids(1).SequenceEqual(Ids(2)), "Entries do not share the Helper blockers");

// The exact instruction, its offset and the PDB location name the construct.
var site = allocation.GetProperty("sites").EnumerateArray().Single();
var instruction = site.GetProperty("instruction").GetString()!;
Require(site.GetProperty("method").GetString() == helper &&
    instruction == $"IL_{site.GetProperty("ilOffset").GetInt32():x4}: newarr System.Single" &&
    site.GetProperty("message").GetString() == "Unsupported instruction: " + instruction, "Wrong blocking instruction: " + instruction);
Require(site.GetProperty("source").GetString()!.StartsWith(
    $"Fixture.cs:{LineOf("new float[x]")}:", StringComparison.Ordinal),
    "Wrong source location: " + site.GetProperty("source"));

// The AVX2 branch is folded away under scalar and reported only where the profile makes it live.
Require(Ids(3).Length == 0, "Excluded branch reported under the scalar profile");
var live = Blocker("Unsupported instruction: newarr System.Double");
var liveSite = live.GetProperty("sites").EnumerateArray().Single();
Require(Ids(4).Order(StringComparer.Ordinal)
    .SequenceEqual(new[] { Id(live), Id(generation) }.Order(StringComparer.Ordinal)) &&
    Reached(live).SequenceEqual([$"x64-v3 {excluded}"]) && liveSite.GetProperty("method").GetString() == excluded &&
    liveSite.GetProperty("source").GetString()!.StartsWith($"Fixture.cs:{LineOf("Avx2.IsSupported")}:", StringComparison.Ordinal),
    "Live AVX2 branch not reported");

// An unmodelled overload is named once at its call; the call is not reported again as untranslatable.
var external = Blocker("Rejected external call: System.Int32 System.Environment::get_ProcessorCount()");
var call = external.GetProperty("sites").EnumerateArray().Single();
Require(Ids(7).SequenceEqual([Id(external)]) && Reached(external).SequenceEqual(["scalar System.Int32 Fixture::External(System.Int32)"]) &&
    call.GetProperty("instruction").GetString() == $"IL_{call.GetProperty("ilOffset").GetInt32():x4}: call System.Int32 System.Environment::get_ProcessorCount()" &&
    call.GetProperty("source").GetString()!.StartsWith($"Fixture.cs:{LineOf("ProcessorCount")}:", StringComparison.Ordinal),
    "Unmodelled call not reported at its site");
Require(!blockers.Any(b => b.GetProperty("construct").GetString()!.StartsWith("Unsupported or unresolved call", StringComparison.Ordinal)),
    "Rejected call reported again by translation");
Require(entries[5].GetProperty("reason").GetString()!.Contains("No method matches selector"), "Bad signature lacks its reason");
Require(entries[6].GetProperty("reason").GetString()!.Contains("Unknown execution profile"), "Bad profile lacks its reason");
// A generic entry closes over a value type of its own module, and the report keeps the type arguments.
Require(entries[8].GetProperty("typeArguments").EnumerateArray().Select(e => e.GetString()).SequenceEqual(["Pair"]) &&
    summary.Contains("Fixture::Size<Pair>()"), "Closed generic entry lost its type arguments");
Require(entries[9].GetProperty("reason").GetString()!.Contains("Closed entry type arguments require"),
    "Reference type argument not rejected at selection");
Require(entries[10].GetProperty("reason").GetString()!.Contains("`typeArguments` must be an array"),
    "Malformed type arguments accepted");
Require(summary.Contains("4 admitted, 9 blocked, 4 not checked") && summary.Contains("nothing here is proved") &&
    !summary.Contains("verified", StringComparison.OrdinalIgnoreCase), "Summary overstates or misses counts");
// A rejected signature or receiver does not hide the body: its unsupported instruction is reported too.
string[] Constructs(int index) => Ids(index).Select(id => blockers.Single(b => Id(b) == id)
    .GetProperty("construct").GetString()!).ToArray();
var decimals = Blocker("Unsupported instruction: newarr System.Decimal");
Require(Constructs(12).Order(StringComparer.Ordinal).SequenceEqual(
    ["Unsupported instruction: newarr System.Decimal", "Unsupported type: System.String"]) &&
    decimals.GetProperty("sites").EnumerateArray().Any(s =>
        s.GetProperty("method").GetString() == "System.Int32 Signatures::Measure(System.String,System.Int32)"),
    "Rejected signature hid the body's blockers: " + string.Join("; ", Constructs(12)));
Require(Constructs(11).Order(StringComparer.Ordinal).SequenceEqual([
        "Unsupported aggregate layout: Counter",
        "Unsupported class instance method",
        "Unsupported instruction: newarr System.Decimal"]),
    "Reference-type receiver hid the body's blockers: " + string.Join("; ", Constructs(11)));
// A resolved entry of rejected shape is blocked, not unchecked, and its definition is still analysed.
// One condition is one blocker: the shape names the modifier, and the walk names the open generic owner.
Require(Constructs(16).Single(c => c.Contains("InAttribute")).StartsWith("Custom modifiers are unsupported",
        StringComparison.Ordinal) &&
    Constructs(16).Contains("Unsupported instruction: newarr System.Decimal") &&
    entries[16].GetProperty("method").GetString()!.EndsWith("Views::Peek(System.Int32)", StringComparison.Ordinal),
    "Modified return not analysed past its modifier: " + string.Join("; ", Constructs(16)));
Require(Constructs(14).Contains("Unsupported method metadata: member of an open generic type") &&
    !Constructs(14).Contains("Contract method requires an exact closed generic instantiation.") &&
    Constructs(14).Contains("Unsupported instruction: newarr System.Decimal"),
    "Open generic member not analysed past its shape: " + string.Join("; ", Constructs(14)));
// A static constructor is reported as itself, not again as its owner's static initialisation.
Require(Constructs(15).Count(c => c.StartsWith("Unsupported static initialisation", StringComparison.Ordinal)) == 1,
    "Static constructor reported twice: " + string.Join("; ", Constructs(15)));

// `admitted` means exactly that `extract` succeeds, so every well-formed entry is also extracted.
var manifestEntries = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(manifest)).GetProperty("entries")
    .EnumerateArray().ToArray();
for (var index = 0; index < entries.Length; index++)
{
    var entry = manifestEntries[index];
    string[]? typeArguments = !entry.TryGetProperty("typeArguments", out var listed) ? [] :
        listed.ValueKind == JsonValueKind.Array ? [.. listed.EnumerateArray().Select(a => a.GetString()!)] : null;
    if (typeArguments is null) continue;
    var output = Path.Combine(directory, "extract", index.ToString(System.Globalization.CultureInfo.InvariantCulture));
    var extracted = Execute(["dotnet", ExtractorPath, "extract", assembly, entry.GetProperty("signature").GetString()!,
        output, entry.GetProperty("profile").GetString()!,
        .. typeArguments.SelectMany(argument => new[] { "--type-argument", argument })]);
    Require((extracted.Code == 0) == (entries[index].GetProperty("status").GetString() == "admitted"),
        $"Entry {index} is {entries[index].GetProperty("status")} but extract exited {extracted.Code}:\n" +
        extracted.Output);
}
// The report groups the condition across methods; extract still names the method it stopped at.
var classInstance = Execute(["dotnet", ExtractorPath, "extract", assembly, "Counter::Add(int)",
    Path.Combine(directory, "extract", "class-instance"), "scalar"]);
Require(classInstance.Code != 0 && classInstance.Output.Contains("Unsupported class instance method") &&
    classInstance.Output.Contains("Method: System.Int32 Counter::Add(System.Int32)"),
    "extract no longer names the class instance method it rejects:\n" + classInstance.Output);

// MSBuild configuration names are case-insensitive, so a `-c release` build is a Release build.
string BuildAs(string configuration)
{
    var output = Path.Combine(directory, "configuration", configuration);
    Run(["dotnet", "build", Path.Combine(source, "Fixture.csproj"), "-c", configuration, "-o", output]);
    return Path.Combine(output, "Fixture.dll");
}
(int Code, string Output, string Stdout, string Stderr) ExtractAdmitted(string dll, string configuration) =>
    Execute(["dotnet", ExtractorPath, "extract", dll, "Fixture::Admitted(ulong,ulong)",
        Path.Combine(directory, "extract", configuration), "scalar"]);
var lowercase = ExtractAdmitted(BuildAs("release"), "release");
Require(lowercase.Code == 0, "A `-c release` build is rejected:\n" + lowercase.Output);
var debug = ExtractAdmitted(BuildAs("Debug"), "Debug");
Require(debug.Code != 0 && debug.Output.Contains("build configuration"),
    "A Debug build is accepted:\n" + debug.Output);

// Distinct arrays and sites are compared by content, while output keeps first discovery order.
var blockersType = Assembly.LoadFrom(ExtractorPath).GetType("Nethermind.LeanCIL.Blockers", true)!;
var findingType = blockersType.GetNestedType("Finding", BindingFlags.NonPublic)!;
var siteType = blockersType.GetNestedType("Site", BindingFlags.NonPublic)!;
const BindingFlags instanceMembers = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;
object Construct(Type type, params object?[] values) => Activator.CreateInstance(type, instanceMembers,
    null, values, null)!;
var finding = Construct(findingType, "construct");
var add = findingType.GetMethod("Add", instanceMembers)!;
void Add(int offset, string profile, string[] chain) => add.Invoke(finding,
    [Construct(siteType, "Method", offset, "op", "source", "message"), "Entry", profile, chain]);
Add(1, "scalar", ["Entry", "ab", "c"]);
Add(1, "scalar", ["Entry", "ab", "c"]);
Add(1, "scalar", ["Entry", "a", "bc"]);
Add(2, "scalar", ["Entry", "ab", "c"]);
Add(1, "Scalar", ["Entry", "ab", "c"]);
var sites = (System.Collections.IList)findingType.GetProperty("Sites", instanceMembers)!.GetValue(finding)!;
var reaches = (System.Collections.IList)findingType.GetProperty("Entries", instanceMembers)!.GetValue(finding)!;
var reach = reaches[0]!;
var chains = (List<string[]>)reach.GetType().GetProperty("Chains", instanceMembers)!.GetValue(reach)!;
Require(sites.Count == 2 && reaches.Count == 2 && chains.Count == 2 &&
    chains[0].SequenceEqual(new[] { "Entry", "ab", "c" }) &&
    chains[1].SequenceEqual(new[] { "Entry", "a", "bc" }),
    "Blocker indexes lost content equality, profile case or chain order");

// LeanCIL's own assembly against its checked-in baseline, then the gate's decisions on altered baselines.
const string selfAdmission = "Tests/SelfAdmission.cs";
Run(["dotnet", "run", "--file", selfAdmission], streamOutput: true, progress: "Self-admission");
var selfReport = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(At("artifacts/SelfAdmission/blockers.json")))
    .GetProperty("entries").EnumerateArray().ToArray();
string? Existing(string status) => selfReport.FirstOrDefault(e => e.GetProperty("status").GetString() == status)
    is { ValueKind: JsonValueKind.Object } entry ? entry.GetProperty("signature").GetString() : null;
(int Code, string Output) Gate(params string[] lines)
{
    var path = Path.Combine(directory, "self-baseline.txt");
    File.WriteAllLines(path, lines);
    var result = Execute(["dotnet", "run", "--file", selfAdmission, "--", "--baseline", path, "--reuse-report"]);
    return (result.Code, result.Output);
}
// Losing an admission that still exists is the only failure.
var blockedMethod = Existing("blocked")!;
var lostAdmission = Gate(blockedMethod);
Require(lostAdmission.Code != 0 && lostAdmission.Output.Contains("no longer admitted") &&
    lostAdmission.Output.Contains(blockedMethod), "Lost admission passed the gate:\n" + lostAdmission.Output);
// Removed methods and gained admissions are reported, since the tool's own method set changes every PR.
const string gone = "System.Int32 Gone::Removed()";
var admittedMethod = Existing("admitted");
var reported = Gate(gone);
Require(reported.Code == 0 && !reported.Output.Contains("Lost admissions") &&
    reported.Output.Contains("Removed admitted methods:") && reported.Output.Contains(gone) &&
    (admittedMethod is null || reported.Output.Contains("Gained admissions") &&
        reported.Output.Contains(admittedMethod)),
    "Removed or gained methods misreported:\n" + reported.Output);
Console.WriteLine($"PASS {checks} admission report checks");
