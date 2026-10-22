#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

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
    static int Helper(int x) => new int[x].Length;

    public static int First(int x) => Helper(x);

    public static int Second(int x) => Helper(x) + 1;

    public static ulong Excluded(ulong x, ulong y)
    {
        if (Avx2.IsSupported) return (ulong)new long[(int)x].Length;
        return x + y;
    }
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
        new { signature = "Fixture::Excluded(ulong,ulong)", profile = "x64-avx2" },
        new { signature = "Fixture::Missing(int)", profile = "scalar" },
        new { signature = "Fixture::Admitted(ulong,ulong)", profile = "x64-unknown" }
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

string[] expected = ["admitted", "blocked", "blocked", "admitted", "blocked", "notChecked", "notChecked"];
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
    .SequenceEqual(["Unsupported instruction: ldlen", "Unsupported instruction: newarr System.Int32", "Unsupported instruction: newarr System.Int64"]),
    "Expected one blocker per unsupported construct");
var allocation = Blocker("Unsupported instruction: newarr System.Int32");
var length = Blocker("Unsupported instruction: ldlen");
Require(Reached(allocation).SequenceEqual([
    $"scalar System.Int32 Fixture::First(System.Int32) -> {helper}",
    $"scalar System.Int32 Fixture::Second(System.Int32) -> {helper}"]), "Wrong call chains: " + string.Join("; ", Reached(allocation)));
Require(Reached(length).SequenceEqual([
    $"scalar System.Int32 Fixture::First(System.Int32) -> {helper}",
    $"scalar System.Int32 Fixture::Second(System.Int32) -> {helper}",
    $"x64-avx2 {excluded}"]), "ldlen not shared across methods and profiles: " + string.Join("; ", Reached(length)));
Require(length.GetProperty("sites").EnumerateArray().Select(s => s.GetProperty("method").GetString()).Order(StringComparer.Ordinal)
    .SequenceEqual([helper, excluded]), "ldlen sites not kept per method");
Require(Ids(1).Order(StringComparer.Ordinal).SequenceEqual(new[] { Id(allocation), Id(length) }.Order(StringComparer.Ordinal)) &&
    Ids(1).SequenceEqual(Ids(2)), "Entries do not share the Helper blockers");

// The exact instruction, its offset and the PDB location name the construct.
var site = allocation.GetProperty("sites").EnumerateArray().Single();
var instruction = site.GetProperty("instruction").GetString()!;
Require(site.GetProperty("method").GetString() == helper &&
    instruction == $"IL_{site.GetProperty("ilOffset").GetInt32():x4}: newarr System.Int32" &&
    site.GetProperty("message").GetString() == "Unsupported instruction: " + instruction, "Wrong blocking instruction: " + instruction);
Require(site.GetProperty("source").GetString()!.StartsWith($"Fixture.cs:{LineOf("new int[x]")}:", StringComparison.Ordinal),
    "Wrong source location: " + site.GetProperty("source"));

// The AVX2 branch is folded away under scalar and reported only where the profile makes it live.
Require(Ids(3).Length == 0, "Excluded branch reported under the scalar profile");
var live = Blocker("Unsupported instruction: newarr System.Int64");
var liveSite = live.GetProperty("sites").EnumerateArray().Single();
Require(Ids(4).Order(StringComparer.Ordinal).SequenceEqual(new[] { Id(live), Id(length) }.Order(StringComparer.Ordinal)) &&
    Reached(live).SequenceEqual([$"x64-avx2 {excluded}"]) && liveSite.GetProperty("method").GetString() == excluded &&
    liveSite.GetProperty("source").GetString()!.StartsWith($"Fixture.cs:{LineOf("Avx2.IsSupported")}:", StringComparison.Ordinal),
    "Live AVX2 branch not reported");
Require(entries[5].GetProperty("reason").GetString()!.Contains("No method matches selector"), "Bad signature lacks its reason");
Require(entries[6].GetProperty("reason").GetString()!.Contains("Unknown execution profile"), "Bad profile lacks its reason");
Require(summary.Contains("2 admitted, 3 blocked, 2 not checked") && summary.Contains("nothing here is proved") &&
    !summary.Contains("verified", StringComparison.OrdinalIgnoreCase), "Summary overstates or misses counts");
Console.WriteLine($"PASS {checks} admission report checks");
