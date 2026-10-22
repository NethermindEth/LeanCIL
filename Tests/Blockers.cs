#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;
using System.Text.RegularExpressions;

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


// Validation continues past the first construct; each one in Helper is a single blocker shared by both entry points.
const string helper = "System.Int32 Fixture::Helper(System.Int32)";
var shared = blockers.Where(b => b.GetProperty("method").GetString() == helper).ToArray();
Require(shared.Select(b => Regex.Replace(b.GetProperty("instruction").GetString()!, @"\AIL_[0-9a-f]{4}: ", "")).Order(StringComparer.Ordinal)
    .SequenceEqual(["ldlen", "newarr System.Int32"]), $"Expected one deduplicated Helper blocker per construct; found {shared.Length}");
Require(Ids(1).Order(StringComparer.Ordinal).SequenceEqual(shared.Select(b => b.GetProperty("id").GetString()!).Order(StringComparer.Ordinal)) &&
    Ids(1).SequenceEqual(Ids(2)), "Entries do not share the Helper blockers");
foreach (var blocker in shared)
{
    var chains = blocker.GetProperty("entries").EnumerateArray()
        .Select(e => string.Join(" -> ", e.GetProperty("chain").EnumerateArray().Select(m => m.GetString()))).Order(StringComparer.Ordinal).ToArray();
    Require(chains.SequenceEqual([
        $"System.Int32 Fixture::First(System.Int32) -> {helper}",
        $"System.Int32 Fixture::Second(System.Int32) -> {helper}"]), "Wrong call chains: " + string.Join("; ", chains));
}

// The exact instruction, its offset and the PDB location name the construct.
var allocation = shared.Single(b => b.GetProperty("instruction").GetString()!.Contains("newarr"));
var instruction = allocation.GetProperty("instruction").GetString()!;
Require(instruction.StartsWith($"IL_{allocation.GetProperty("ilOffset").GetInt32():x4}: newarr System.Int32", StringComparison.Ordinal) &&
    allocation.GetProperty("message").GetString() == "Unsupported instruction: " + instruction, "Wrong blocking instruction: " + instruction);
Require(allocation.GetProperty("source").GetString()!.StartsWith($"Fixture.cs:{LineOf("new int[x]")}:", StringComparison.Ordinal),
    "Wrong source location: " + allocation.GetProperty("source"));

// The AVX2 branch is folded away under scalar and reported only where the profile makes it live.
Require(Ids(3).Length == 0, "Excluded branch reported under the scalar profile");
var live = blockers.Where(b => Ids(4).Contains(b.GetProperty("id").GetString())).ToArray();
Require(live.Length == 2 && live.All(b => b.GetProperty("method").GetString() == "System.UInt64 Fixture::Excluded(System.UInt64,System.UInt64)" &&
    b.GetProperty("source").GetString()!.StartsWith($"Fixture.cs:{LineOf("Avx2.IsSupported")}:", StringComparison.Ordinal) &&
    b.GetProperty("entries").EnumerateArray().Single().GetProperty("profile").GetString() == "x64-avx2") &&
    live.Any(b => b.GetProperty("instruction").GetString()!.EndsWith("newarr System.Int64", StringComparison.Ordinal)),
    "Live AVX2 branch not reported");
Require(blockers.Length == 4, $"Expected exactly four distinct blockers; found {blockers.Length}");


Require(entries[5].GetProperty("reason").GetString()!.Contains("No method matches selector"), "Bad signature lacks its reason");
Require(entries[6].GetProperty("reason").GetString()!.Contains("Unknown execution profile"), "Bad profile lacks its reason");
Require(summary.Contains("2 admitted, 3 blocked, 2 not checked") && summary.Contains("nothing here is proved") &&
    !summary.Contains("verified", StringComparison.OrdinalIgnoreCase), "Summary overstates or misses counts");
Console.WriteLine($"PASS {checks} admission report checks");
