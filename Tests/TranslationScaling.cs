#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include GeneratedEvidence.cs

using System.Text.Json;

// Real compiled C# call graph: each method fits the ordinary budget, while one monolithic elaborator `decide`
// over the whole certificate is refused at once, since only the kernel may evaluate the body and metadata check.
var directory = At("artifacts/TranslationScaling");
var source = Path.Combine(directory, "Assembly");
Directory.CreateDirectory(source);
File.WriteAllText(Path.Combine(source, "Scaling.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
""");
var methods = Enumerable.Range(0, 6).Select(index =>
    $"public static ulong M{index}(ulong x) {{ " +
    string.Join(" ", Enumerable.Range(1, 48).Select(value => $"x = (x + {value}UL) ^ {value + index}UL;")) +
    (index == 0 ? " return M1(x) + M2(x) + M3(x) + M4(x) + M5(x); }" : " return x; }"));
File.WriteAllText(Path.Combine(source, "Scaling.cs"), "public static class Scaling { " + string.Join('\n', methods) + " }");
Run(["dotnet", "build", Path.Combine(source, "Scaling.csproj"), "-c", "Release"]);
var assembly = Path.Combine(source, "bin/Scaling.dll");
var output = Path.Combine(directory, "Extraction");
Run(Extract("extract", assembly, "Scaling", "Scaling::M0(ulong)", output));
var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
if (!extracted.Contains("method5_evidence_validated") || extracted.Contains("set_option maxHeartbeats"))
    throw new InvalidOperationException("Expected six independently checked methods at the default heartbeat budget.");
var start = extracted.IndexOf("theorem translation_valid :", StringComparison.Ordinal);
var end = extracted.IndexOf("@[cil_code] theorem lookup0", start, StringComparison.Ordinal);
var monolithicSource = extracted[..start] +
    "theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts " +
    "methodEvidence imports program := by decide\n" + extracted[end..];
void RequireElaboratorRefusal(int code, string diagnostic)
{
    var errors = diagnostic.Split('\n').Where(line => line.Contains(": error:", StringComparison.Ordinal)).ToArray();
    if (code == 0 || errors.Length != 1 ||
        !errors[0].Contains("failed to reduce", StringComparison.Ordinal))
        throw new InvalidOperationException(
            "Fixture no longer demonstrates the elaborator refusing the monolithic certificate: " + diagnostic);
}
if (args.Contains("--measure", StringComparer.Ordinal))
{
    var trace = Path.Combine(directory, "Trace-" + Guid.NewGuid().ToString("N"));
    Environment.SetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY", trace);
    Console.WriteLine("Fixed-workload prefix measurements: " + trace);
    Run(["lake", "env", "lean", Path.Combine(output, "Extracted.lean")], cwd: FixturePackage(),
        progress: "Baseline complete compositional extraction");
    var original = Path.Combine(directory, "FullMonolithic.lean");
    File.WriteAllText(original, monolithicSource);
    var result = Execute(["lake", "env", "lean", original], cwd: FixturePackage(), progress: "Baseline complete monolithic refusal");
    RequireElaboratorRefusal(result.Code, result.Output);
}
var old = Path.Combine(directory, "Monolithic.lean");
// The monolithic decision uses the raw definitions, not the already-proved component lemmas.
// The production consumer below checks the complete unchanged positive certificate once.
File.WriteAllText(old, NarrowEvidence(monolithicSource, "translation_valid"));
var monolithic = Execute(["lake", "env", "lean", old], cwd: FixturePackage(),
    progress: "Checking monolithic certificate refusal");
RequireElaboratorRefusal(monolithic.Code, monolithic.Output);
Console.WriteLine("PASS six-method compiled fixture: the elaborator refuses the monolithic certificate");

// The kernel decides the monolithic certificate. Its time and the memory it adds to the import floor, per method of the
// call graph, may not grow with the number of methods: superlinear growth would make the check unusable on large
// extractions even though only the kernel may run it.
const double AllowedKernelGrowth = 1.5;
(double Seconds, double Gigabytes) KernelCost(int methodCount)
{
    var work = Path.Combine(directory, "Kernel" + methodCount);
    var kernelSource = Path.Combine(work, "Assembly");
    Directory.CreateDirectory(kernelSource);
    File.WriteAllText(Path.Combine(kernelSource, "Scaling.csproj"), File.ReadAllText(Path.Combine(source,
        "Scaling.csproj")));
    var kernelMethods = Enumerable.Range(0, methodCount).Select(index =>
        $"public static ulong M{index}(ulong x) {{ " +
        string.Join(" ", Enumerable.Range(1, 48).Select(value => $"x = (x + {value}UL) ^ {value + index}UL;")) +
        (index == 0 ? " return " + string.Join(" + ", Enumerable.Range(1,
            methodCount - 1).Select(call => $"M{call}(x)")) + "; }"
            : " return x; }"));
    File.WriteAllText(Path.Combine(kernelSource, "Scaling.cs"), "public static class Scaling { " + string.Join('\n',
        kernelMethods) + " }");
    Run(["dotnet", "build", Path.Combine(kernelSource, "Scaling.csproj"), "-c", "Release"]);
    var extraction = Path.Combine(work, "Extraction");
    Run(Extract("extract", Path.Combine(kernelSource, "bin/Scaling.dll"), "Scaling", "Scaling::M0(ulong)", extraction));
    var full = File.ReadAllText(Path.Combine(extraction, "Extracted.lean"));
    var from = full.IndexOf("theorem translation_valid :", StringComparison.Ordinal);
    var to = full.IndexOf("@[cil_code] theorem lookup0", from, StringComparison.Ordinal);
    var kernelFile = Path.Combine(work, "Monolithic.lean");
    File.WriteAllText(kernelFile, NarrowEvidence(full[..from] +
        "theorem translation_valid : Extraction.TranslationValid rawLayouts computedLayouts " +
        "methodEvidence imports program := by decide +kernel\n" + full[to..], "translation_valid"));
    var start = System.Diagnostics.Stopwatch.StartNew();
    var peak = MeasurePeakGigabytes(["lake", "env", "lean", kernelFile], FixturePackage());
    return (start.Elapsed.TotalSeconds, peak);
}
var floorMemory = MeasurePeakGigabytes(["lake", "env", "lean", Path.Combine(directory, "Imports.lean")],
    FixturePackage(),
    "import CIL.Extraction.Translation\n");
int[] workloads = [2, 4, 8];
var costs = workloads.Select(count => (Count: count, Cost: KernelCost(count))).ToArray();
foreach (var (count, cost) in costs)
    Console.WriteLine(FormattableString.Invariant(
        $"kernel decide of the {count}-method certificate: {cost.Seconds:F1} s, peak {cost.Gigabytes:F2} GB (import floor {floorMemory:F2} GB)"));
var (smallCount, small) = costs[0];
var (largeCount, large) = costs[^1];
var timeGrowth = (large.Seconds / largeCount) / (small.Seconds / smallCount);
var memoryGrowth = Math.Max(large.Gigabytes - floorMemory,
    0.05) / largeCount / (Math.Max(small.Gigabytes - floorMemory, 0.05) / smallCount);
if (timeGrowth > AllowedKernelGrowth || memoryGrowth > AllowedKernelGrowth)
    throw new InvalidOperationException(string.Create(System.Globalization.CultureInfo.InvariantCulture,
        $"The kernel check of {largeCount} methods costs {timeGrowth:F2} times the time and {memoryGrowth:F2} times the memory " +
        $"per method of {smallCount}; the limit is {AllowedKernelGrowth}."));
Console.WriteLine(FormattableString.Invariant(
    $"PASS the kernel check grows {timeGrowth:F2} times in time and {memoryGrowth:F2} times in memory per method from {smallCount} to {largeCount} methods"));

// Peak working set of a command's process tree in gigabytes, sampled while it runs.
static double MeasurePeakGigabytes(string[] command, string cwd, string? sourceText = null)
{
    var path = command[^1];
    if (sourceText is not null) File.WriteAllText(path, sourceText);
    var info = new System.Diagnostics.ProcessStartInfo(command[0]) { WorkingDirectory = cwd, UseShellExecute = false,
        RedirectStandardOutput = true, RedirectStandardError = true };
    foreach (var argument in command.Skip(1)) info.ArgumentList.Add(argument);
    using var process = System.Diagnostics.Process.Start(info)!;
    var output = process.StandardOutput.ReadToEndAsync();
    var errors = process.StandardError.ReadToEndAsync();
    long peak = 0;
    while (!process.WaitForExit(200))
    {
        long tree = 0;
        foreach (var id in ProcessTree.Of(process.Id))
            try { tree = Math.Max(tree, System.Diagnostics.Process.GetProcessById(id).WorkingSet64); } catch (ArgumentException) { }
        peak = Math.Max(peak, tree);
    }
    if (process.ExitCode != 0 || output.Result.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException($"{string.Join(' ', command)} failed ({process.ExitCode}):\n{output.Result}\n{errors.Result}");
    return peak / (1024.0 * 1024 * 1024);
}
var consumer = Path.Combine(directory, "Consumer");
Directory.CreateDirectory(consumer);
var revision = Run(["git", "rev-parse", "HEAD"]).Trim();
File.WriteAllText(Path.Combine(consumer, "lakefile.toml"),
    $"name = \"scaling\"\n[[require]]\nname = \"leancil\"\ngit = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}\nrev = \"{revision}\"\n");
File.Copy(At("lean-toolchain"), Path.Combine(consumer, "lean-toolchain"), true);
var proof = Path.Combine(consumer, "Proof.lean");
File.WriteAllText(proof, """
import Extracted
namespace ExampleProof
theorem correctness : CIL.Extraction.TranslationValid Extracted.rawLayouts Extracted.computedLayouts
    Extracted.methodEvidence Extracted.imports Extracted.program := Extracted.translation_valid
#print axioms correctness
end ExampleProof
""");
Run(["lake", "update"], consumer);
Run(["dotnet", ExtractorPath, "verify", output, "--proof", proof, "--proof-root", consumer]);
var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
if (!report.GetProperty("extractionAudit").GetString()!.Contains("Extracted.translation_valid") ||
    !report.GetProperty("theoremAudit").GetString()!.Contains("ExampleProof.correctness"))
    throw new InvalidOperationException("Missing independent certificate/theorem audits.");
Console.WriteLine("PASS fresh consumer proof-root verifies the multi-method certificate with kernel replay and restricted axioms");

// The descendants of a process, from a snapshot of the machine's process list.
static class ProcessTree
{
    [System.Runtime.InteropServices.StructLayout(System.Runtime.InteropServices.LayoutKind.Sequential,
        CharSet = System.Runtime.InteropServices.CharSet.Unicode)]
    struct Entry
    {
        public uint Size, Usage, ProcessId;
        public nint DefaultHeap;
        public uint ModuleId, Threads, ParentProcessId;
        public int PriorityClassBase;
        public uint Flags;
        [System.Runtime.InteropServices.MarshalAs(System.Runtime.InteropServices.UnmanagedType.ByValTStr,
            SizeConst = 260)]
        public string ExeFile;
    }

    [System.Runtime.InteropServices.DllImport("kernel32.dll")] static extern nint CreateToolhelp32Snapshot(uint flags,
        uint process);
    [System.Runtime.InteropServices.DllImport("kernel32.dll", CharSet = System.Runtime.InteropServices.CharSet.Unicode)]
    static extern bool Process32First(nint snapshot, ref Entry entry);
    [System.Runtime.InteropServices.DllImport("kernel32.dll", CharSet = System.Runtime.InteropServices.CharSet.Unicode)]
    static extern bool Process32Next(nint snapshot, ref Entry entry);
    [System.Runtime.InteropServices.DllImport("kernel32.dll")] static extern bool CloseHandle(nint handle);

    internal static IEnumerable<int> Of(int root)
    {
        var parents = new Dictionary<int, List<int>>();
        var snapshot = CreateToolhelp32Snapshot(2, 0);
        var entry = new Entry { Size = (uint)System.Runtime.InteropServices.Marshal.SizeOf<Entry>() };
        for (var more = Process32First(snapshot, ref entry); more; more = Process32Next(snapshot, ref entry))
        {
            if (!parents.TryGetValue((int)entry.ParentProcessId,
                out var children)) parents[(int)entry.ParentProcessId] = children = [];
            children.Add((int)entry.ProcessId);
        }
        CloseHandle(snapshot);
        var found = new List<int> { root };
        for (var index = 0; index < found.Count; index++)
            if (parents.TryGetValue(found[index],
                out var children)) found.AddRange(children.Where(child => !found.Contains(child)));
        return found;
    }
}
