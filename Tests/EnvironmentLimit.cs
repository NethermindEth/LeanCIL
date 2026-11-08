#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Diagnostics;
using System.Globalization;
using System.Runtime.InteropServices;
using System.Text;

// Started by Lake, this program reports the raw block it received, so the test compares prediction with reality.
if (args is ["--environment-block"])
{
    foreach (var entry in ReceivedEnvironment())
        Console.WriteLine(Encoding.UTF8.GetByteCount(entry) + 1 + "\t" + entry[..entry.IndexOf('=', 1)]);
    return;
}

const string PaddingVariable = "LEANCIL_ENVIRONMENT_PADDING";
var invariant = CultureInfo.InvariantCulture;
var package = At("artifacts/EnvironmentLimit-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(package);
File.WriteAllText(Path.Combine(package, "lakefile.toml"), "name = \"envprobe\"\n[[lean_lib]]\nname = \"Probe\"\n");
File.WriteAllText(Path.Combine(package, "Probe.lean"), "def probe : Nat := 1\n");
File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
var olean = Path.Combine(package, ".lake", "build", "lib", "lean", "Probe.olean");
try
{
    Console.WriteLine("Counting an environment block as Lean builds it");
    // Lean matches override names case-sensitively, so Lake's PATH sits beside an inherited Path and both count;
    // sizes are UTF-8 bytes, so a three-byte character costs three.
    var counted = LeanChildEnvironment(
        [KeyValuePair.Create("Path", "abc"), KeyValuePair.Create("A", "inherited")],
        [KeyValuePair.Create("PATH", "xy"), KeyValuePair.Create("A", "\u4E2D")]);
    if (!counted.Select(entry => entry.Name).SequenceEqual(["Path", "PATH", "A"]) ||
        EnvironmentBlockBytes(counted) != "Path=abc".Length + 1 + "PATH=xy".Length + 1 + "A=".Length + 3 + 1 + 1)
        throw new InvalidOperationException("The environment block is not counted as Lean builds it.");

    Console.WriteLine("Rejecting Lake commands whose Lean environment exceeds a lowered limit");
    Environment.SetEnvironmentVariable(LeanEnvironmentLimitVariable, "1000");
    var buildSize = EnvironmentBlockBytes(
        PredictedLeanChildEnvironment(["lake", "build"], package, new ProcessStartInfo().Environment)!);
    var rejected = Rejection(() => Run(["lake", "build", "Probe"], package));
    // The check runs before Lake starts, so nothing is built.
    if (!rejected.Contains("1,000-byte limit", StringComparison.Ordinal) ||
        !rejected.Contains(buildSize.ToString("N0", invariant) + "-byte environment", StringComparison.Ordinal) ||
        !rejected.Contains("LEAN_PATH", StringComparison.Ordinal) || File.Exists(olean))
        throw new InvalidOperationException("An oversized Lake environment was not rejected before the build:\n" +
            rejected);
    // Printing Lake's variables and other programs start no Lean process with an environment of its own.
    Run(["lake", "env"], package);
    Run(["git", "--version"]);
    Environment.SetEnvironmentVariable(LeanEnvironmentLimitVariable, "0");
    if (!Rejection(() => Run(["lake", "build", "Probe"], package)).Contains(LeanEnvironmentLimitVariable,
            StringComparison.Ordinal))
        throw new InvalidOperationException("A limit that is not a positive byte count was accepted.");
    // The variable only lowers the limit, so a large value builds where Lean's own buffer allows.
    Environment.SetEnvironmentVariable(LeanEnvironmentLimitVariable, int.MaxValue.ToString(invariant));
    if (OperatingSystem.IsWindows() ? LeanEnvironmentLimit() != LeanEnvironmentBuffer
            : LeanEnvironmentLimit() != int.MaxValue)
        throw new InvalidOperationException("The limit variable raised Lean's buffer.");
    Run(["lake", "build", "Probe"], package);
    if (!File.Exists(olean)) throw new InvalidOperationException("A fitting Lake environment did not build.");
    Environment.SetEnvironmentVariable(LeanEnvironmentLimitVariable, null);

    Console.WriteLine("Asking Lake again after the package declares another library");
    // Each library adds its source directory to LEAN_SRC_PATH; a stale answer would undercount the block.
    int ServeBytes() => EnvironmentBlockBytes(
        PredictedLeanChildEnvironment(["lake", "serve"], package, new ProcessStartInfo().Environment)!);
    var before = ServeBytes();
    File.AppendAllText(Path.Combine(package, "lakefile.toml"), "[[lean_lib]]\nname = \"Second\"\n");
    if (ServeBytes() <= before)
        throw new InvalidOperationException("A changed lakefile reused Lake's earlier variables.");

    if (OperatingSystem.IsWindows())
        CheckWindowsBoundary();
    else Console.WriteLine("Lean's environment buffer exists only on Windows; skipping the boundary checks");
}
finally
{
    Environment.SetEnvironmentVariable(LeanEnvironmentLimitVariable, null);
    Directory.Delete(package, true);
}

void CheckWindowsBoundary()
{
    string[] probe = Path.GetFileNameWithoutExtension(Environment.ProcessPath) == "dotnet"
        ? [Environment.ProcessPath!, typeof(Program).Assembly.Location, "--environment-block"]
        : [Environment.ProcessPath!, "--environment-block"];
    string[] command = ["lake", "env", .. probe];

    Console.WriteLine("Predicting the block Lake hands Lean, byte for byte");
    var predicted = Predicted(0);
    var initial = Received(0);
    // Lake prints a variable it unsets as empty; counting it is the prediction's only allowed excess.
    var unset = predicted.Where(entry => entry.SetByLake && entry.Value.Length == 0 &&
        !initial.Names.Contains(entry.Name, StringComparer.Ordinal)).ToArray();
    var expected = predicted.Except(unset).Select(entry => entry.Name).Order(StringComparer.Ordinal);
    if (!expected.SequenceEqual(initial.Names.Order(StringComparer.Ordinal), StringComparer.Ordinal) ||
        EnvironmentBlockBytes(predicted) - unset.Sum(entry => entry.Bytes) != initial.Bytes)
        throw new InvalidOperationException($"Predicted {EnvironmentBlockBytes(predicted)} bytes less " +
            $"{unset.Sum(entry => entry.Bytes)} unset, but Lean passed {initial.Bytes}:\n" +
            string.Join(", ", initial.Names.Order(StringComparer.Ordinal)));
    var lakeNames = predicted.Except(unset).Where(entry => entry.SetByLake).Select(entry => entry.Name).ToArray();

    Console.WriteLine("Finding Lean's limit at exactly 32,767 bytes");
    var fitting = LeanEnvironmentBuffer - initial.Bytes;
    var full = Received(fitting);
    var over = Received(fitting + 1);
    if (full.Bytes != LeanEnvironmentBuffer || !lakeNames.All(name => full.Names.Contains(name)) ||
        lakeNames.Count(name => over.Names.Contains(name)) != lakeNames.Length - 1)
        throw new InvalidOperationException("Lean's limit is not exactly " + LeanEnvironmentBuffer + " bytes.");
    var overflow = Rejection(() => Execute(command, package,
        environment: new Dictionary<string, string> { [PaddingVariable] = new('x', fitting + 1) }));
    if (!overflow.Contains("32,767-byte limit", StringComparison.Ordinal))
        throw new InvalidOperationException("A block one byte over Lean's limit was not rejected:\n" + overflow);

    Console.WriteLine("Showing LEAN_PATH vanish without the check, and the check's report instead");
    // Inherited bytes that leave no room for LEAN_PATH drop it whatever Lean's override order, yet still fit.
    var leanPath = predicted.Single(entry => entry.SetByLake && entry.Name == "LEAN_PATH").Bytes;
    var inherited = initial.Bytes - 1 - predicted.Where(entry => entry.SetByLake)
        .Except(unset).Sum(entry => entry.Bytes);
    var crowded = LeanEnvironmentBuffer - leanPath - inherited;
    if (Received(crowded).Names.Contains("LEAN_PATH"))
        throw new InvalidOperationException("Lean passed LEAN_PATH beyond its environment buffer.");
    var crowdedBlock = Predicted(crowded);
    var report = Rejection(() => Execute(command, package,
        environment: new Dictionary<string, string> { [PaddingVariable] = new('x', crowded) }));
    var largest = crowdedBlock.MaxBy(entry => entry.Bytes)!;
    var doubled = crowdedBlock.GroupBy(entry => entry.Name, StringComparer.OrdinalIgnoreCase)
        .Any(group => group.Count() > 1);
    if (!report.Contains(EnvironmentBlockBytes(crowdedBlock).ToString("N0", invariant) + "-byte environment",
            StringComparison.Ordinal) || !report.Contains("drop LEAN_PATH", StringComparison.Ordinal) ||
        !report.Contains("\n  " + largest.Name + " " + largest.Bytes.ToString("N0", invariant),
            StringComparison.Ordinal) ||
        doubled != report.Contains("are both passed", StringComparison.Ordinal))
        throw new InvalidOperationException("The report does not name the size and largest variables:\n" + report);

    EnvironmentEntry[] Predicted(int padding)
    {
        var environment = new ProcessStartInfo().Environment;
        environment[PaddingVariable] = new string('x', padding);
        return PredictedLeanChildEnvironment(command, package, environment)!;
    }

    // Starts Lake directly, without the check, to observe what Lean really passes on.
    (int Bytes, string[] Names) Received(int padding)
    {
        var start = new ProcessStartInfo("lake")
        {
            WorkingDirectory = package, UseShellExecute = false,
            RedirectStandardOutput = true, RedirectStandardError = true
        };
        foreach (var argument in command.Skip(1)) start.ArgumentList.Add(argument);
        start.Environment[PaddingVariable] = new string('x', padding);
        using var process = Process.Start(start)!;
        var errors = process.StandardError.ReadToEndAsync();
        var lines = process.StandardOutput.ReadToEnd().Split('\n',
            StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
        process.WaitForExit();
        if (process.ExitCode != 0)
            throw new InvalidOperationException("The environment probe failed: " + errors.GetAwaiter().GetResult());
        var entries = lines.Select(line => line.Split('\t', 2)).ToArray();
        return (entries.Sum(entry => int.Parse(entry[0], invariant)) + 1, [.. entries.Select(entry => entry[1])]);
    }
}

static string Rejection(Action action)
{
    try { action(); }
    catch (Exception error) when (error is InvalidOperationException or ArgumentException) { return error.Message; }
    throw new InvalidOperationException("The command was not rejected.");
}

partial class Program
{
    [DllImport("kernel32")]
    static extern nint GetEnvironmentStringsW();

    [DllImport("kernel32")]
    static extern bool FreeEnvironmentStringsW(nint block);

    /// <summary>This process's environment entries as Windows holds them, hidden and repeated names kept.</summary>
    static string[] ReceivedEnvironment()
    {
        var block = GetEnvironmentStringsW();
        try
        {
            var entries = new List<string>();
            for (var offset = 0; Marshal.ReadInt16(block, offset) != 0;)
            {
                var entry = Marshal.PtrToStringUni(block + offset)!;
                entries.Add(entry);
                offset += (entry.Length + 1) * sizeof(char);
            }
            return [.. entries];
        }
        finally { FreeEnvironmentStringsW(block); }
    }
}
