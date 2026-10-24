#!/usr/bin/env dotnet
#:property PublishAot=false

using System.Diagnostics;
using System.Globalization;
using System.Runtime.CompilerServices;

const string usage = "Usage: dotnet run --file scripts/BenchmarkViews.cs -- [--stores <1-512>] [--repetitions <1-10>]";
int stores = 64;
int repetitions = 3;
for (int index = 0; index < args.Length; index++)
{
    string option = args[index];
    if (option is "--help" or "-h")
    {
        Console.WriteLine(usage);
        return;
    }
    int maximum = option switch { "--stores" => 512, "--repetitions" => 10, _ => 0 };
    if (maximum == 0 || ++index == args.Length ||
        !int.TryParse(args[index], NumberStyles.None, CultureInfo.InvariantCulture, out int value) ||
        value < 1 || value > maximum)
    {
        Console.Error.WriteLine(usage);
        Environment.ExitCode = 1;
        return;
    }
    if (option == "--stores") stores = value;
    else repetitions = value;
}

static string Source([CallerFilePath] string path = "") => path;
string root = Path.GetDirectoryName(Path.GetDirectoryName(Source()))!;
string artifacts = Path.Combine(root, "artifacts", "ViewBenchmark");
Directory.CreateDirectory(artifacts);
await Run(["build", "Tests.ViewReuse"], "build.log", "Benchmark dependencies failed to build.");
List<string> results = ["variant,iteration,stores,views,milliseconds"];
for (int iteration = 1; iteration <= repetitions; iteration++)
{
    string[] variants = iteration % 2 == 1 ? ["optimized", "legacy"] : ["legacy", "optimized"];
    foreach (string variant in variants)
    {
        string writer = variant == "optimized" ? "write" : "writeAlwaysPrepend";
        int views = variant == "optimized" ? 1 : stores + 1;
        string source = Path.Combine(artifacts, variant + ".lean");
        File.WriteAllText(source, FormattableString.Invariant($"""
            import Tests.ViewReuse
            open CIL.Safety Tests.ViewReuse
            set_option maxRecDepth 32768
            set_option maxHeartbeats 4000000
            theorem benchmark : (stores {writer} {stores} benchmarkMemory).map (·.views.length) = .ok {views} := rfl
            #print axioms benchmark
            """));
        var timer = Stopwatch.StartNew();
        await Run(["env", "lean", source], $"{variant}-{iteration}.log",
            $"Kernel reduction failed: {variant} iteration {iteration}");
        timer.Stop();
        results.Add(FormattableString.Invariant($"{variant},{iteration},{stores},{views},{timer.ElapsedMilliseconds}"));
        Console.WriteLine($"{variant} iteration {iteration}: {timer.ElapsedMilliseconds} ms, {views} views");
    }
}
File.WriteAllLines(Path.Combine(artifacts, "results.csv"), results);

async Task Run(string[] arguments, string log, string failure)
{
    var start = new ProcessStartInfo("lake")
    {
        WorkingDirectory = root,
        UseShellExecute = false,
        RedirectStandardOutput = true,
        RedirectStandardError = true
    };
    foreach (string argument in arguments) start.ArgumentList.Add(argument);
    using var process = Process.Start(start) ?? throw new InvalidOperationException("Could not start lake.");
    Task<string> stdout = process.StandardOutput.ReadToEndAsync();
    Task<string> stderr = process.StandardError.ReadToEndAsync();
    await process.WaitForExitAsync();
    string output = await stdout + await stderr;
    string logPath = Path.Combine(artifacts, log);
    File.WriteAllText(logPath, output);
    if (process.ExitCode != 0 || output.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException($"{failure} See {logPath}");
}
