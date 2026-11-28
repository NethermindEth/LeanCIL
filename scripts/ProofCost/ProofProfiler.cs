partial class Program
{
    internal sealed record ProofProfiler(string Executable, Dictionary<string, string> Runtime);

    /// <summary>Builds the measurement frontend for the checkout's toolchain in a private directory.</summary>
    internal static ProofProfiler BuildProofProfiler(string directory, string frontend, string checkout)
    {
        var sysroot = Run(["lean", "--print-prefix"], cwd: checkout).Trim();
        var bin = Path.Combine(sysroot, "bin");
        var suffix = OperatingSystem.IsWindows() ? ".exe" : "";
        var lake = Path.Combine(bin, "lake" + suffix);
        var runtime = new Dictionary<string, string>
        {
            ["LEAN_SYSROOT"] = sysroot,
            ["PATH"] = bin + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH")
        };
        Directory.CreateDirectory(directory);
        File.Copy(frontend, Path.Combine(directory, "ProofCost.lean"));
        File.WriteAllText(Path.Combine(directory, "lakefile.toml"), """
            name = "proof_measurement"
            [[lean_exe]]
            name = "proof-profiler"
            root = "ProofCost"
            supportInterpreter = true
            """);
        Run([lake, "build", "proof-profiler"], cwd: directory, environment: runtime);
        // Use Lake's native library paths. The caller selects the Lean modules each sample may import.
        foreach (var line in Run([lake, "env"], cwd: directory, environment: runtime).Split('\n'))
        {
            var setting = line.TrimEnd('\r').Split('=', 2);
            if (setting is ["PATH" or "LD_LIBRARY_PATH" or "DYLD_LIBRARY_PATH", var value])
                runtime[setting[0]] = value;
        }
        return new(Path.Combine(directory, ".lake", "build", "bin", "proof-profiler" + suffix), runtime);
    }
}
