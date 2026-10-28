using System.Diagnostics;
using System.Text.RegularExpressions;

/// <summary>Runs independent suites sequentially, retaining every failure and each suite's own cache.</summary>
internal static class VerificationGroupRunner
{
    internal static async Task<int> Run(string[] command, string[] suites, string artifacts)
    {
        var invalidSuites = suites.Length == 0 ||
            suites.Distinct(StringComparer.Ordinal).Count() != suites.Length ||
            suites.Any(suite => !Regex.IsMatch(suite, "^[a-z]+$"));
        if (command.Length == 0 || invalidSuites)
            throw new ArgumentException("Expected a command and distinct suite names");
        artifacts = Path.GetFullPath(artifacts);
        Directory.CreateDirectory(artifacts);
        var failed = false;
        foreach (var suite in suites)
        {
            var start = new ProcessStartInfo(command[0])
            {
                UseShellExecute = false, CreateNoWindow = true,
                RedirectStandardOutput = true, RedirectStandardError = true
            };
            foreach (var argument in command.Skip(1).Concat(["--suite", suite])) start.ArgumentList.Add(argument);
            start.Environment["LEANCIL_SUITE"] = suite;
            start.Environment["LEANCIL_CACHE_DIR"] = Path.Combine(artifacts, "suite-caches", suite);
            using var log = new StreamWriter(Path.Combine(artifacts, "verification-" + suite + ".log"));
            var outputLock = new object();
            async Task Copy(StreamReader reader)
            {
                while (await reader.ReadLineAsync() is { } line)
                    lock (outputLock)
                    {
                        Console.WriteLine(line);
                        log.WriteLine(line);
                    }
            }
            Console.WriteLine("Running suite " + suite);
            try
            {
                using var process = Process.Start(start) ??
                    throw new InvalidOperationException("Could not start suite");
                await Task.WhenAll(Copy(process.StandardOutput), Copy(process.StandardError),
                    process.WaitForExitAsync());
                log.WriteLine("Suite exit code: " + process.ExitCode);
                failed |= process.ExitCode != 0;
            }
            catch (System.ComponentModel.Win32Exception error)
            {
                log.WriteLine(error);
                Console.Error.WriteLine(error.Message);
                failed = true;
            }
        }
        return failed ? 1 : 0;
    }
}
