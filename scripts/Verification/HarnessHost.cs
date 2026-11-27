using System.Runtime.CompilerServices;
using System.Runtime.ExceptionServices;
using System.Runtime.InteropServices;
using System.Text.Json;
using System.Text.RegularExpressions;

// Host configuration and fixture management for file-based verification scripts.
partial class Program
{
    static bool IsToolMode => false;

    // Settable so a test can stand a few modules in for the framework; the tool's root is fixed.
    static string Root { get; set; } = FixtureRoot() ??
        Path.GetFullPath(Path.Combine(Path.GetDirectoryName(Source())!, "..", ".."));

    // Only relocated binaries need the producer's source path replaced. Source-built children
    // may belong to an isolated corpus and must retain their own Verification location.
    static string? FixtureRoot()
    {
        var root = Environment.GetEnvironmentVariable("LEANCIL_FIXTURE_ROOT");
        var manifest = Environment.GetEnvironmentVariable("LEANCIL_FIXTURE_MANIFEST");
        if (string.IsNullOrEmpty(root) || string.IsNullOrEmpty(manifest)) return null;
        return RunsFromFixtures(manifest) ? Path.GetFullPath(root) : null;
    }

    /// <summary>
    /// Whether this program is a prepared fixture listed in `manifest`, built below the manifest's directory. The
    /// runtime may report the assembly with links followed, so both sides are compared resolved.
    /// </summary>
    static bool RunsFromFixtures(string manifest) =>
        typeof(Program).Assembly.Location is { Length: > 0 } location &&
        ResolvedRelativePath(Path.GetDirectoryName(Path.GetFullPath(manifest))!, location) is not (null or ".");

    static string Source([CallerFilePath] string path = "") => path;

    static string ExtractorPath => At("Extractor/bin/Nethermind.LeanCIL.dll");

    static void CacheProgress(string message) => Console.WriteLine("CACHE " + message);

    static string[] PrepareProcessCommand(string[] args, string workingDirectory) =>
        ReusePreparedFixture(args, workingDirectory);

    static void ConfigureChildEnvironment(IDictionary<string, string?> environment)
    {
        if (!string.IsNullOrEmpty(Environment.GetEnvironmentVariable(FixtureManifestEnvironment)))
            environment["LEANCIL_FIXTURE_ROOT"] = Root;
    }

    static IDisposable? AcquireCheckSlot() => CheckSlot();

    static void AddHarnessCommonInputs(List<(string Name, string Path)> files,
        List<(string Folder, string[] Extensions)> folders, bool libraryOnly)
    {
        if (libraryOnly) return;
        foreach (var name in new[] { "global.json", "Directory.Build.props", "Directory.Packages.props",
            ".editorconfig" })
            files.Add((name, At(name)));
        folders.AddRange([("Examples", [".lean"]), ("Tests", [".lean"]), ("Extractor", [".cs", ".csproj"]),
            ("scripts", [".cs"])]);
    }

    static bool TryRunExtractorInProcess(string[] command, out Sha256Digest? digest)
    {
        digest = null;
        return false;
    }

    static void LogLibraryBuildNotice(string cached, bool fresh) { }

    static void LogAuditFused(bool? fused, string[] modules) =>
        Console.WriteLine(JsonSerializer.Serialize(new { auditFused = fused, modules }));

    bool DownloadReleasedLibrary(string cached, string key) => false;

    const string FixtureManifestEnvironment = "LEANCIL_FIXTURE_MANIFEST";
    const string FixtureDigestEnvironment = "LEANCIL_FIXTURE_MANIFEST_SHA256";
    sealed record PreparedFixture(string Assembly, SortedDictionary<string, string> Inputs,
        SortedDictionary<string, string> Outputs);
    sealed record PreparedFixtures(string Sdk, string Runtime, Dictionary<string, PreparedFixture> Fixtures);
    static string? fixtureSdk;

    static SortedDictionary<string, string>? FixtureInputs(string script)
    {
        var inputs = new SortedDictionary<string, string>(StringComparer.Ordinal);
        var supported = true;
        void Add(string path)
        {
            path = Path.GetFullPath(path);
            // A sibling of the checkout whose name differs only in case is outside it where case is told apart.
            var relative = RelativeBelow(Path.GetFullPath(Root), path)?.Replace('\\', '/') ??
                throw new InvalidOperationException("Fixture input is outside the checkout: " + path);
            if (!inputs.TryAdd(relative, Sha(path))) return;
            if (Path.GetExtension(path) != ".cs") return;
            var source = File.ReadAllText(path);
            // Project references bring in an MSBuild graph not described by file-app includes.
            if (Regex.IsMatch(source, @"(?m)^[\t ]*#:project\b")) supported = false;
            foreach (Match include in Regex.Matches(source, @"(?m)^[\t ]*#:include\s+([^\r\n]+)"))
                Add(Path.Combine(Path.GetDirectoryName(path)!, include.Groups[1].Value.Trim()));
        }
        Add(At(script));
        var root = Path.TrimEndingDirectorySeparator(Root);
        for (var directory = Path.GetDirectoryName(Path.GetFullPath(script, Root)); directory is not null;
             directory = Path.GetDirectoryName(directory))
        {
            foreach (var path in Directory.EnumerateFiles(directory))
                  if (Path.GetExtension(path).ToLowerInvariant() is ".props" or ".targets" ||
                      Path.GetFileName(path).ToLowerInvariant() is "global.json" or "nuget.config" or ".editorconfig")
                    Add(path);
            if (LocationComparer.Equals(directory, root)) break;
        }
        return supported ? inputs : null;
    }

    // The workflow pins this manifest's digest separately from its downloadable artifact.
    static string[]? PreparedFixtureCommand(string script, string[] arguments)
    {
        var manifest = Environment.GetEnvironmentVariable(FixtureManifestEnvironment);
        if (string.IsNullOrEmpty(manifest)) return null;
        if (Sha(manifest) != Environment.GetEnvironmentVariable(FixtureDigestEnvironment))
            throw new InvalidOperationException("Prepared fixture manifest changed");
        var prepared = JsonSerializer.Deserialize<PreparedFixtures>(File.ReadAllText(manifest))!;
        var relative = Path.GetRelativePath(Root, Path.GetFullPath(script, Root)).Replace('\\', '/');
        if (!prepared.Fixtures.TryGetValue(relative, out var fixture)) return null;
        fixtureSdk ??= Run(["dotnet", "--version"]).Trim();
        if (prepared.Runtime != RuntimeInformation.RuntimeIdentifier || prepared.Sdk != fixtureSdk ||
            FixtureInputs(relative) is not { } inputs || !Same(fixture.Inputs, inputs)) return null;
        var directory = Path.GetDirectoryName(manifest)!;
        directory = Path.GetFullPath(directory);
        var assemblyDirectory = Path.GetDirectoryName(Path.GetFullPath(fixture.Assembly, directory))!;
        if (!Directory.Exists(assemblyDirectory) ||
            !fixture.Outputs.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(
                Directory.EnumerateFiles(assemblyDirectory, "*", SearchOption.AllDirectories)
                    .Select(path => Path.GetRelativePath(directory, path).Replace('\\', '/'))))
            throw new InvalidOperationException("Prepared fixture output set changed: " + relative);
        foreach (var (path, hash) in fixture.Outputs)
        {
            var full = Path.GetFullPath(path, directory);
            if (ResolvedRelativePath(directory, full) is null or "." ||
                !File.Exists(full) || Sha(full) != hash)
                throw new InvalidOperationException("Prepared fixture output changed: " + path);
        }
        if (!fixture.Outputs.ContainsKey(fixture.Assembly))
            throw new InvalidOperationException("Prepared fixture assembly is missing from the manifest");
        return ["dotnet", Path.GetFullPath(fixture.Assembly, directory), .. arguments];
    }

    static string[] ReusePreparedFixture(string[] command, string cwd)
    {
        if (command.Length < 4 || command[0] != "dotnet" || command[1] != "run" || command[2] != "--file")
            return command;
        var separator = Array.IndexOf(command, "--", 4);
        var options = command[4..(separator < 0 ? command.Length : separator)];
        // Only the repository's standard Release build options match the producer.
        if (options is not ([] or ["-c", "Release", "--no-build", EnforceStyle, GenerateDocumentation] or
            ["-c", "Release", EnforceStyle, GenerateDocumentation] or
            ["-c", "Release", EnforceStyle, GenerateDocumentation, RejectUnusedImports])) return command;
        var arguments = separator < 0 ? [] : command[(separator + 1)..];
        // Nested fixtures share the parent's Release configuration but still rebuild changed sources.
        return PreparedFixtureCommand(Path.GetFullPath(command[3], cwd), arguments) ??
            (options.Length == 0 ? FixtureCommand(command[3], arguments, prepared: false) : command);
    }

    /// <summary>Memory a child process of a concurrent check reserves unless its check reserves more.</summary>
    const long CheckProcessMemory = 3L << 30;

    /// <summary>The memory the child processes of concurrent checks reserve together, a tenth below the machine's.
    /// </summary>
    static readonly long CheckMemory = GC.GetGCMemoryInfo().TotalAvailableMemoryBytes / 10 * 9;

    /// <summary>Guards the admission state below; a check waiting for a slot waits on it.</summary>
    static readonly object CheckAdmission = new();

    /// <summary>The reservations of the child processes of concurrent checks that run now.</summary>
    static readonly List<long> runningReservations = [];

    /// <summary>The child processes of concurrent checks that wait for a slot, in the order they asked.</summary>
    static readonly List<CheckRequest> waitingRequests = [];

    /// <summary>Whether this thread runs a check that <see cref="Concurrently{TItem, TResult}"/> started.</summary>
    [ThreadStatic] static bool concurrentCheck;

    /// <summary>The memory each child process of this thread's check reserves; 0 reserves the default.</summary>
    [ThreadStatic] static long checkMemory;

    /// <summary>
    /// Runs `check` on every item at once, each on its own thread, and returns the results in item order. Each
    /// thread keeps the caller's reservation; every failure is rethrown together.
    /// </summary>
    static TResult[] Concurrently<TItem, TResult>(IReadOnlyList<TItem> items, Func<TItem, TResult> check)
    {
        var results = new TResult[items.Count];
        var failures = new ExceptionDispatchInfo?[items.Count];
        var memory = checkMemory;
        var threads = items.Select((item, index) => new Thread(() =>
        {
            concurrentCheck = true;
            checkMemory = memory;
            try { results[index] = check(item); }
            catch (Exception error) { failures[index] = ExceptionDispatchInfo.Capture(error); }
        })).ToArray();
        foreach (var thread in threads) thread.Start();
        foreach (var thread in threads) thread.Join();
        var failed = failures.OfType<ExceptionDispatchInfo>().ToArray();
        if (failed.Length == 1) failed[0].Throw();
        if (failed.Length > 1) throw new AggregateException(failed.Select(failure => failure.SourceException));
        return results;
    }

    /// <summary>Runs `check` on every item at once, as <see cref="Concurrently{TItem, TResult}"/> runs it.</summary>
    static void Concurrently<TItem>(IReadOnlyList<TItem> items, Action<TItem> check) => Concurrently(items, item =>
    {
        check(item);
        return true;
    });

    /// <summary>Runs independent checks at once, as <see cref="Concurrently{TItem, TResult}"/> runs them.</summary>
    static void Concurrently(params Action[] checks) => Concurrently(checks, check => check());

    /// <summary>
    /// Precompiles independent file-based test fixtures concurrently, then runs them in parallel under
    /// <see cref="Concurrently{TItem}(IReadOnlyList{TItem}, Action{TItem})"/> memory and processor bounds.
    /// </summary>
    static void RunFixturesConcurrently(IReadOnlyList<(string Script, string Progress)> fixtures)
    {
        var unbuilt = fixtures.Select(fixture => fixture.Script).Distinct(StringComparer.Ordinal)
            .Where(script => PreparedFixtureCommand(script, []) is null).ToArray();
        if (unbuilt.Length > 0)
            ReservingMemory(1L << 30, () => Concurrently(unbuilt, script =>
                Run(["dotnet", "build", script, "-c", "Release", EnforceStyle, GenerateDocumentation],
                    progress: "Building " + script)));
        Concurrently(fixtures, fixture =>
        {
            var output = Run(FixtureCommand(fixture.Script, [], prepared: true), progress: fixture.Progress);
            if (!string.IsNullOrWhiteSpace(output)) Console.WriteLine(output.TrimEnd());
        });
    }

    /// <summary>Runs `check` with each child process it starts reserving `memory` bytes; 0 keeps the default.
    /// </summary>
    static TResult ReservingMemory<TResult>(long memory, Func<TResult> check)
    {
        var outer = checkMemory;
        checkMemory = memory;
        try { return check(); }
        finally { checkMemory = outer; }
    }

    /// <summary>Runs `check` as <see cref="ReservingMemory{TResult}"/> runs it.</summary>
    static void ReservingMemory(long memory, Action check) => ReservingMemory(memory, () =>
    {
        check();
        return true;
    });

    /// <summary>
    /// Admits a child process of a concurrent check once a processor and its reservation are free; null on other
    /// threads. A reservation larger than <see cref="CheckMemory"/> runs alone.
    /// </summary>
    static IDisposable? CheckSlot()
    {
        if (!concurrentCheck) return null;
        var request = new CheckRequest(Math.Min(checkMemory == 0 ? CheckProcessMemory : checkMemory, CheckMemory));
        lock (CheckAdmission)
        {
            waitingRequests.Add(request);
            AdmitRequests();
            while (!request.Admitted) Monitor.Wait(CheckAdmission);
        }
        return new CheckSlotLease(request.Memory);
    }

    /// <summary>
    /// Admits waiting processes, larger reservations first and each size in the order it asked. A process that does
    /// not fit holds back smaller ones unless a running process reserves as much, so draining smaller ones makes room
    /// for it within the longest of their runs.
    /// </summary>
    static void AdmitRequests()
    {
        var reserved = runningReservations.Sum();
        foreach (var request in waitingRequests.OrderByDescending(request => request.Memory).ToList())
        {
            if (runningReservations.Count < Environment.ProcessorCount && reserved + request.Memory <= CheckMemory)
            {
                waitingRequests.Remove(request);
                runningReservations.Add(request.Memory);
                reserved += request.Memory;
                request.Admitted = true;
            }
            else if (runningReservations.Count == 0 || runningReservations.Max() < request.Memory)
                break;
        }
        Monitor.PulseAll(CheckAdmission);
    }

    /// <summary>A child process of a concurrent check that asks for a slot and `Memory` bytes.</summary>
    sealed class CheckRequest(long memory)
    {
        internal long Memory { get; } = memory;
        internal bool Admitted { get; set; }
    }

    /// <summary>Returns its process slot and reservation once, and admits the processes that then fit.</summary>
    sealed class CheckSlotLease(long memory) : IDisposable
    {
        int released;

        public void Dispose()
        {
            if (Interlocked.Exchange(ref released, 1) != 0) return;
            lock (CheckAdmission)
            {
                runningReservations.Remove(memory);
                AdmitRequests();
            }
        }
    }
}
