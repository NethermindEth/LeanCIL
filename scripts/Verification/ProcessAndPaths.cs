using System.Buffers;
using System.Collections.Concurrent;
using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

// Process execution, Lean environment validation, path resolution and hashing.
partial class Program : IDisposable
{
    const string EnforceStyle = "-p:EnforceCodeStyleInBuild=true";
    const string GenerateDocumentation = "-p:GenerateDocumentationFile=true";
    const string RejectUnusedImports = "-p:WarningsAsErrors=IDE0005";

    static string[] FixtureCommand(string script, string[] arguments, bool prepared)
    {
        string[] buildArguments = prepared
            ? ["-c", "Release", "--no-build", EnforceStyle, GenerateDocumentation]
            : ["-c", "Release", EnforceStyle, GenerateDocumentation, RejectUnusedImports];
        return ["dotnet", "run", "--file", script, .. buildArguments, "--", .. arguments];
    }

    // A parent build can be reused only while its sources and complete output still match.
    static string ExtractorBuildIdentity()
    {
        if (!File.Exists(ExtractorPath)) return "";
        var inputs = CommonInputs();
        var files = new List<(string Name, string Path)>();
        foreach (var path in Directory.EnumerateFiles(Root))
            files.Add(("root:" + Path.GetFileName(path), path));
        foreach (var path in Directory.EnumerateFiles(At("Extractor"), "*", SearchOption.AllDirectories))
        {
            var relative = Path.GetRelativePath(Root, path).Replace('\\', '/');
            if (!inputs.ContainsKey(relative) && !relative.Split('/').Any(part => part is "bin" or "obj"))
                files.Add((relative, path));
        }
        foreach (var path in Directory.EnumerateFiles(Path.GetDirectoryName(ExtractorPath)!, "*",
                     SearchOption.AllDirectories))
            files.Add(("output:" + Path.GetRelativePath(Root, path), path));
        foreach (var (name, digest) in HashFiles(files))
            inputs.Add(name, digest);
        return ContentKey(Root + JsonSerializer.Serialize(inputs));
    }

    static bool PreparedExtractorMatches()
    {
        var prepared = Environment.GetEnvironmentVariable(ExtractorBuildEnvironment);
        return !string.IsNullOrEmpty(prepared) && prepared == ExtractorBuildIdentity();
    }

    void EnsureExtractorBuilt()
    {
        if (extractorBuilt) return;
        if (!PreparedExtractorMatches())
            Run(["dotnet", "build", "Extractor", "-c", "Release",
                "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"]);
        extractorBuilt = true;
    }
    int extractionCacheHits;
    int proofCacheHits;
    int supportCacheHits;
    int deepCacheHits;
    SortedDictionary<string, string>? certifiedModules;

    byte[]? receiptKey;
    readonly HashSet<string> preparedSupport = new(StringComparer.Ordinal);
    string? verificationPolicy;
    string VerificationPolicy => verificationPolicy ??= Sha(typeof(Program).Assembly.Location);
    readonly Dictionary<string, SortedDictionary<string, string>> supportSourceKeys = new(StringComparer.Ordinal);

    bool forceFullVerification { get; init; }
    sealed record FullImportResult(string Theorem, string Audit, PublishedImport[] Imports,
        DeploymentDependency[] Dependencies);
    Func<string, string, string, string, FullImportResult>? fullImportAudit { get; set; }
    readonly AsyncLocal<bool> referenceOnlyContext = new();
    bool referenceOnlyAuthoring { get => referenceOnlyContext.Value; set => referenceOnlyContext.Value = value; }
    bool UseSuccessCache => !referenceOnlyAuthoring && !freshProofs && !freshLibrary &&
        !string.Equals(Environment.GetEnvironmentVariable("LEANCIL_DISABLE_SUCCESS_CACHE"), "true", StringComparison.OrdinalIgnoreCase);


    string Toolchain => resolvedToolchain ??= Run(["lean", "--print-prefix"]).Trim();
    SortedDictionary<string, string>? libraryInputs;

    static string At(string path) => Path.Combine(Root, path);

    /// <summary>Links one path may expand through before it is taken for a cycle, the bound POSIX sets.</summary>
    const int MaximumPathLinks = 40;

    /// <summary>
    /// The absolute location `path` names, with every symbolic link and junction among its existing components
    /// followed, the last one included; the components below the deepest existing one follow as spelled. A `..`
    /// names the parent of the location reached so far, as POSIX reads it, so a link before it is followed first.
    /// </summary>
    internal static string ResolvedPath(string path)
    {
        char[] separators = [Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar];
        var full = AbsolutePath(path);
        var resolved = Path.GetPathRoot(full)!;
        // The components still to resolve, the next one on top.
        var pending = new Stack<string>(full[resolved.Length..]
            .Split(separators, StringSplitOptions.RemoveEmptyEntries).Reverse());
        var links = 0;
        while (pending.TryPop(out var component))
        {
            if (component == ".") continue;
            if (component == "..")
            {
                resolved = Path.GetDirectoryName(resolved) ?? resolved;
                continue;
            }
            var next = Path.Join(resolved, component);
            var directory = new DirectoryInfo(next);
            if (directory.Exists && (directory.Attributes & FileAttributes.ReparsePoint) == 0)
            {
                resolved = next;
                continue;
            }
            // A dangling link is still a link: where it points is where a write through it lands.
            if (new FileInfo(next).LinkTarget is { } target)
            {
                if (++links > MaximumPathLinks)
                    throw new InvalidDataException($"Path expands through more than {MaximumPathLinks} links: {path}");
                var targetRoot = Path.GetPathRoot(target);
                if (!string.IsNullOrEmpty(targetRoot))
                    resolved = Path.GetPathRoot(Path.GetFullPath(targetRoot, resolved))!;
                foreach (var part in target[(targetRoot?.Length ?? 0)..]
                    .Split(separators, StringSplitOptions.RemoveEmptyEntries).Reverse())
                    pending.Push(part);
            }
            else if (Directory.Exists(next) || File.Exists(next)) resolved = next;
            else return Path.GetFullPath(Path.Join([next, .. pending]));
        }
        return resolved;
    }

    /// <summary>
    /// `path` made absolute against the working directory with its `.` and `..` components kept, which
    /// Path.GetFullPath would remove before any link is followed.
    /// </summary>
    static string AbsolutePath(string path)
    {
        var absolute = Path.IsPathFullyQualified(path) ? path
            : Path.IsPathRooted(path) ? Path.GetFullPath(path) : Path.Join(Environment.CurrentDirectory, path);
        return Path.DirectorySeparatorChar == '\\' ? absolute.Replace('/', '\\') : absolute;
    }

    /// <summary>
    /// `path` relative to `root` once both are resolved through their links, or null when it lies outside `root`:
    /// two spellings of one location agree, and a link cannot carry a path out of `root` unnoticed. Windows reads
    /// `..` before following links and POSIX after, so a path the two readings place apart is refused.
    /// </summary>
    internal static string? ResolvedRelativePath(string root, string path)
    {
        var relative = RelativeBelow(ResolvedPath(root), ResolvedPath(path));
        if (relative is null || !PathNames(root).Contains("..") && !PathNames(path).Contains("..")) return relative;
        return RelativeBelow(ResolvedPath(Path.GetFullPath(root)), ResolvedPath(Path.GetFullPath(path))) == relative
            ? relative : null;
    }

    /// <summary>
    /// `path` relative to `root`, or null when it lies outside; both are taken as already resolved. Two names
    /// differing only in case are one entry exactly where the directory holding them is known to ignore case.
    /// </summary>
    internal static string? RelativeBelow(string root, string path) => RelativeBelow(root, path, NameCaseIn);

    /// <summary>
    /// `path` relative to `root` (`.` when they are equal), or null when it lies outside; both are full paths
    /// without `.` or `..` components. `nameCaseIn` gives the rule by which a directory matches entry names, and a
    /// name differing only in case where that rule is unknown matches only when `unknownMatches` is set.
    /// </summary>
    internal static string? RelativeBelow(string root, string path, Func<string, NameCase> nameCaseIn,
        bool unknownMatches = false)
    {
        var rootPrefix = Path.GetPathRoot(root) ?? "";
        // Drive letters and server names match ignoring case on every volume.
        if (!string.Equals(rootPrefix, Path.GetPathRoot(path), StringComparison.OrdinalIgnoreCase)) return null;
        var rootNames = PathNames(root[rootPrefix.Length..]);
        var pathNames = PathNames(path[rootPrefix.Length..]);
        if (pathNames.Length < rootNames.Length) return null;
        var directory = rootPrefix;
        for (var index = 0; index < rootNames.Length; index++)
        {
            var (expected, actual) = (rootNames[index], pathNames[index]);
            if (expected != actual)
            {
                if (!string.Equals(expected, actual, StringComparison.OrdinalIgnoreCase)) return null;
                var rule = nameCaseIn(directory);
                if (rule is NameCase.Sensitive || rule is NameCase.Unknown && !unknownMatches) return null;
            }
            directory = Path.Join(directory, expected);
        }
        return pathNames.Length == rootNames.Length ? "."
            : string.Join(Path.DirectorySeparatorChar, pathNames[rootNames.Length..]);
    }

    /// <summary>The names of the directories and file below a path's root, in order.</summary>
    static string[] PathNames(string belowRoot) => belowRoot.Split(
        [Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar], StringSplitOptions.RemoveEmptyEntries);

    /// <summary>
    /// Whether `path` is `root` or lies below it once links in both are followed, matching a name in another case
    /// only where the directory holding it is known to ignore case.
    /// </summary>
    internal static bool Inside(string root, string path) => ResolvedRelativePath(root, path) is not null;

    /// <summary>
    /// Whether two paths name one location once links are followed, matching a name in another case only where the
    /// directory holding it is known to ignore case.
    /// </summary>
    internal static bool SameLocation(string first, string second) => ResolvedRelativePath(first, second) == ".";

    /// <summary>
    /// How a directory matches the names of its entries: telling case apart, ignoring it, or unknown where neither
    /// the operating system nor the directory's entries tell.
    /// </summary>
    internal enum NameCase { Sensitive, Insensitive, Unknown }

    // Answers for directories that existed when asked; an unknown rule is asked again.
    static readonly ConcurrentDictionary<string, NameCase> nameCases = new(StringComparer.Ordinal);

    /// <summary>
    /// The rule by which `directory` matches entry names. A directory that does not exist yet takes the rule of its
    /// nearest existing ancestor, where it would be created; the operating system is asked first, and the
    /// directory's entries are read where it gives no answer.
    /// </summary>
    internal static NameCase NameCaseIn(string directory)
    {
        string? existing = Path.GetFullPath(directory);
        while (existing is not null && !Directory.Exists(existing)) existing = Path.GetDirectoryName(existing);
        if (existing is null) return NameCase.Unknown;
        if (nameCases.TryGetValue(existing, out var known)) return known;
        var rule = QueriedNameCase(existing) ?? EntryNameCase(existing);
        if (rule is not NameCase.Unknown) nameCases.TryAdd(existing, rule);
        return rule;
    }

    /// <summary>
    /// The rule the operating system reports for an existing directory, or null where it reports none that decides
    /// it: the volume's case sensitivity on macOS, the case-sensitive flag of a Windows directory, and the
    /// case-folding flag of a Linux directory.
    /// </summary>
    internal static NameCase? QueriedNameCase(string directory)
    {
        if (OperatingSystem.IsMacOS())
            return pathconf(directory, CaseSensitivePathSetting) switch
            {
                1 => NameCase.Sensitive, 0 => NameCase.Insensitive, _ => null
            };
        if (OperatingSystem.IsWindows())
        {
            using var handle = CreateFileW(Win32Path(directory), ReadAttributesAccess, ShareAll, 0, OpenExisting,
                BackupSemantics, 0);
            // A directory without the flag can still sit on a volume that tells case apart, such as a share.
            return !handle.IsInvalid && GetFileInformationByHandleEx(handle, FileCaseSensitiveInfo, out var flags,
                sizeof(uint)) && (flags & CaseSensitiveDirectoryFlag) != 0 ? NameCase.Sensitive : null;
        }
        if (OperatingSystem.IsLinux())
        {
            var descriptor = open(directory, ReadOnlyCloseOnExec);
            if (descriptor < 0) return null;
            try
            {
                // Without the flag the volume may still ignore case, as a FAT or SMB mount does.
                return ioctl(descriptor, GetFlagsRequest, out var flags) == 0 && (flags & CaseFoldFlag) != 0
                    ? NameCase.Insensitive : null;
            }
            finally { close(descriptor); }
        }
        return null;
    }

    /// <summary>`_PC_CASE_SENSITIVE`: 1 where the volume holding a path tells case apart, 0 where not.</summary>
    const int CaseSensitivePathSetting = 11;
    const uint ReadAttributesAccess = 0x80, ShareAll = 7, OpenExisting = 3, BackupSemantics = 0x02000000;
    /// <summary>`FileCaseSensitiveInfo` and its `FILE_CS_FLAG_CASE_SENSITIVE_DIR` bit.</summary>
    const int FileCaseSensitiveInfo = 23;
    const uint CaseSensitiveDirectoryFlag = 1;
    /// <summary>`O_RDONLY | O_CLOEXEC`, `FS_IOC_GETFLAGS` and its `FS_CASEFOLD_FL` bit on Linux.</summary>
    const int ReadOnlyCloseOnExec = 0x80000, CaseFoldFlag = 0x40000000;
    const nuint GetFlagsRequest = 0x80086601;

    [DllImport("libc", CharSet = CharSet.Ansi, SetLastError = true)]
    static extern nint pathconf(string path, int name);

    [DllImport("kernel32", CharSet = CharSet.Unicode, SetLastError = true)]
    static extern Microsoft.Win32.SafeHandles.SafeFileHandle CreateFileW(string fileName, uint access, uint share,
        nint securityAttributes, uint disposition, uint flags, nint template);

    [DllImport("kernel32", SetLastError = true)]
    static extern bool GetFileInformationByHandleEx(Microsoft.Win32.SafeHandles.SafeFileHandle file,
        int informationClass, out uint information, uint size);

    [DllImport("libc", CharSet = CharSet.Ansi, SetLastError = true)]
    static extern int open(string path, int flags);

    [DllImport("libc", SetLastError = true)]
    static extern int ioctl(int descriptor, nuint request, out int flags);

    [DllImport("libc")]
    static extern int close(int descriptor);

    /// <summary>
    /// The rule shown by the entries of an existing directory: the case-flipped name of an entry finds it only
    /// where case is ignored. Entries whose flipped name is itself listed are passed over, a finding is confirmed
    /// by listing the directory again, and Unknown is returned when no entry decides it.
    /// </summary>
    internal static NameCase EntryNameCase(string directory)
    {
        if (EntryNames(directory) is not { } names) return NameCase.Unknown;
        foreach (var name in names)
        {
            var flipped = FlippedAsciiCase(name);
            if (flipped == name || names.Contains(flipped)) continue;
            var found = File.Exists(Path.Join(directory, flipped)) || Directory.Exists(Path.Join(directory, flipped));
            // The listing must still hold the entry and not its flipped name, or it changed while being read.
            if (EntryNames(directory) is not { } again || !again.Contains(name) || again.Contains(flipped)) continue;
            return found ? NameCase.Insensitive : NameCase.Sensitive;
        }
        return NameCase.Unknown;
    }

    /// <summary>The names of a directory's entries other than links as listed, or null when unreadable.</summary>
    static HashSet<string>? EntryNames(string directory)
    {
        // Links are skipped: whether a flipped name exists must not depend on where a link points.
        try
        {
            return new DirectoryInfo(directory).EnumerateFileSystemInfos()
                .Where(entry => (entry.Attributes & FileAttributes.ReparsePoint) == 0)
                .Select(entry => entry.Name).ToHashSet(StringComparer.Ordinal);
        }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { return null; }
    }

    /// <summary>`name` with each ASCII letter in the other case.</summary>
    static string FlippedAsciiCase(string name) => string.Create(name.Length, name, (flipped, source) =>
    {
        for (var index = 0; index < source.Length; index++)
            flipped[index] = char.IsAsciiLetterLower(source[index]) ? char.ToUpperInvariant(source[index])
                : char.IsAsciiLetterUpper(source[index]) ? char.ToLowerInvariant(source[index]) : source[index];
    });

    /// <summary>
    /// Equality of full paths without `.` or `..` components, matching a name in another case where the directory
    /// holding it ignores case and, when `unknownMatches` is set, where its rule is unknown. Every spelling that
    /// differs only in case has one hash code, so hashed sets and groupings stay exact.
    /// </summary>
    internal sealed class LocationEquality(Func<string, NameCase> nameCaseIn, bool unknownMatches)
        : IEqualityComparer<string>
    {
        public bool Equals(string? first, string? second) => first is null || second is null ? first == second
            : RelativeBelow(first, second, nameCaseIn, unknownMatches) == ".";

        public int GetHashCode(string path)
        {
            var hash = new HashCode();
            hash.Add(Path.GetPathRoot(path) ?? "", StringComparer.OrdinalIgnoreCase);
            foreach (var name in PathNames(path[(Path.GetPathRoot(path) ?? "").Length..]))
                hash.Add(name, StringComparer.OrdinalIgnoreCase);
            return hash.ToHashCode();
        }
    }

    /// <summary>Equality of resolved paths known to name one location, for checks that require it.</summary>
    internal static readonly LocationEquality LocationComparer = new(NameCaseIn, unknownMatches: false);

    /// <summary>
    /// Equality of resolved paths that may name one location, for checks that keep outputs apart: two spellings
    /// differing only in case collide unless the directory holding them is known to tell case apart.
    /// </summary>
    internal static readonly LocationEquality CollidingLocationComparer = new(NameCaseIn, unknownMatches: true);

    /// <summary>Deletes a tree that may hold git objects, which git marks read-only and Windows refuses to delete.</summary>
    static void DeleteTree(string directory)
    {
        EnumerationOptions ownFiles = new() { RecurseSubdirectories = true, AttributesToSkip = FileAttributes.ReparsePoint };
        foreach (var file in Directory.EnumerateFiles(directory, "*", ownFiles))
            File.SetAttributes(file, FileAttributes.Normal);
        Directory.Delete(directory, recursive: true);
    }

    static string Sha(string path)
    {
        const int bufferSize = 64 * 1024;
        using var file = File.OpenHandle(path, FileMode.Open, FileAccess.Read, FileShare.Read);
        var length = RandomAccess.GetLength(file);
        if (length > Array.MaxLength) throw new IOException("The file is too long to read.");
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        var buffer = ArrayPool<byte>.Shared.Rent(bufferSize);
        try
        {
            // A positive initial length bounds the read; premature EOF must fail.
            var offset = 0L;
            while (length == 0 || offset < length)
            {
                var count = length == 0 ? bufferSize : (int)Math.Min(bufferSize, length - offset);
                var read = RandomAccess.Read(file, buffer.AsSpan(0, count), offset);
                if (read == 0)
                {
                    if (length != 0) throw new EndOfStreamException();
                    break;
                }
                hash.AppendData(buffer, 0, read);
                offset += read;
            }
            return Convert.ToHexStringLower(hash.GetHashAndReset());
        }
        finally { ArrayPool<byte>.Shared.Return(buffer); }
    }


    static readonly JsonSerializerOptions Json = new() { WriteIndented = true };

    sealed class ProgressSummary(string label)
    {
        readonly object gate = new();
        string latest = "";
        int pending;

        public void Add(string line, TextWriter writer)
        {
            if (string.IsNullOrWhiteSpace(line)) return;
            lock (gate)
            {
                if (line.StartsWith("PASS ", StringComparison.Ordinal) || line.StartsWith("All ", StringComparison.Ordinal))
                    writer.WriteLine(line);
                else
                {
                    // Lake prints axiom details after its completed-target line.
                    // Keep the target count or proof phase as the summary instead.
                    if (latest.Length == 0 || (!line.StartsWith("info: ", StringComparison.Ordinal) &&
                        !line.Contains("depends on axioms:", StringComparison.Ordinal)))
                        latest = line.Length > 200 ? line[..200] + "…" : line;
                    pending++;
                }
            }
        }

        public void Report()
        {
            lock (gate)
            {
                if (pending == 0) return;
                Console.WriteLine($"PROGRESS {label}: {latest} ({pending} output lines since last update)");
                pending = 0;
            }
        }
    }

    /// <summary>The latest `[done/total]` job count that a Lake build printed, for progress lines.</summary>
    sealed partial class JobCount
    {
        string latest = "";

        public void Add(string line)
        {
            if (LakeJob.Match(line) is { Success: true } job)
                Volatile.Write(ref latest, $": {job.Groups[1].Value} of {job.Groups[2].Value} Lake jobs");
        }

        public override string ToString() => Volatile.Read(ref latest);

        [GeneratedRegex(@"\A(?:\S+ )?\[([0-9]+)/([0-9]+)\] ")]
        private static partial Regex LakeJob { get; }
    }

    static async Task<string> CaptureOutput(StreamReader reader, TextWriter writer, ProgressSummary? summary = null,
        TextWriter? transcript = null, JobCount? jobs = null)
    {
        var captured = new StringBuilder();
        var line = new StringBuilder();
        var buffer = new char[4096];
        int count;
        while ((count = await reader.ReadAsync(buffer)) != 0)
        {
            captured.Append(buffer, 0, count);
            if (transcript is not null)
            {
                await transcript.WriteAsync(buffer.AsMemory(0, count));
                await transcript.FlushAsync();
            }
            if (summary is null)
            {
                await writer.WriteAsync(buffer.AsMemory(0, count));
                await writer.FlushAsync();
            }
            if (summary is null && jobs is null) continue;
            for (var i = 0; i < count; i++)
                if (buffer[i] == '\n')
                {
                    var text = line.ToString().TrimEnd('\r');
                    summary?.Add(text, writer);
                    jobs?.Add(text);
                    line.Clear();
                }
                else line.Append(buffer[i]);
        }
        if (summary is not null && line.Length > 0) summary.Add(line.ToString(), writer);
        return captured.ToString();
    }

    /// <summary>Milliseconds between progress lines of one stage on a terminal.</summary>
    const int InteractiveProgressInterval = 10_000;
    /// <summary>Milliseconds between progress lines when stderr is redirected; a shorter stage prints none.</summary>
    const int RedirectedProgressInterval = 20_000;

    /// <summary>
    /// Stderr without stage progress lines, which a run prints for any stage that outlasts an interval:
    /// what remains is the command's own diagnostics.
    /// </summary>
    internal static string WithoutStageProgress(string stderr) => StageProgressLine.Replace(stderr, "");

    [GeneratedRegex(@"^(?:START|PROGRESS|END) [^\n]*(?:\n|\z)", RegexOptions.Multiline)]
    private static partial Regex StageProgressLine { get; }

    static readonly object TraceGate = new();
    // A reused process id must not append to an earlier process's trace, which a reader treats as old.
    static readonly string TraceFile = $"{Environment.ProcessId}-{Guid.NewGuid():N}.jsonl";

    /// <summary>
    /// Runs `command` and returns its exit code and output. A Lean command that exits 0 after printing an internal
    /// error fails here, unless `internalErrors` is false and the caller attributes them itself.
    /// </summary>
    static (int Code, string Output, string Stdout, string Stderr) Execute(IEnumerable<string> command, string? cwd = null, string? leanPath = null,
        bool streamOutput = false, string? progress = null, IReadOnlyDictionary<string, string>? environment = null,
        bool internalErrors = true)
    {
        var traceStage = progress;
        // Stdout stays the report in tool mode; a redirected stderr names only a stage that outlasts one interval.
        var interactive = IsToolMode && !Console.IsErrorRedirected;
        var announced = interactive && progress is not null;
        if (announced) Console.Error.WriteLine("START " + progress);
        var jobs = IsToolMode && progress is not null ? new JobCount() : null;
        if (IsToolMode)
        {
            progress = null;
            streamOutput = false;
        }
        // Aggregate at the suite boundary; nested build/proof phases feed this summary.
        var summary = streamOutput && progress is not null ? new ProgressSummary(progress) : null;
        streamOutput |= progress is not null;
        var args = command.ToArray();
        args = PrepareProcessCommand(args, cwd ?? Root);
        var start = new ProcessStartInfo(args[0])
        {
            WorkingDirectory = cwd ?? Root,
            UseShellExecute = false,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            StandardOutputEncoding = Encoding.UTF8,
            StandardErrorEncoding = Encoding.UTF8,
            CreateNoWindow = true
        };

        foreach (var arg in args.Skip(1))
            start.ArgumentList.Add(arg);

        if (leanPath is not null)
            start.Environment["LEAN_PATH"] = leanPath;
        ConfigureChildEnvironment(start.Environment);
        foreach (var (name, value) in environment ?? new Dictionary<string, string>())
            start.Environment[name] = value;
        if (ChecksLeanEnvironment(args, leanPath is not null))
            RequireLeanEnvironmentFits(args, start.WorkingDirectory, start.Environment);

        using var slot = AcquireCheckSlot();
        if (progress is not null) Console.WriteLine("START " + progress);
        var startedAtUtc = DateTimeOffset.UtcNow;
        var elapsed = Stopwatch.StartNew();
        using var process = new Process { StartInfo = start };
        try
        {
            if (!process.Start())
                throw new InvalidOperationException("Process did not start");
        }
        catch (System.ComponentModel.Win32Exception exception) when (exception.NativeErrorCode is 2 or 3)
        {
            throw new InvalidOperationException("Required command not found: " + args[0], exception);
        }
        var traceDirectory = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
        var transcript = $"{Environment.ProcessId}-{Guid.NewGuid():N}.log";
        if (!string.IsNullOrWhiteSpace(traceDirectory)) Directory.CreateDirectory(traceDirectory);
        using var traceWriter = string.IsNullOrWhiteSpace(traceDirectory) ? null :
            TextWriter.Synchronized(new StreamWriter(Path.Combine(traceDirectory, transcript), false, Encoding.UTF8));
        var stdout = CaptureOutput(process.StandardOutput, streamOutput ? Console.Out : TextWriter.Null, summary,
            traceWriter, jobs);
        var stderr = CaptureOutput(process.StandardError, streamOutput ? Console.Error : TextWriter.Null, summary,
            traceWriter, jobs);
        if (summary is null)
        {
            if (IsToolMode && traceStage is not null)
                while (!process.WaitForExit(interactive ? InteractiveProgressInterval : RedirectedProgressInterval))
                {
                    Console.Error.WriteLine($"PROGRESS {traceStage}{jobs} ({elapsed.Elapsed.TotalSeconds:F0}s)");
                    announced = true;
                }
            else
                process.WaitForExit();
        }
        else
            while (!process.WaitForExit(10_000)) summary.Report();

        var output = stdout.GetAwaiter().GetResult();
        var error = stderr.GetAwaiter().GetResult();
        if (progress is not null)
            Console.WriteLine($"END {progress} (exit {process.ExitCode}, {elapsed.Elapsed.TotalSeconds:F1}s)");
        if (announced)
            Console.Error.WriteLine($"END {traceStage} (exit {process.ExitCode}, {elapsed.Elapsed.TotalSeconds:F1}s)");
        Trace(traceStage ?? string.Join(" ", args.Take(2)), startedAtUtc, start.WorkingDirectory, elapsed.Elapsed, process.ExitCode, transcript, args);
        if (internalErrors && LeanOutput.RejectedSuccess(args, process.ExitCode, output + error) is { } rejected)
            throw rejected;
        return (process.ExitCode, output + error, output, error);
    }

    static void Trace(string stage, DateTimeOffset startedAtUtc, string cwd, TimeSpan elapsed, int exitCode, string transcript, string[] command)
    {
        var traceDirectory = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
        if (string.IsNullOrWhiteSpace(traceDirectory)) return;
        Directory.CreateDirectory(traceDirectory);
        // Concurrent commands in one process append to the same trace file.
        lock (TraceGate)
            File.AppendAllText(Path.Combine(traceDirectory, TraceFile), JsonSerializer.Serialize(new {
            stage, startedAtUtc, processId = Environment.ProcessId, cwd, durationSeconds = elapsed.TotalSeconds,
            exitCode, transcript, command, suite = Environment.GetEnvironmentVariable("LEANCIL_SUITE")
        }) + "\n");
    }

    static string Run(IEnumerable<string> command, string? cwd = null, string? leanPath = null,
        bool streamOutput = false, string? progress = null, IReadOnlyDictionary<string, string>? environment = null)
    {
        var args = command.ToArray();
        var result = Execute(args, cwd, leanPath, streamOutput, progress, environment);

        if (result.Code != 0)
            throw new InvalidOperationException($"Command failed ({result.Code}): {string.Join(' ', args)}\n{result.Output}");

        return result.Output;
    }

    /// <summary>
    /// Lean on Windows builds a child's environment in one buffer of this many bytes: inherited entries are copied
    /// unchecked, and an override that no longer fits is dropped silently, with every override after it.
    /// </summary>
    const int LeanEnvironmentBuffer = 0x7fff;
    /// <summary>Lowers, never raises, the enforced block size; set on another OS, it enables the check.</summary>
    const string LeanEnvironmentLimitVariable = "LEANCIL_LEAN_ENVIRONMENT_LIMIT";
    const int LargestVariablesShown = 6;
    static readonly System.Collections.Concurrent.ConcurrentDictionary<string, KeyValuePair<string, string>[]?>
        LakeVariables = new(StringComparer.Ordinal);

    /// <summary>One `name=value` entry of an environment block, and whether Lake set it.</summary>
    sealed record EnvironmentEntry(string Name, string Value, bool SetByLake)
    {
        /// <summary>The entry's bytes with its terminator; Lean's executables use the UTF-8 code page.</summary>
        public int Bytes => Encoding.UTF8.GetByteCount(Name) + Encoding.UTF8.GetByteCount(Value) + 2;
    }

    /// <summary>The largest environment block a Lean process can pass on; null where Lean has no limit.</summary>
    static int? LeanEnvironmentLimit()
    {
        int? limit = OperatingSystem.IsWindows() ? LeanEnvironmentBuffer : null;
        var configured = Environment.GetEnvironmentVariable(LeanEnvironmentLimitVariable);
        if (string.IsNullOrEmpty(configured)) return limit;
        if (!int.TryParse(configured, System.Globalization.NumberStyles.None,
                System.Globalization.CultureInfo.InvariantCulture, out var lowered) || lowered <= 0)
            throw new ArgumentException(LeanEnvironmentLimitVariable + " must be a positive number of bytes.");
        return Math.Min(limit ?? lowered, lowered);
    }

    /// <summary>Whether `command` starts Lean processes that may start others with their own environment.</summary>
    static bool ChecksLeanEnvironment(string[] command, bool leanSearchPath) =>
        (leanSearchPath || Path.GetFileNameWithoutExtension(command[0]) == "lake") &&
        LeanEnvironmentLimit() is not null;

    /// <summary>
    /// Fails before `command` starts when the environment its Lean processes would hand their children exceeds the
    /// limit, naming the size and the largest variables, instead of letting Lean drop LEAN_PATH without an error.
    /// </summary>
    static void RequireLeanEnvironmentFits(string[] command, string cwd, IDictionary<string, string?> environment)
    {
        if (LeanEnvironmentLimit() is not { } limit ||
            PredictedLeanChildEnvironment(command, cwd, environment) is not { } entries) return;
        var size = EnvironmentBlockBytes(entries);
        if (size > limit)
            throw new InvalidOperationException(LeanEnvironmentOverflow(command, cwd, entries, size, limit));
    }

    /// <summary>
    /// The block a Lean process started by `command` builds for its own children: for Lake, its inherited
    /// environment after the elan proxy's changes plus the variables Lake sets; for another Lean program, the
    /// environment it is given. Null when the command starts no child with an environment of its own.
    /// </summary>
    static EnvironmentEntry[]? PredictedLeanChildEnvironment(string[] command, string cwd,
        IDictionary<string, string?> environment)
    {
        var inherited = environment.Where(entry => entry.Value is not null)
            .Select(entry => KeyValuePair.Create(entry.Key, entry.Value!)).ToList();
        if (Path.GetFileNameWithoutExtension(command[0]) != "lake") return LeanChildEnvironment(inherited, []);
        var subcommand = command.Skip(1).FirstOrDefault(argument => !argument.StartsWith('-'));
        // Printing its variables and updating dependencies start no Lean process with an environment.
        if (subcommand is null or "update" || subcommand == "env" && command[^1] == "env") return null;
        if (LakeEnvironment(cwd, inherited) is not { } lake) return LeanChildEnvironment(inherited, []);
        ApplyElanProxy(inherited, lake);
        // A build starts Lean with LEAN_PATH alone; the printed value also holds Lake's own library directory.
        return LeanChildEnvironment(inherited,
            subcommand == "build" ? [.. lake.Where(entry => entry.Key == "LEAN_PATH")] : lake);
    }

    /// <summary>
    /// The block Lean builds from `inherited` and `overrides`: the inherited entries whose name no override spells
    /// exactly, since Lean compares names case-sensitively even on Windows, then every override.
    /// </summary>
    static EnvironmentEntry[] LeanChildEnvironment(IEnumerable<KeyValuePair<string, string>> inherited,
        IReadOnlyCollection<KeyValuePair<string, string>> overrides)
    {
        var replaced = overrides.Select(entry => entry.Key).ToHashSet(StringComparer.Ordinal);
        return [.. inherited.Where(entry => !replaced.Contains(entry.Key))
                .Select(entry => new EnvironmentEntry(entry.Key, entry.Value, false)),
            .. overrides.Select(entry => new EnvironmentEntry(entry.Key, entry.Value, true))];
    }

    /// <summary>The block's size in bytes: every entry with its terminator, then the block's own terminator.</summary>
    static int EnvironmentBlockBytes(IEnumerable<EnvironmentEntry> entries) => entries.Sum(entry => entry.Bytes) + 1;

    /// <summary>
    /// The variables Lake sets for Lean in `cwd` under `environment`, as `lake env` prints them, or null when Lake
    /// cannot load the workspace. Lake prints a variable it unsets as empty, so counting it can only overcount.
    /// </summary>
    static KeyValuePair<string, string>[]? LakeEnvironment(string cwd,
        IReadOnlyCollection<KeyValuePair<string, string>> environment)
    {
        var given = environment.ToDictionary(entry => entry.Key, entry => entry.Value);
        // Lake's paths follow the package's libraries and dependencies, so an edited lakefile or manifest re-asks.
        var workspace = new[] { "lakefile.toml", "lakefile.lean", "lake-manifest.json" }
            .Select(name => Path.Combine(cwd, name)).Where(File.Exists).Select(path => path + "=" + Sha(path));
        var key = Path.GetFullPath(cwd) + "\n" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(
            string.Join('\0', given.OrderBy(entry => entry.Key, StringComparer.Ordinal)
                .Select(entry => entry.Key + "=" + entry.Value).Concat(workspace)))));
        return LakeVariables.GetOrAdd(key, _ =>
        {
            var printed = Execute(["lake", "env"], cwd, environment: given);
            // A workspace Lake cannot load fails the command itself, with Lake's own error.
            return printed.Code != 0 ? null : [.. printed.Stdout.Split('\n')
                .Select(line => line.TrimEnd('\r')).Where(line => line.Contains('='))
                .Select(line => KeyValuePair.Create(line[..line.IndexOf('=')], line[(line.IndexOf('=') + 1)..]))];
        });
    }

    /// <summary>
    /// Applies what elan's proxy sets before it starts the toolchain's Lake, when a bare `lake` resolves to it:
    /// elan's and (on Windows) the toolchain's bin directories ahead of PATH, a raised LEAN_RECURSION_COUNT, and
    /// ELAN_TOOLCHAIN and ELAN_HOME, each under the spelling the environment already uses.
    /// </summary>
    static void ApplyElanProxy(List<KeyValuePair<string, string>> inherited,
        IReadOnlyCollection<KeyValuePair<string, string>> lake)
    {
        string Printed(string name) => lake.FirstOrDefault(entry => entry.Key == name).Value ?? "";
        var comparison = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        var elanBin = Printed("ELAN_HOME") is { Length: > 0 } home ? Path.Combine(home, "bin") : null;
        // PATH may reach the elan directory through a link that Lake's ELAN_HOME does not, or the reverse.
        if (elanBin is null || LakeOnPath() is not { } proxy || !SameLocation(Path.GetDirectoryName(proxy)!, elanBin))
            return;
        void Set(string name, Func<string?, string> value)
        {
            var index = inherited.FindIndex(entry => entry.Key.Equals(name, comparison));
            var entry = KeyValuePair.Create(index < 0 ? name : inherited[index].Key,
                value(index < 0 ? null : inherited[index].Value));
            if (index < 0) inherited.Add(entry);
            else inherited[index] = entry;
        }
        string[] prefix = OperatingSystem.IsWindows()
            ? [elanBin, Path.Combine(Printed("LEAN_SYSROOT"), "bin")] : [elanBin];
        Set("PATH", current => string.Join(Path.PathSeparator, current is null ? prefix : [.. prefix, current]));
        Set("LEAN_RECURSION_COUNT", current => ((uint.TryParse(current, System.Globalization.NumberStyles.None,
            System.Globalization.CultureInfo.InvariantCulture, out var count) ? count : 0) + 1)
            .ToString(System.Globalization.CultureInfo.InvariantCulture));
        Set("ELAN_TOOLCHAIN", _ => Printed("ELAN_TOOLCHAIN"));
        Set("ELAN_HOME", _ => Printed("ELAN_HOME"));
    }

    /// <summary>The executable a bare `lake` command starts: the first one on this process's PATH.</summary>
    static string? LakeOnPath() =>
        (Environment.GetEnvironmentVariable("PATH") ?? "")
            .Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
            .Select(directory => Path.Combine(directory.Trim('"'), OperatingSystem.IsWindows() ? "lake.exe" : "lake"))
            .FirstOrDefault(File.Exists);

    static string LeanEnvironmentOverflow(string[] command, string cwd, EnvironmentEntry[] entries, int size,
        int limit)
    {
        var invariant = System.Globalization.CultureInfo.InvariantCulture;
        var largest = entries.OrderByDescending(entry => entry.Bytes).Take(LargestVariablesShown)
            .Select(entry => string.Create(invariant,
                $"\n  {entry.Name} {entry.Bytes:N0}{(entry.SetByLake ? " (set by Lake)" : "")}"));
        var doubled = entries.GroupBy(entry => entry.Name, StringComparer.OrdinalIgnoreCase)
            .Where(group => group.Count() > 1).Select(group => string.Join(" and ", group.Select(entry => entry.Name)))
            .Select(names => "\n" + names + " are both passed: Lean keeps an inherited spelling beside Lake's.");
        return string.Create(invariant, $"`{string.Join(' ', command.Take(2))}` in {cwd} would start Lean ") +
            string.Create(invariant, $"processes that pass on a {size:N0}-byte environment, over the ") +
            string.Create(invariant, $"{limit:N0}-byte limit ") +
            "of the environment Lean on Windows can pass to a process. Lean would drop LEAN_PATH and the other " +
            "variables set for it without an error, so imports would not resolve.\n" +
            "Largest variables (bytes of name=value):" +
            string.Concat(largest) + string.Concat(doubled) +
            "\nRemove unneeded variables or PATH entries from the environment leancil runs in.";
    }

}
