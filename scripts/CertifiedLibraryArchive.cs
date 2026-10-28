using System.Diagnostics;
using System.Formats.Tar;
using System.Security.Cryptography;
using System.Text.RegularExpressions;

/// <summary>Transports the complete certified library without trusting archive paths or embedded digests.</summary>
static class CertifiedLibraryArchive
{
    public const string FileName = "certified-library.tar.zst";

    public static string Digest(string path)
    {
        using var stream = File.OpenRead(path);
        return Convert.ToHexStringLower(SHA256.HashData(stream));
    }

    static void RequireDigest(string path, string expected)
    {
        if (!Regex.IsMatch(expected, "^[0-9a-f]{64}$") || Digest(path) != expected)
            throw new InvalidDataException("Certified library digest mismatch: " + path);
    }

    // Enumerating one directory at a time rejects links before descending through them.
    static IEnumerable<string> Files(string directory)
    {
        if ((File.GetAttributes(directory) & FileAttributes.ReparsePoint) != 0)
            throw new InvalidDataException("Linked library entry: " + directory);
        foreach (var entry in Directory.EnumerateFileSystemEntries(directory))
        {
            var attributes = File.GetAttributes(entry);
            if ((attributes & FileAttributes.ReparsePoint) != 0)
                throw new InvalidDataException("Linked library entry: " + entry);
            if ((attributes & FileAttributes.Directory) != 0)
            {
                foreach (var file in Files(entry)) yield return file;
            }
            else yield return entry;
        }
    }

    static Process Start(string[] arguments, bool input)
    {
        var start = new ProcessStartInfo("zstd")
        {
            UseShellExecute = false, RedirectStandardInput = input,
            RedirectStandardOutput = !input, RedirectStandardError = true, CreateNoWindow = true
        };
        foreach (var argument in arguments) start.ArgumentList.Add(argument);
        return Process.Start(start) ?? throw new InvalidOperationException("Could not start zstd");
    }

    static void Complete(Process process, Task<string> error)
    {
        process.WaitForExit();
        if (process.ExitCode != 0) throw new InvalidDataException("zstd failed: " + error.GetAwaiter().GetResult());
    }

    /// <summary>Streams all files, including hidden files and independent hard-link contents, into one archive.</summary>
    public static string Pack(string source, string archive, string manifestDigest)
    {
        source = Path.GetFullPath(source);
        archive = Path.GetFullPath(archive);
        RequireDigest(Path.Combine(source, "cache-manifest.json"), manifestDigest);
        var relativeArchive = Path.GetRelativePath(source, archive);
        if (File.Exists(archive) || Directory.Exists(archive) || (!Path.IsPathRooted(relativeArchive) &&
            !relativeArchive.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal)))
            throw new InvalidDataException("Archive must be new and outside the library");
        Directory.CreateDirectory(Path.GetDirectoryName(archive)!);
        using var process = Start(["-T2", "-6", "-q", "-o", archive], input: true);
        var error = process.StandardError.ReadToEndAsync();
        try
        {
            using (var writer = new TarWriter(process.StandardInput.BaseStream, TarEntryFormat.Pax, leaveOpen: true))
            foreach (var path in Files(source))
            {
                using var contents = File.OpenRead(path);
                var entry = new PaxTarEntry(TarEntryType.RegularFile, Path.GetRelativePath(source, path).Replace('\\', '/'))
                {
                    DataStream = contents
                };
                if (!OperatingSystem.IsWindows()) entry.Mode = File.GetUnixFileMode(path) & (UnixFileMode)0x1ff;
                writer.WriteEntry(entry);
            }
            process.StandardInput.Close();
            Complete(process, error);
            RequireDigest(Path.Combine(source, "cache-manifest.json"), manifestDigest);
            return Digest(archive);
        }
        catch
        {
            if (!process.HasExited) process.Kill(entireProcessTree: true);
            process.WaitForExit();
            File.Delete(archive);
            throw;
        }
    }

    static string EntryPath(string root, string name)
    {
        if (name.Contains('\\') || name.Contains(':') || name.StartsWith('/') ||
            name.Split('/').Any(part => part == ".."))
            throw new InvalidDataException("Unsafe library archive path: " + name);
        var relative = string.Join(Path.DirectorySeparatorChar,
            name.Split('/').Where(part => part.Length != 0 && part != "."));
        var path = Path.GetFullPath(Path.Combine(root, relative));
        if (path != root && !path.StartsWith(root + Path.DirectorySeparatorChar, StringComparison.Ordinal))
            throw new InvalidDataException("Library archive path escapes destination: " + name);
        return path;
    }

    /// <summary>Authenticates before decompression, then publishes only a complete, path-safe library.</summary>
    public static void Restore(string download, string destination, string manifestDigest, string archiveDigest)
    {
        download = Path.GetFullPath(download);
        destination = Path.TrimEndingDirectorySeparator(Path.GetFullPath(destination));
        if (Directory.Exists(destination) || File.Exists(destination))
            throw new InvalidDataException("Library restore destination already exists");
        var archive = Path.Combine(download, FileName);
        var packed = archiveDigest.Length != 0;
        var elapsed = Stopwatch.StartNew();
        if (packed) RequireDigest(archive, archiveDigest);
        else
        {
            if (File.Exists(archive)) throw new InvalidDataException("Library archive has no trusted digest");
            RequireDigest(Path.Combine(download, "cache-manifest.json"), manifestDigest);
        }
        Console.WriteLine($"Library restore authentication: {elapsed.Elapsed.TotalSeconds:F3}s");
        elapsed.Restart();
        var staging = destination + ".restore-" + Guid.NewGuid().ToString("N");
        Directory.CreateDirectory(staging);
        try
        {
            if (packed)
            {
                using var process = Start(["-d", "-q", "-c", "--", archive], input: false);
                var error = process.StandardError.ReadToEndAsync();
                try
                {
                    using var reader = new TarReader(process.StandardOutput.BaseStream, leaveOpen: true);
                    var seen = new HashSet<string>(OperatingSystem.IsWindows()
                        ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal);
                    while (reader.GetNextEntry() is { } entry)
                    {
                        var path = EntryPath(staging, entry.Name);
                        if (!seen.Add(path)) throw new InvalidDataException("Duplicate library archive entry: " + entry.Name);
                        if (entry.EntryType == TarEntryType.Directory) Directory.CreateDirectory(path);
                        else if (entry.EntryType is TarEntryType.RegularFile or TarEntryType.V7RegularFile)
                        {
                            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                            using (var output = new FileStream(path, FileMode.CreateNew)) entry.DataStream?.CopyTo(output);
                            if (!OperatingSystem.IsWindows()) File.SetUnixFileMode(path, entry.Mode & (UnixFileMode)0x1ff);
                        }
                        else throw new InvalidDataException("Unsupported library archive entry: " + entry.EntryType);
                    }
                    process.StandardOutput.BaseStream.CopyTo(Stream.Null);
                    Complete(process, error);
                }
                finally
                {
                    if (!process.HasExited) process.Kill(entireProcessTree: true);
                    process.WaitForExit();
                }
            }
            else
            {
                foreach (var path in Files(download))
                {
                    var target = EntryPath(staging, Path.GetRelativePath(download, path).Replace('\\', '/'));
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.Copy(path, target);
                }
            }
            Console.WriteLine($"Library restore extraction: {elapsed.Elapsed.TotalSeconds:F3}s");
            elapsed.Restart();
            RequireDigest(Path.Combine(staging, "cache-manifest.json"), manifestDigest);
            Directory.Move(staging, destination);
            Console.WriteLine($"Library restore publication: {elapsed.Elapsed.TotalSeconds:F3}s");
        }
        finally
        {
            if (Directory.Exists(staging)) Directory.Delete(staging, recursive: true);
        }
    }
}
