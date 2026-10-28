#!/usr/bin/env dotnet
#:property PublishAot=false
#:include CertifiedLibraryArchive.cs

using System.Diagnostics;
using System.Formats.Tar;

var root = Path.Combine(Path.GetTempPath(), "leancil-archive-test-" + Guid.NewGuid().ToString("N"));
Directory.CreateDirectory(root);
var source = Path.Combine(root, "source");
var download = Path.Combine(root, "download");
Directory.CreateDirectory(Path.Combine(source, ".lake", "bin"));
Directory.CreateDirectory(download);
File.WriteAllText(Path.Combine(source, "cache-manifest.json"), "{}");
var executable = Path.Combine(source, ".lake", "bin", "audit");
File.WriteAllText(executable, "test executable bytes");
if (!OperatingSystem.IsWindows()) File.SetUnixFileMode(executable, (UnixFileMode)0x1ed);
var manifest = CertifiedLibraryArchive.Digest(Path.Combine(source, "cache-manifest.json"));
var archive = Path.Combine(download, CertifiedLibraryArchive.FileName);
var checks = 0;
void Require(bool condition, string message)
{
    if (!condition) throw new Exception(message);
}
void Reject(string name, Action action, string? diagnostic = null, bool decoding = false)
{
    try { action(); }
    catch (Exception error) when (error is InvalidDataException or IOException)
    {
        Require(diagnostic is null || error.Message.Contains(diagnostic), "Wrong rejection: " + error);
        Require(!decoding || error is EndOfStreamException ||
            (error is InvalidDataException && error.Message.StartsWith("zstd failed:", StringComparison.Ordinal)),
            "Expected decoder failure: " + error);
        Require(!Directory.Exists(Path.Combine(root, "rejected")), "Rejected archive was published");
        checks++;
        Console.WriteLine("PASS " + name);
        return;
    }
    throw new Exception("Invalid archive accepted: " + name);
}
void Run(string executable, params string[] arguments)
{
    var start = new ProcessStartInfo(executable) { UseShellExecute = false };
    foreach (var argument in arguments) start.ArgumentList.Add(argument);
    using var process = Process.Start(start)!;
    process.WaitForExit();
    Require(process.ExitCode == 0, "Failed " + executable);
}
try
{
    if (OperatingSystem.IsLinux()) Run("ln", executable, Path.Combine(source, "hard-link"));
    var digest = CertifiedLibraryArchive.Pack(source, archive, manifest);
    var restored = Path.Combine(root, "restored");
    CertifiedLibraryArchive.Restore(download, restored + Path.DirectorySeparatorChar, manifest, digest);
    foreach (var path in Directory.EnumerateFiles(source, "*", SearchOption.AllDirectories))
    {
        var target = Path.Combine(restored, Path.GetRelativePath(source, path));
        Require(CertifiedLibraryArchive.Digest(path) == CertifiedLibraryArchive.Digest(target), "Changed file bytes");
        Require(new FileInfo(target).LinkTarget is null, "Restored link instead of independent file bytes");
        if (!OperatingSystem.IsWindows())
            Require(File.GetUnixFileMode(path) == File.GetUnixFileMode(target), "Changed executable mode");
    }
    checks++;
    Console.WriteLine("PASS complete payload, hidden files, executable modes and hard-link contents");
    void Restore(string expectedArchive, string? expectedManifest = null) =>
        CertifiedLibraryArchive.Restore(download, Path.Combine(root, "rejected"), expectedManifest ?? manifest,
            expectedArchive);
    Reject("missing archive digest", () => Restore(""));
    Reject("wrong archive digest before decompression", () => Restore(new string('0', 64)), "digest mismatch");
    Reject("wrong embedded manifest", () => Restore(digest, new string('0', 64)), "digest mismatch");
    var bytes = File.ReadAllBytes(archive);
    File.WriteAllBytes(archive, bytes[..(bytes.Length / 2)]);
    Reject("corrupted archive with original digest", () => Restore(digest), "digest mismatch");
    Reject("truncated stream with matching digest", () => Restore(CertifiedLibraryArchive.Digest(archive)), decoding: true);
    File.Delete(archive);
    CertifiedLibraryArchive.Restore(source, Path.Combine(root, "legacy"), manifest, "");
    checks++;
    Console.WriteLine("PASS authenticated legacy raw artifact");
    Reject("raw artifact cannot replace a promised archive", () =>
        CertifiedLibraryArchive.Restore(source, Path.Combine(root, "rejected"), manifest, digest));
    if (OperatingSystem.IsLinux())
    {
        var link = Path.Combine(source, "symlink");
        File.CreateSymbolicLink(link, executable);
        Reject("source symlink", () => CertifiedLibraryArchive.Pack(source, archive, manifest), "Linked library entry");
        File.Delete(link);
    }

    foreach (var (name, type) in new[]
    {
        ("../escape", TarEntryType.RegularFile), ("/escape", TarEntryType.RegularFile),
        ("a\\escape", TarEntryType.RegularFile), ("C:/escape", TarEntryType.RegularFile),
        ("link", TarEntryType.SymbolicLink), ("hard", TarEntryType.HardLink),
        ("pipe", TarEntryType.Fifo), ("device", TarEntryType.CharacterDevice),
        ("duplicate", TarEntryType.RegularFile)
    })
    {
        var tar = Path.Combine(root, "invalid.tar");
        using (var output = File.Create(tar))
        using (var writer = new TarWriter(output))
        {
            using var manifestBytes = File.OpenRead(Path.Combine(source, "cache-manifest.json"));
            writer.WriteEntry(new PaxTarEntry(TarEntryType.RegularFile, "cache-manifest.json")
            {
                DataStream = manifestBytes
            });
            var entry = new PaxTarEntry(type, name);
            if (type is TarEntryType.SymbolicLink or TarEntryType.HardLink) entry.LinkName = "../escape";
            writer.WriteEntry(entry);
            if (name == "duplicate") writer.WriteEntry(new PaxTarEntry(type, name));
        }
        Run("zstd", "-q", "-f", tar, "-o", archive);
        var diagnostic = name == "duplicate" ? "Duplicate library archive entry" :
            type == TarEntryType.RegularFile ? "Unsafe library archive path" : "Unsupported library archive entry";
        Reject("unsafe tar entry " + name, () => Restore(CertifiedLibraryArchive.Digest(archive)), diagnostic);
        Require(!File.Exists(Path.Combine(root, "escape")), "Archive escaped its staging directory");
    }
    Require(!Directory.EnumerateDirectories(root, "*.restore-*").Any(), "Failed staging directory survived");
    Console.WriteLine($"All {checks} library archive checks passed.");
}
finally
{
    Directory.Delete(root, recursive: true);
}
