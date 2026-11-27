using System.Runtime.InteropServices;
using System.Text.Json;

// Host configuration when compiled into the shipped `leancil` CLI tool.
partial class Program
{
    static bool IsToolMode => true;

    static string Root { get; } = Path.Combine(AppContext.BaseDirectory, "verification");

    static string ExtractorPath => typeof(Program).Assembly.Location;

    static void CacheProgress(string message) { }

    static string[] PrepareProcessCommand(string[] args, string workingDirectory) => args;

    static void ConfigureChildEnvironment(IDictionary<string, string?> environment) { }

    static IDisposable? AcquireCheckSlot() => null;

    static void AddHarnessCommonInputs(List<(string Name, string Path)> files,
        List<(string Folder, string[] Extensions)> folders, bool libraryOnly) { }

    static bool TryRunExtractorInProcess(string[] command, out Sha256Digest? digest)
    {
        if (command is ["dotnet", var path, .. var arguments] && path == ExtractorPath)
        {
            digest = Nethermind.LeanCIL.Program.RunQuietly(arguments);
            return true;
        }
        digest = null;
        return false;
    }

    static void LogLibraryBuildNotice(string cached, bool fresh) =>
        Console.Error.WriteLine("Building the certified Lean verification library from the framework sources " +
            "and kernel-replaying it; this takes several minutes. " + (fresh
                ? "This run does not cache it."
                : "Later runs reuse it from " + cached + "."));

    static void LogAuditFused(bool? fused, string[] modules) { }

    // A failed download never becomes a cache entry. The package-pinned archive digest is checked
    // before extraction, then the producer manifest and full kernel replay authorize local reuse.
    bool DownloadReleasedLibrary(string cached, string key)
    {
        var descriptor = Path.Combine(Root, $"certified-library-release.{RuntimeInformation.RuntimeIdentifier}.json");
        if (!File.Exists(descriptor)) return false;
        var staging = cached + ".download-" + Guid.NewGuid().ToString("N");
        var archive = staging + ".zip";
        try
        {
            var asset = JsonSerializer.Deserialize<CertifiedReleaseAsset>(File.ReadAllBytes(descriptor));
            if (asset is null || !ValidReleaseAsset(asset, key)) return false;
            Console.Error.WriteLine("Downloading certified Lean verification library");
            using var client = new System.Net.Http.HttpClient { Timeout = TimeSpan.FromMinutes(3) };
            using var timeout = new CancellationTokenSource(TimeSpan.FromMinutes(3));
            var uri = new Uri("https://github.com/NethermindEth/LeanCIL/releases/download/" +
                Uri.EscapeDataString(asset.Tag) + "/" + Uri.EscapeDataString(asset.Archive));
            using var response = client.GetAsync(uri, System.Net.Http.HttpCompletionOption.ResponseHeadersRead,
                    timeout.Token)
                .GetAwaiter().GetResult();
            response.EnsureSuccessStatusCode();
            using (var input = response.Content.ReadAsStream(timeout.Token))
            using (var output = File.Create(archive))
            {
                var buffer = new byte[1024 * 1024];
                int count;
                while ((count = input.ReadAsync(buffer, timeout.Token).AsTask().GetAwaiter().GetResult()) != 0)
                {
                    if (output.Length + count > asset.ArchiveBytes)
                        throw new InvalidDataException("Released archive exceeds its package-pinned size");
                    output.Write(buffer, 0, count);
                }
            }
            InstallReleasedLibrary(archive, staging, cached, asset);
            return true;
        }
        catch (Exception error) when (error is IOException or InvalidDataException or UnauthorizedAccessException or
            JsonException or InvalidOperationException or System.Net.Http.HttpRequestException or
            OperationCanceledException)
        {
            Console.Error.WriteLine("Certified library download unavailable; building from sources. " +
                error.Message);
            return false;
        }
        finally
        {
            try { File.Delete(archive); }
            catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
            try { if (Directory.Exists(staging)) Directory.Delete(staging, true); }
            catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
        }
    }
}
