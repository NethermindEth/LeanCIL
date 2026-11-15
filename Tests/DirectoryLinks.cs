partial class Program
{
    /// <summary>
    /// Makes `link` a directory link to `target`, which need not exist: a symbolic link, or on Windows without
    /// that privilege a junction. False when the platform can make neither.
    /// </summary>
    static bool TryLinkDirectory(string link, string target)
    {
        try { Directory.CreateSymbolicLink(link, target); return true; }
        catch (Exception error) when (error is IOException or UnauthorizedAccessException) { }
        if (!OperatingSystem.IsWindows()) return false;
        // A junction needs no privilege.
        using var mklink = System.Diagnostics.Process.Start(new System.Diagnostics.ProcessStartInfo("cmd.exe",
            $"/c mklink /J \"{link}\" \"{target}\"")
        {
            CreateNoWindow = true, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false
        })!;
        mklink.StandardOutput.ReadToEnd();
        mklink.StandardError.ReadToEnd();
        mklink.WaitForExit();
        return mklink.ExitCode == 0 && new DirectoryInfo(link).LinkTarget is not null;
    }
}
