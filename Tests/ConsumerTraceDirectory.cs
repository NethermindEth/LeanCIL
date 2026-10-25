internal static class ConsumerTraceDirectory
{
    // Child directories isolate assertions while keeping every trace in the caller's artifact tree.
    internal static string Create(string fallbackRoot, string name)
    {
        var configuredRoot = Environment.GetEnvironmentVariable("LEANCIL_TRACE_DIRECTORY");
        var root = string.IsNullOrWhiteSpace(configuredRoot) ? fallbackRoot : configuredRoot;
        var directory = Path.GetFullPath(Path.Combine(root, name + "-" + Guid.NewGuid().ToString("N")));
        Directory.CreateDirectory(directory);
        return directory;
    }
}
