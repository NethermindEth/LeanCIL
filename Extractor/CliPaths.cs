namespace Nethermind.LeanCIL;

internal static class CliPaths
{
    internal static string Display(string path)
    {
        var fullPath = Path.GetFullPath(path);
        var relative = Path.GetRelativePath(Environment.CurrentDirectory, fullPath);

        return Path.IsPathRooted(relative) || relative == ".." ||
            relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal)
            ? fullPath
            : relative.Replace('\\', '/');
    }
}
