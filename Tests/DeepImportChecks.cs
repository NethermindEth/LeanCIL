partial class Program
{
    /// <summary>
    /// Fails unless a keyed deep session bound its import closure, and unless every module in it outside the
    /// toolchain is the extraction, StrictBinding or CIL. A contract interface, `ExtractedImports` or proof module
    /// in the closure would mean the deep modules depend on a module this classification does not name.
    /// </summary>
    static void RequireDeepImports(SortedDictionary<string, string>? imports, string path)
    {
        var modules = (imports ?? throw new InvalidOperationException("No deep import closure was keyed: " + path))
            .Keys.Select(ModuleName).ToHashSet(StringComparer.Ordinal);
        static bool Under(string module, string library) =>
            module == library || module.StartsWith(library + ".", StringComparison.Ordinal);
        if (!modules.Contains("Extracted") || !modules.Any(module => Under(module, "StrictBinding")) ||
            !modules.Any(module => Under(module, "CIL")) || modules.Any(module => module != "Extracted" &&
                !Under(module, "StrictBinding") && !Under(module, "CIL")))
            throw new InvalidOperationException("Unexpected deep import closure: " + string.Join(", ", modules));
        Console.WriteLine($"PASS the {path} deep key binds {imports.Count} parts of {modules.Count} imported " +
            $"modules: Extracted, {modules.Count(module => Under(module, "StrictBinding"))} StrictBinding and " +
            $"{modules.Count(module => Under(module, "CIL"))} CIL");
    }

    /// <summary>Changes the last byte of a file and restores its write time, keeping its length.</summary>
    static void SameLengthChange(string path)
    {
        var written = File.GetLastWriteTimeUtc(path);
        var bytes = File.ReadAllBytes(path);
        bytes[^1] ^= 1;
        File.WriteAllBytes(path, bytes);
        File.SetLastWriteTimeUtc(path, written);
    }
}
