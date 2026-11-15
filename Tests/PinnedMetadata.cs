using System.Reflection;
using System.Security.Cryptography;
using Mono.Cecil;

/// <summary>A reflection fixture whose Cecil module and identity rows share one pinned image.</summary>
sealed class PinnedMetadata : IDisposable
{
    readonly IDisposable pinned;

    internal PinnedMetadata(Assembly extractor, string path)
    {
        const BindingFlags flags = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;
        var type = extractor.GetType("Nethermind.LeanCIL.PinnedAssemblies", throwOnError: true)!;
        var source = type.GetNestedType("Source", BindingFlags.Public | BindingFlags.NonPublic)!;
        byte[] bytes = File.ReadAllBytes(path);
        pinned = (IDisposable)Activator.CreateInstance(type, flags, null,
            [bytes, Convert.ToHexStringLower(SHA256.HashData(bytes)), Array.CreateInstance(source, 0), null], null)!;
        Module = (ModuleDefinition)type.GetProperty("Selected", flags)!.GetValue(pinned)!;
    }

    internal ModuleDefinition Module { get; }

    internal object Context => pinned;

    public void Dispose() => pinned.Dispose();
}
