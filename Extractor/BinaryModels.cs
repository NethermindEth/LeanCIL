using Mono.Cecil;

namespace Nethermind.LeanCIL;

// The checked runtime catalog supplies the semantics of each admitted binary primitive.
internal static class BinaryModels
{
    private static readonly HashSet<string> Signatures = BuildSignatures();

    internal static bool CallModel(MethodReference reference, string architecture)
    {
        if (reference.DeclaringType.FullName != "System.Buffers.Binary.BinaryPrimitives" ||
            !RuntimeModels.ExactScope(reference.DeclaringType, PlatformAssemblies.SystemMemory) ||
            reference.HasThis || reference.ExplicitThis || reference.HasGenericParameters ||
            reference is GenericInstanceMethod || reference.CallingConvention != MethodCallingConvention.Default)
            return false;
        if (!Signatures.Contains(reference.FullName)) return false;
        RuntimeModels.ValidateSignature(reference, architecture);
        return true;
    }

    private static HashSet<string> BuildSignatures()
    {
        var signatures = new HashSet<string>(StringComparer.Ordinal);
        foreach (var type in new[] { "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64", "IntPtr", "UIntPtr" })
        foreach (var order in new[] { "BigEndian", "LittleEndian" })
        foreach (var read in new[] { false, true })
        foreach (var trying in new[] { false, true })
        {
            var prefix = trying ? "Try" : "";
            var action = read ? "Read" : "Write";
            var name = $"{prefix}{action}{type}{order}";
            var result = trying ? "System.Boolean" : read ? $"System.{type}" : "System.Void";
            var span = read ? "System.ReadOnlySpan`1<System.Byte>" : "System.Span`1<System.Byte>";
            var suffix = read ? "&" : "";
            var parameters = read && !trying ? span : $"{span},System.{type}{suffix}";
            signatures.Add($"{result} System.Buffers.Binary.BinaryPrimitives::{name}({parameters})");
        }
        return signatures;
    }
}
