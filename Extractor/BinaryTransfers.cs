using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Exact fixed-width overloads share checked transfers and the scalar byte-reversal model.
internal static class BinaryTransfers
{
    private static readonly Dictionary<string, string> Operations = BuildOperations();

    internal static string? Translate(MethodReference reference)
    {
        if (reference.DeclaringType.FullName != "System.Buffers.Binary.BinaryPrimitives" ||
            !RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Memory") ||
            reference.HasThis || reference.ExplicitThis || reference.HasGenericParameters ||
            reference is GenericInstanceMethod || reference.CallingConvention != MethodCallingConvention.Default)
            return null;
        return Operations.GetValueOrDefault(reference.FullName);
    }

    private static Dictionary<string, string> BuildOperations()
    {
        var operations = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var (type, width, signed) in new[]
        {
            ("Int16", 2, true), ("UInt16", 2, false), ("Int32", 4, true), ("UInt32", 4, false),
            ("Int64", 8, true), ("UInt64", 8, false)
        })
        foreach (var bigEndian in new[] { false, true })
        foreach (var read in new[] { false, true })
        foreach (var trying in new[] { false, true })
        {
            var name = (trying ? "Try" : "") + (read ? "Read" : "Write") + type +
                (bigEndian ? "BigEndian" : "LittleEndian");
            var result = trying ? "System.Boolean" : read ? "System." + type : "System.Void";
            var span = (read ? "System.ReadOnlySpan`1" : "System.Span`1") + "<System.Byte>";
            var parameters = span + (read && !trying ? "" : ",System." + type + (read ? "&" : ""));
            var operation = read
                ? $".binaryRead {width} {signed.ToString().ToLowerInvariant()}"
                : $".binaryWrite {width}";
            operations.Add($"{result} System.Buffers.Binary.BinaryPrimitives::{name}({parameters})",
                $".memory ({operation} {bigEndian.ToString().ToLowerInvariant()} " +
                $"{trying.ToString().ToLowerInvariant()})");
        }
        return operations;
    }
}
