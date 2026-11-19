using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Exact fixed-width overloads share checked transfers and the scalar byte-reversal model.
internal static class BinaryModels
{
    private static readonly Dictionary<string, Operation> Operations = BuildOperations();

    internal static Operation? CallModel(MethodReference reference, string architecture)
    {
        if (reference.DeclaringType.FullName != "System.Buffers.Binary.BinaryPrimitives" ||
            !RuntimeModels.ExactScope(reference.DeclaringType, PlatformAssemblies.SystemMemory) ||
            reference.HasThis || reference.ExplicitThis || reference.HasGenericParameters ||
            reference is GenericInstanceMethod || reference.CallingConvention != MethodCallingConvention.Default)
            return null;
        if (!Operations.TryGetValue(reference.FullName, out var operation)) return null;
        RuntimeModels.ValidateSignature(reference, architecture);
        return operation;
    }

    private static Dictionary<string, Operation> BuildOperations()
    {
        var operations = new Dictionary<string, Operation>(StringComparer.Ordinal);
        foreach (var (type, width, signed) in new[]
        {
            ("Int16", 2, true), ("UInt16", 2, false), ("Int32", 4, true), ("UInt32", 4, false),
            ("Int64", 8, true), ("UInt64", 8, false), ("IntPtr", 8, true), ("UIntPtr", 8, false)
        })
        foreach (var bigEndian in new[] { false, true })
        foreach (var read in new[] { false, true })
        foreach (var trying in new[] { false, true })
        {
            var prefix = trying ? "Try" : "";
            var action = read ? "Read" : "Write";
            var order = bigEndian ? "BigEndian" : "LittleEndian";
            var name = $"{prefix}{action}{type}{order}";
            var result = trying ? "System.Boolean" : read ? $"System.{type}" : "System.Void";
            var span = read ? "System.ReadOnlySpan`1<System.Byte>" : "System.Span`1<System.Byte>";
            var suffix = read ? "&" : "";
            var parameters = read && !trying ? span : $"{span},System.{type}{suffix}";
            var operation = read
                ? $".binaryRead {width} {signed.ToString().ToLowerInvariant()}"
                : $".binaryWrite {width}";
            var orderFlag = bigEndian.ToString().ToLowerInvariant();
            var tryFlag = trying.ToString().ToLowerInvariant();
            operations.Add($"{result} System.Buffers.Binary.BinaryPrimitives::{name}({parameters})",
                MemoryOperation.Other($"({operation} {orderFlag} {tryFlag})"));
        }
        return operations;
    }
}
