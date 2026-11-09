using Mono.Cecil;

namespace Nethermind.LeanCIL;

// The System.Runtime argument guards modeled as checked runtime calls; CIL.Extraction.guardCallMatches
// rechecks each emission against the raw call. The parameter name is an opaque argument.
internal static class ArgumentGuards
{
    private const string OutOfRange = "System.ArgumentOutOfRangeException";
    private const string NullGuard = "System.Void System.ArgumentNullException::ThrowIfNull(System.Object,System.String)";

    private static readonly (string Type, int Width, bool Signed)[] Integers =
    [
        ("System.SByte", 8, true), ("System.Byte", 8, false),
        ("System.Int16", 16, true), ("System.UInt16", 16, false),
        ("System.Int32", 32, true), ("System.UInt32", 32, false),
        ("System.Int64", 64, true), ("System.UInt64", 64, false),
        ("System.IntPtr", 64, true), ("System.UIntPtr", 64, false)
    ];

    private static readonly (string Method, string Guard)[] ZeroGuards =
        [("ThrowIfZero", "zero"), ("ThrowIfNegative", "negative"), ("ThrowIfNegativeOrZero", "negativeOrZero")];

    private static readonly (string Method, string Guard)[] ComparingGuards =
    [
        ("ThrowIfEqual", "equal"), ("ThrowIfNotEqual", "notEqual"), ("ThrowIfGreaterThan", "greaterThan"),
        ("ThrowIfGreaterThanOrEqual", "greaterThanOrEqual"), ("ThrowIfLessThan", "lessThan"),
        ("ThrowIfLessThanOrEqual", "lessThanOrEqual")
    ];

    private static readonly Dictionary<string, string> Operations = Build();

    // Exact generic instances only: another type argument or overload is not a modeled guard.
    internal static string? Translate(string signature) => Operations.GetValueOrDefault(signature);

    // The modeled ThrowIfNull, whose object argument must be a class instance or null on the stack.
    internal static bool IsNullGuard(MethodReference callee) =>
        callee.FullName == NullGuard && callee.DeclaringType.Scope.Name == "System.Runtime";

    private static Dictionary<string, string> Build()
    {
        var operations = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [NullGuard] = ".memory .throwIfNull"
        };
        foreach (var (type, width, signed) in Integers)
        {
            var bits = $"{width} {(signed ? "true" : "false")}";
            foreach (var (method, guard) in ZeroGuards)
                operations.Add($"System.Void {OutOfRange}::{method}<{type}>(!!0,System.String)",
                    $".memory (.zeroGuard .{guard} {bits})");
            foreach (var (method, guard) in ComparingGuards)
                operations.Add($"System.Void {OutOfRange}::{method}<{type}>(!!0,!!0,System.String)",
                    $".memory (.comparisonGuard .{guard} {bits})");
        }
        return operations;
    }
}
