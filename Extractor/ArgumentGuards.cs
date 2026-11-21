using Mono.Cecil;

namespace Nethermind.LeanCIL;

// The parameter name is an opaque argument to each checked guard.
internal static class ArgumentGuards
{
    private const string OutOfRange = "System.ArgumentOutOfRangeException";
    private const string NullGuard = "System.Void System.ArgumentNullException::ThrowIfNull(System.Object,System.String)";

    private static readonly HashSet<string> Signatures = BuildSignatures();

    // Exact generic instances only: another type argument or overload is not a modeled guard.
    internal static Operation? CallModel(MethodReference reference, string architecture)
    {
        if (!Signatures.Contains(reference.FullName)) return null;
        if (!RuntimeModels.ExactScope(reference.DeclaringType, PlatformAssemblies.SystemRuntime) ||
            reference.HasThis || reference.ExplicitThis) return null;
        var generic = reference is GenericInstanceMethod { GenericArguments.Count: 1 } instance &&
            instance.ElementMethod.GenericParameters.Count == 1;
        var numeric = reference.DeclaringType.FullName == OutOfRange;
        var convention = numeric ? MethodCallingConvention.Generic : MethodCallingConvention.Default;
        if (generic != numeric || reference.CallingConvention != convention) return null;
        RuntimeModels.ValidateSignature(reference, architecture);
        return Unoutlined.Site;
    }

    // The modeled ThrowIfNull, whose object argument must be a class instance or null on the stack.
    internal static bool IsNullGuard(MethodReference callee) =>
        callee.FullName == NullGuard && callee.DeclaringType.Scope.Name == "System.Runtime";

    private static HashSet<string> BuildSignatures()
    {
        var signatures = new HashSet<string>(StringComparer.Ordinal) { NullGuard };
        string[] unaryGuards = ["ThrowIfZero", "ThrowIfNegative", "ThrowIfNegativeOrZero"];
        string[] binaryGuards = ["ThrowIfEqual", "ThrowIfNotEqual", "ThrowIfGreaterThan",
            "ThrowIfGreaterThanOrEqual", "ThrowIfLessThan", "ThrowIfLessThanOrEqual"];
        foreach (var (type, _, _) in RuntimeModels.MathIntegers)
        {
            foreach (var method in unaryGuards)
                signatures.Add($"System.Void {OutOfRange}::{method}<{type}>(!!0,System.String)");
            foreach (var method in binaryGuards)
                signatures.Add($"System.Void {OutOfRange}::{method}<{type}>(!!0,!!0,System.String)");
        }
        return signatures;
    }
}
