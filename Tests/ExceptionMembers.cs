partial class Program
{
    // The CIL.ExceptionType member of each CLR exception type a differential test can observe.
    static readonly Dictionary<Type, string> ExceptionMembers = new()
    {
        [typeof(Exception)] = "baseException",
        [typeof(SystemException)] = "systemException",
        [typeof(ApplicationException)] = "applicationException",
        [typeof(ArithmeticException)] = "arithmetic",
        [typeof(DivideByZeroException)] = "divideByZero",
        [typeof(OverflowException)] = "overflow",
        [typeof(InvalidOperationException)] = "invalidOperation",
        [typeof(NotSupportedException)] = "notSupported",
        [typeof(NotImplementedException)] = "notImplemented",
        [typeof(ArgumentException)] = "argument",
        [typeof(ArgumentNullException)] = "argumentNull",
        [typeof(ArgumentOutOfRangeException)] = "argumentOutOfRange",
        [typeof(IndexOutOfRangeException)] = "indexOutOfRange",
        [typeof(NullReferenceException)] = "nullReference",
        [typeof(FormatException)] = "format",
        [typeof(InvalidCastException)] = "invalidCast",
        [typeof(ArrayTypeMismatchException)] = "arrayTypeMismatch",
    };

    /// <summary>
    /// The Lean member naming the type of <paramref name="error"/>; a type the model has no member for fails the test.
    /// </summary>
    static string ExceptionMember(Exception error) =>
        ExceptionMembers.TryGetValue(error.GetType(), out var member) ? member
            : throw new InvalidOperationException("No modelled exception type for " + error.GetType().FullName);
}
