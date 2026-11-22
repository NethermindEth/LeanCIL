using ILOpCode = System.Reflection.Metadata.ILOpCode;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

/// <summary>
/// Instruction information used by extraction and proof outlines.
/// The compiled method's instructions come from Lean's decoder.
/// </summary>
internal abstract record Operation
{
    /// <summary>The operation does nothing: a prefix or an operand the translator folded away.</summary>
    internal bool IsNop => this is StackOperation { Kind: Code.Nop };
}

/// <summary>A site without a separate outline descriptor. Outlines and diagnostics can inspect its CIL instruction.</summary>
internal sealed record Unoutlined : Operation
{
    internal static readonly Unoutlined Site = new();
}

/// <summary>The CIL stack opcode used by the proof outline for this site.</summary>
internal sealed record StackOperation(Code Kind) : Operation
{
    /// <summary>The operation is word addition, subtraction, multiplication or a bitwise combination.</summary>
    internal bool IsArithmetic => Kind is Code.Add or Code.Sub or Code.Mul or
        Code.And or Code.Or or Code.Xor;

    /// <summary>The infix operator that Lean's bit-vector arithmetic writes for an arithmetic operation.</summary>
    internal string Symbol => Kind switch
    {
        Code.Add => "+", Code.Sub => "-", Code.Mul => "*", Code.And => "&&&",
        Code.Or => "|||", Code.Xor => "^^^",
        _ => throw new InvalidOperationException("Not an arithmetic operation: " + Kind)
    };

    internal static readonly StackOperation Nop = new(Code.Nop);
}

/// <summary>The one-byte CIL branch encoding and the destination's instruction index.</summary>
internal sealed record Jump(int Opcode, int Target) : Operation
{
    // ECMA-335 places the short and long branch families in the same order in consecutive ranges.
    private int LongOpcode => Opcode is >= (int)ILOpCode.Br_s and <= (int)ILOpCode.Blt_un_s
        ? Opcode + ((int)ILOpCode.Br - (int)ILOpCode.Br_s) : Opcode;

    internal ILOpCode Kind => (ILOpCode)LongOpcode;
    internal bool Conditional => LongOpcode != (int)ILOpCode.Br;

    /// <summary>The number of evaluation stack operands consumed by this branch.</summary>
    internal int Operands => LongOpcode switch
    {
        (int)ILOpCode.Br => 0,
        (int)ILOpCode.Brfalse or (int)ILOpCode.Brtrue => 1,
        _ => 2
    };

    /// <summary>The Lean constructor name, without its dot.</summary>
    internal string Mnemonic => Name[1..];

    string Name => LongOpcode switch
    {
        (int)ILOpCode.Br => ".br", (int)ILOpCode.Brfalse => ".brfalse", (int)ILOpCode.Brtrue => ".brtrue",
        (int)ILOpCode.Beq => ".beq", (int)ILOpCode.Bne_un => ".bne_un", (int)ILOpCode.Blt => ".blt",
        (int)ILOpCode.Ble => ".ble", (int)ILOpCode.Bgt => ".bgt", (int)ILOpCode.Bge => ".bge",
        (int)ILOpCode.Blt_un => ".blt_un", (int)ILOpCode.Ble_un => ".ble_un",
        (int)ILOpCode.Bgt_un => ".bgt_un", (int)ILOpCode.Bge_un => ".bge_un",
        _ => throw new ArgumentOutOfRangeException(nameof(Opcode))
    };
}

/// <summary>The width and signedness a narrow integer is truncated to when it is read.</summary>
internal enum Narrowing { Signed8, Unsigned8, Signed16, Unsigned16 }

internal static class NarrowingText
{
    /// <summary>The Lean constructor name.</summary>
    internal static string LeanName(this Narrowing narrowing) => narrowing switch
    {
        Narrowing.Signed8 => "signed8", Narrowing.Unsigned8 => "unsigned8",
        Narrowing.Signed16 => "signed16", Narrowing.Unsigned16 => "unsigned16",
        _ => throw new ArgumentOutOfRangeException(nameof(narrowing))
    };
}

/// <summary>An argument pushed from its slot; the method's declared parameter type gives any narrowing.</summary>
internal sealed record Arg(int Index) : Operation;

/// <summary>A local pushed from its slot; the slot's kind gives any narrowing.</summary>
internal sealed record Local(int Index) : Operation;

/// <summary>A local assigned from the stack; the slot's kind gives any narrowing.</summary>
internal sealed record SetLocal(int Index) : Operation;

internal sealed record LocalAddress(int Index) : Operation;

/// <summary>
/// An integer constant of <see cref="Width"/> bits. <see cref="Numeral"/> says it was written as a bare numeral
/// rather than as a bit-vector conversion.
/// </summary>
internal sealed record Constant : Operation
{
    public Constant(int width, long value, bool numeral)
    {
        Width = width;
        Value = value;
        Numeral = numeral;
    }

    public int Width { get; init; }

    /// <summary>The value; a numeral never holds a negative one, whichever of the two is set last.</summary>
    public long Value
    {
        get;
        init => field = !Numeral || value >= 0 ? value : throw NegativeNumeral(nameof(Value));
    }

    /// <summary>Whether the constant is written as a bare numeral; the numeral form has no sign.</summary>
    public bool Numeral
    {
        get;
        init => field = !value || Value >= 0 ? value : throw NegativeNumeral(nameof(Numeral));
    }

    static ArgumentOutOfRangeException NegativeNumeral(string name) =>
        new(name, "A numeral constant is not negative.");
}

internal enum CallKind { Static, Instance, Tail }

/// <summary>A resolved call target and its stack argument count for the proof outline.</summary>
internal sealed record Call(CallKind Kind, int Method, int Arguments) : Operation
{
    /// <summary>The call enters one body with a caller continuation for contract composition.</summary>
    internal bool ReturnsToCaller => Kind is CallKind.Static or CallKind.Instance;
}

internal enum FieldAccess { Load, Store, LoadAggregate, StoreAggregate, Address }

/// <summary>
/// A struct field access at byte <paramref name="Offset"/> of
/// the layout the extraction computed. <paramref name="Width"/> is the field's size and <paramref name="Signed"/>
/// says a load sign-extends; the step takes all three from the checked layouts, so only proof outlines read them.
/// </summary>
internal sealed record StructField(FieldAccess Access, int Offset, int Width, bool Signed) : Operation;

/// <summary>The class layout entry used by a field load or store in a proof outline.</summary>
internal sealed record ClassField(ClassViews.FieldOperation Field) : Operation;

/// <summary>The object opcode and storage shape used by a proof outline.</summary>
internal sealed record ObjectInstruction(Code Opcode, int? ScalarWidth = null,
    bool Signed = false, int? ByteSize = null) : Operation;

/// <summary>
/// The integer element an <c>ldind</c>, <c>stind</c>, <c>ldelem</c> or <c>stelem</c> opcode names; <c>I</c> is
/// native-sized.
/// </summary>
internal enum NumericKind { I1, U1, I2, U2, I4, U4, I8, I }

/// <summary>The width, sign extension and Lean term of a <see cref="NumericKind"/>.</summary>
internal static class NumericKinds
{
    /// <summary>Bytes an access of the kind moves; native int is eight bytes on every admitted profile.</summary>
    internal static int Width(this NumericKind kind) => kind switch
    {
        NumericKind.I1 or NumericKind.U1 => 1,
        NumericKind.I2 or NumericKind.U2 => 2,
        NumericKind.I4 or NumericKind.U4 => 4,
        _ => 8
    };

    /// <summary>A load sign-extends: only the one- and two-byte signed kinds.</summary>
    internal static bool Signed(this NumericKind kind) => kind is NumericKind.I1 or NumericKind.I2;

    /// <summary>The Lean term of the kind, such as <c>.i4</c>.</summary>
    internal static string Term(this NumericKind kind) => "." + kind.ToString().ToLowerInvariant();
}

internal enum ScalarFunction
{
    BigMul32, DivRem, Min, Max, Clamp, Abs, Sign, RotateLeft, RotateRight, PopCount, LeadingZeroCount,
    TrailingZeroCount, Log2, RoundUpToPowerOf2, IsPow2, ReverseEndianness
}

/// <summary>
/// A scalar helper over integers of <paramref name="Width"/> bits. <paramref name="Result"/> is the width of the
/// word a bit count returns.
/// </summary>
internal sealed record ScalarIntrinsic(ScalarFunction Function, int Width, bool Signed, int Result, int Arguments)
    : Operation
{
    /// <summary>The function counts bits, which the instruction semantics treats as pure word arithmetic.</summary>
    internal bool CountsBits => Function is ScalarFunction.PopCount or ScalarFunction.LeadingZeroCount or
        ScalarFunction.TrailingZeroCount or ScalarFunction.Log2;

    // BigMul32 fixes its input width. Only bit counts select a result width.
    // Rotates, unsigned round-up and bit counts ignore signedness.
    (int Width, bool Signed, int Result) OperandTypes =>
        (Function == ScalarFunction.BigMul32 ? 32 : Width,
         Signed && !CountsBits && Function is not (ScalarFunction.RotateLeft or ScalarFunction.RotateRight or
             ScalarFunction.RoundUpToPowerOf2),
         CountsBits ? Result : 0);

    public bool Equals(ScalarIntrinsic? other) =>
        other is not null && Function == other.Function && Arguments == other.Arguments &&
        OperandTypes == other.OperandTypes;

    public override int GetHashCode() => HashCode.Combine(Function, Arguments, OperandTypes);
}
