using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

/// <summary>
/// What the translator decides for one CIL instruction: one sealed case per kind of interpreter operation.
/// Consumers read the typed members; <see cref="ToLean()"/> renders the Lean `CIL.Instruction` term for emission
/// and for diagnostics.
/// </summary>
internal abstract record Operation
{
    /// <summary>The Lean instruction term.</summary>
    internal string ToLean() => Render(LeanText.MethodNumber);

    /// <summary>The Lean instruction term with each callee index written as <paramref name="calleeName"/>.</summary>
    internal string ToLean(Func<int, string> calleeName) => Render(calleeName);

    /// <summary>
    /// The index of every method this operation enters, constructs through, dispatches to or names as a
    /// callable target; empty when it names none.
    /// </summary>
    internal virtual IEnumerable<int> Methods => [];

    /// <summary>The operation does nothing: a prefix or an operand the translator folded away.</summary>
    internal bool IsNop => this is StackOperation { Kind: StackOpcode.Nop };

    /// <summary>This operation with every method index replaced by <paramref name="map"/> of it.</summary>
    internal virtual Operation Renumber(Func<int, int> map) => this;

    /// <summary>
    /// The Lean `Link` term the interpreter follows from this instruction, with each callee written as
    /// <paramref name="calleeName"/> of it; null for an instruction that enters no method.
    /// </summary>
    internal virtual string? Link(Func<int, string> calleeName) => null;

    internal abstract string Render(Func<int, string> calleeName);
}

/// <summary>An instruction that only moves the evaluation stack or does scalar arithmetic.</summary>
internal enum StackOpcode
{
    Nop, Pop, Dup, Add, Sub, Mul, And, Or, Xor, Not, Neg, Shl, Shr, ShrUn, Ceq, Clt, Cgt, CltUn, CgtUn,
    ConvI1, ConvI2, ConvU2, ConvI4, ConvI8, ConvI, ConvU, ConvU1, ConvU4, ConvU8, SkipInit
}

internal sealed record StackOperation(StackOpcode Kind) : Operation
{
    /// <summary>The operation is word addition, subtraction, multiplication or a bitwise combination.</summary>
    internal bool IsArithmetic => Kind is StackOpcode.Add or StackOpcode.Sub or StackOpcode.Mul or
        StackOpcode.And or StackOpcode.Or or StackOpcode.Xor;

    /// <summary>The infix operator that Lean's bit-vector arithmetic writes for an arithmetic operation.</summary>
    internal string Symbol => Kind switch
    {
        StackOpcode.Add => "+", StackOpcode.Sub => "-", StackOpcode.Mul => "*", StackOpcode.And => "&&&",
        StackOpcode.Or => "|||", StackOpcode.Xor => "^^^",
        _ => throw new InvalidOperationException("Not an arithmetic operation: " + Kind)
    };

    internal override string Render(Func<int, string> calleeName) => Kind switch
    {
        StackOpcode.Nop => ".nop",
        StackOpcode.Pop => ".pop",
        StackOpcode.Dup => ".dup",
        StackOpcode.Add => ".add",
        StackOpcode.Sub => ".sub",
        StackOpcode.Mul => ".mul",
        StackOpcode.And => ".and",
        StackOpcode.Or => ".or",
        StackOpcode.Xor => ".xor",
        StackOpcode.Not => ".not",
        StackOpcode.Neg => ".neg",
        StackOpcode.Shl => ".shl",
        StackOpcode.Shr => ".shr",
        StackOpcode.ShrUn => ".shr_un",
        StackOpcode.Ceq => ".ceq",
        StackOpcode.Clt => ".clt",
        StackOpcode.Cgt => ".cgt",
        StackOpcode.CltUn => ".clt_un",
        StackOpcode.CgtUn => ".cgt_un",
        StackOpcode.ConvI1 => ".conv_i1",
        StackOpcode.ConvI2 => ".conv_i2",
        StackOpcode.ConvU2 => ".conv_u2",
        StackOpcode.ConvI4 => ".conv_i4",
        StackOpcode.ConvI8 => ".conv_i8",
        StackOpcode.ConvI => ".conv_i",
        StackOpcode.ConvU => ".conv_u",
        StackOpcode.ConvU1 => ".conv_u1",
        StackOpcode.ConvU4 => ".conv_u4",
        StackOpcode.ConvU8 => ".conv_u8",
        StackOpcode.SkipInit => ".skipInit",
        _ => throw new ArgumentOutOfRangeException(nameof(Kind))
    };

    internal static readonly StackOperation Nop = new(StackOpcode.Nop);
}

/// <summary>
/// A hole carrying the raw opcode at its pc, which faults when stepped. The extractor writes one at each pc outside
/// the selected profile's reachable code and at each profile combination a template does not select.
/// </summary>
internal sealed record Unadmitted(int Opcode) : Operation
{
    /// <summary>The hole at <paramref name="instruction"/>.</summary>
    internal static Unadmitted At(Instruction instruction) => new(RawOpcode(instruction));

    /// <summary>
    /// The opcode as <c>RawInstruction</c> numbers it: a one-byte opcode is its byte and <c>0xFE nn</c> is
    /// <c>0xFE00 + nn</c>.
    /// </summary>
    internal static int RawOpcode(Instruction instruction) => (ushort)instruction.OpCode.Value;

    internal override string Render(Func<int, string> calleeName) => $".unadmitted {Opcode}";
}

/// <summary>The jump kinds; a conditional jump pops one (zero tests) or two operands.</summary>
internal enum JumpKind
{
    Always, IfZero, IfNonzero, Equal, NotEqual, Less, LessOrEqual, Greater, GreaterOrEqual,
    LessUnsigned, LessOrEqualUnsigned, GreaterUnsigned, GreaterOrEqualUnsigned
}

/// <summary>A jump to the instruction at index <paramref name="Target"/>.</summary>
internal sealed record Jump(JumpKind Kind, int Target) : Operation
{
    /// <summary>The jump depends on the evaluation stack.</summary>
    internal bool Conditional => Kind != JumpKind.Always;

    /// <summary>The number of evaluation stack operands a conditional jump pops.</summary>
    internal int Operands => Kind switch
    {
        JumpKind.Always => 0,
        JumpKind.IfZero or JumpKind.IfNonzero => 1,
        _ => 2
    };

    internal override string Render(Func<int, string> calleeName) => $"{Name} {Target}";

    /// <summary>The Lean constructor name, without its dot.</summary>
    internal string Mnemonic => Name[1..];

    string Name => Kind switch
    {
        JumpKind.Always => ".br", JumpKind.IfZero => ".brfalse", JumpKind.IfNonzero => ".brtrue",
        JumpKind.Equal => ".beq", JumpKind.NotEqual => ".bne_un", JumpKind.Less => ".blt",
        JumpKind.LessOrEqual => ".ble", JumpKind.Greater => ".bgt", JumpKind.GreaterOrEqual => ".bge",
        JumpKind.LessUnsigned => ".blt_un", JumpKind.LessOrEqualUnsigned => ".ble_un",
        JumpKind.GreaterUnsigned => ".bgt_un", JumpKind.GreaterOrEqualUnsigned => ".bge_un",
        _ => throw new ArgumentOutOfRangeException(nameof(Kind))
    };
}

internal sealed record Switch(ValueList<int> Targets) : Operation
{
    internal override string Render(Func<int, string> calleeName) => $".switch [{string.Join(", ", Targets)}]";
}

/// <summary>A return whose value and storage width are determined by the method declaration.</summary>
internal sealed record Return : Operation
{
    internal override string Render(Func<int, string> calleeName) => ".ret";
}

/// <summary>A fault of the modelled CLR exception type.</summary>
internal sealed record Throw(ExceptionType Exception) : Operation
{
    internal override string Render(Func<int, string> calleeName) => $".throw {Exception.ToLean()}";
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
internal sealed record Arg(int Index) : Operation
{
    internal override string Render(Func<int, string> calleeName) => $".ldarg {Index}";
}

/// <summary>An argument assigned from the stack into its home, whose kind gives any narrowing.</summary>
internal sealed record Starg(int Index) : Operation
{
    internal override string Render(Func<int, string> calleeName) => $".starg {Index}";
}

/// <summary>The address of an argument's home.</summary>
internal sealed record Ldarga(int Index) : Operation
{
    internal override string Render(Func<int, string> calleeName) => $".ldarga {Index}";
}

/// <summary>A local pushed from its slot; the slot's kind gives any narrowing.</summary>
internal sealed record Local(int Index) : Operation
{
    /// <summary>The load of the argument homed in this slot when the body names the argument, as diagnostics show it.
    /// </summary>
    internal Arg? Argument { get; init; }

    internal override string Render(Func<int, string> calleeName) =>
        Argument?.Render(calleeName) ?? $".ldloc {Index}";
}

/// <summary>A local assigned from the stack; the slot's kind gives any narrowing.</summary>
internal sealed record SetLocal(int Index) : Operation
{
    /// <summary>The store to the argument homed in this slot when the body names the argument, as diagnostics show it.
    /// </summary>
    internal Starg? Argument { get; init; }

    internal override string Render(Func<int, string> calleeName) =>
        Argument?.Render(calleeName) ?? $".stloc {Index}";
}

internal sealed record LocalAddress(int Index) : Operation
{
    /// <summary>The address of the argument homed in this slot when the body names the argument, as diagnostics show
    /// it.</summary>
    internal Ldarga? Argument { get; init; }

    internal override string Render(Func<int, string> calleeName) =>
        Argument?.Render(calleeName) ?? $".ldloca {Index}";
}

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

    /// <summary>The Lean constructor name, without its dot: `ldc_i4` for 32 bits and `ldc_i8` for 64.</summary>
    string Mnemonic => Width switch
    {
        32 => "ldc_i4",
        64 => "ldc_i8",
        _ => throw new InvalidOperationException($"No integer constant instruction has width {Width}.")
    };

    internal override string Render(Func<int, string> calleeName) => Numeral
        ? $".{Mnemonic} {Value}" : $".{Mnemonic} (BitVec.ofInt {Width} ({Value}))";
}

internal enum CallKind { Static, Instance, Tail }

/// <summary>
/// A call of the method at index <paramref name="Method"/> with the given operand count. A static or tail call
/// names the method its raw operand names, <see cref="Site"/>, and takes its target from its link; a constrained
/// one also names the type its prefix resolves the method on, <see cref="ConstrainedType"/>.
/// </summary>
internal sealed record Call(CallKind Kind, int Method, int Arguments, bool Constrained = false) : Operation
{
    /// <summary>The typed method the call site's raw operand names, which the extraction sets.</summary>
    internal MethodRef? Site { get; init; }

    /// <summary>The type term of the <c>constrained.</c> prefix's closed operand.</summary>
    internal string? ConstrainedType { get; init; }

    internal override IEnumerable<int> Methods => [Method];

    internal override Operation Renumber(Func<int, int> map) => this with { Method = map(Method) };

    internal override string? Link(Func<int, string> calleeName) => $".direct {calleeName(Method)}";

    internal override string Render(Func<int, string> calleeName) => Kind switch
    {
        CallKind.Instance => $".callInstance {calleeName(Method)} {Arguments}",
        CallKind.Static or CallKind.Tail =>
            $".call ({Site?.ToLean() ?? throw new InvalidOperationException("A call has no method operand.")}) " +
            Prefixes,
        _ => throw new ArgumentOutOfRangeException(nameof(Kind))
    };

    string Prefixes => (Kind, Constrained) switch
    {
        (CallKind.Tail, false) => "{ tail := true }",
        (CallKind.Static, true) => $"{{ constrained := some ({ConstrainedType ??
            throw new InvalidOperationException("A constrained call has no constraint type.")}) }}",
        (CallKind.Static, false) => "{}",
        _ => throw new InvalidOperationException("A tail call carries no constrained prefix.")
    };
}

/// <summary>What a <c>newobj</c> allocates, as its link states it.</summary>
internal abstract record Allocation
{
    /// <summary>A zeroed value-type temporary of the layout's <paramref name="Size"/> bytes.</summary>
    internal sealed record Aggregate(int Size) : Allocation;

    /// <summary>A class instance with its base classes (Lean type terms), nearest first, and its field bytes.
    /// </summary>
    internal sealed record Instance(ValueList<string> Bases, int Size) : Allocation;
}

/// <summary>
/// <c>newobj</c> entering the constructor at method index <paramref name="Method"/> with a fresh
/// <paramref name="Allocated"/>. <paramref name="Constructor"/> is the typed reference its raw operand names,
/// which the extraction sets; rendering the instruction before it is set fails.
/// </summary>
internal sealed record Newobj(int Method, Allocation Allocated, MethodRef? Constructor) : Operation
{
    internal override IEnumerable<int> Methods => [Method];

    internal override Operation Renumber(Func<int, int> map) => this with { Method = map(Method) };

    internal override string? Link(Func<int, string> calleeName) => Allocated switch
    {
        Allocation.Aggregate aggregate => $".aggregate {calleeName(Method)} {aggregate.Size}",
        Allocation.Instance instance =>
            $".object {calleeName(Method)} {LeanText.ClassList(instance.Bases)} {instance.Size}",
        _ => throw new InvalidOperationException("Unknown allocation: " + Allocated)
    };

    internal override string Render(Func<int, string> calleeName) => $".newobj ({(Constructor ??
        throw new InvalidOperationException("A construction is rendered before its constructor is named."))
        .ToLean()})";
}

/// <summary>A virtual call dispatched on the receiver's class to the listed (class, method) targets.</summary>
internal sealed record CallVirtual(ValueList<(string Class, int Method)> Targets, int Arguments) : Operation
{
    internal override IEnumerable<int> Methods => Targets.Select(target => target.Method);

    internal override Operation Renumber(Func<int, int> map) =>
        this with { Targets = [.. Targets.Select(target => (target.Class, map(target.Method)))] };

    internal override string? Link(Func<int, string> calleeName) => $".virtual {Table(calleeName)}";

    internal override string Render(Func<int, string> calleeName) =>
        $".callVirtual {Table(calleeName)} {Arguments}";

    string Table(Func<int, string> calleeName) => "[" + string.Join(", ",
        Targets.Select(target => $"({target.Class}, {calleeName(target.Method)})")) + "]";
}

/// <summary>The CIL instruction of a static field access.</summary>
internal enum StaticFieldOpcode { Ldsfld, Ldsflda, Ldtoken }

/// <summary>
/// A static field load, address load or field token over the field its raw operand names; the field is null
/// until the emitter resolves it, and rendering an unresolved access fails.
/// </summary>
internal sealed record StaticFieldInstruction(StaticFieldOpcode Opcode, FieldRef? Field) : Operation
{
    internal override string Render(Func<int, string> calleeName) => Opcode switch
    {
        StaticFieldOpcode.Ldsfld => $".ldsfld {Operand}",
        StaticFieldOpcode.Ldsflda => $".ldsflda {Operand}",
        _ => $".ldtoken (.field {Operand})"
    };

    string Operand => (Field ?? throw new InvalidOperationException(
        $"Static field {Opcode} rendered before its field operand was resolved")).ToLean();
}

/// <summary>A boolean read of a runtime feature of the selected profile.</summary>
internal sealed record FeatureTest(Feature Feature) : Operation
{
    internal override string Render(Func<int, string> calleeName) =>
        ".feature " + FeatureProfile.LeanFeature(Feature);
}

internal enum FieldAccess { Load, Store, LoadAggregate, StoreAggregate, Address }

/// <summary>
/// A struct field access at byte <paramref name="Offset"/>. <paramref name="Width"/> is the field's size and
/// <paramref name="Signed"/> says a load sign-extends.
/// </summary>
internal sealed record StructField(FieldAccess Access, int Offset, int Width, bool Signed) : Operation
{
    internal override string Render(Func<int, string> calleeName) => Access switch
    {
        FieldAccess.Address => $".fieldAddress {Offset}",
        FieldAccess.LoadAggregate => $".aggregateFieldAt {Offset} {Width}",
        FieldAccess.StoreAggregate => $".setAggregateFieldAt {Offset} {Width}",
        FieldAccess.Load => $".fieldAt {Offset} {Width}" + (Signed ? " true" : ""),
        _ => $".setFieldAt {Offset} {Width}"
    };

    // An address ignores the width, and only a load reads the sign, so two accesses are equal exactly when
    // they render the same, as profiles merged into one template must be.
    public bool Equals(StructField? other) => other is not null && ToLean() == other.ToLean();

    public override int GetHashCode() => ToLean().GetHashCode(StringComparison.Ordinal);
}

/// <summary>
/// A load or store of a class instance field of an admitted class, naming the field operand
/// <paramref name="Reference"/>, which the extraction sets from the raw operand the scalar check compares it with.
/// </summary>
internal sealed record ClassField(ClassViews.FieldOperation Field, FieldRef? Reference) : Operation
{
    internal override string Render(Func<int, string> calleeName) =>
        Naming($"({(Reference ?? throw new InvalidOperationException(
            "A class field access is rendered before its field operand is named.")).ToLean()})");

    /// <summary>The instruction with its field operand written as the Lean term <paramref name="operand"/>.</summary>
    internal string Naming(string operand) => $".{(Field.Store ? "stfld" : "ldfld")} {operand}";

    // The rendered term holds only the direction and the operand, so profiles merged into one template compare those.
    public bool Equals(ClassField? other) =>
        other is not null && Field.Store == other.Field.Store && Reference == other.Reference;

    public override int GetHashCode() => HashCode.Combine(Field.Store, Reference);
}

internal enum AggregateAccess { Load, Store, Initialize, Copy }

/// <summary>A load, store, initialisation or object copy of an aggregate of <paramref name="Size"/> bytes.</summary>
internal sealed record AggregateTransfer(AggregateAccess Access, int Size) : Operation
{
    internal override string Render(Func<int, string> calleeName) => Access switch
    {
        AggregateAccess.Load => $".loadAggregate {Size}",
        AggregateAccess.Store => $".storeAggregate {Size}",
        AggregateAccess.Initialize => $".initAggregate {Size}",
        _ => $".copyObject {Size}"
    };
}

/// <summary>
/// How a scalar load extends its value, and how the Lean term spells an unsigned extension: left out, as an
/// indirect load writes it, or as an explicit <c>false</c>, as a memory transfer writes it.
/// </summary>
internal enum LoadSign { Unsigned, UnsignedSpelled, Signed }

/// <summary>A scalar load of <paramref name="Width"/> bytes extended as <paramref name="Sign"/> says.</summary>
internal sealed record LoadScalar(int Width, LoadSign Sign) : Operation
{
    public LoadScalar(int width, bool signed) : this(width, signed ? LoadSign.Signed : LoadSign.Unsigned)
    {
    }

    /// <summary>The load sign-extends.</summary>
    internal bool Signed => Sign == LoadSign.Signed;

    internal override string Render(Func<int, string> calleeName) => $".loadScalar {Width}" + Sign switch
    {
        LoadSign.Signed => " true",
        LoadSign.UnsignedSpelled => " false",
        _ => ""
    };
}

internal sealed record StoreScalar(int Width) : Operation
{
    internal override string Render(Func<int, string> calleeName) => $".storeScalar {Width}";
}

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

/// <summary>An <c>ldind</c> or <c>stind</c> of <paramref name="Kind"/>, rendered as its constructor.</summary>
internal sealed record IndirectAccess(NumericKind Kind, bool Store) : Operation
{
    /// <summary>Bytes the access moves.</summary>
    internal int Width => Kind.Width();

    /// <summary>Whether a load sign-extends.</summary>
    internal bool Signed => Kind.Signed();

    /// <summary>The Lean term of the kind, such as <c>.i4</c>.</summary>
    internal string KindTerm => Kind.Term();

    internal override string Render(Func<int, string> calleeName) => $".{(Store ? "stind" : "ldind")} {KindTerm}";
}

/// <summary>An <c>ldlen</c> of a value array, an array of class references or a managed handler table.</summary>
internal sealed record ArrayLength : Operation
{
    internal override string Render(Func<int, string> calleeName) => ".ldlen";
}

/// <summary>
/// An <c>ldelem</c> or <c>stelem</c> of <paramref name="Kind"/> on a value array, or the <c>ldelem.i</c> of a managed
/// handler table, rendered as its constructor.
/// </summary>
internal sealed record ArrayElementAccess(NumericKind Kind, bool Store) : Operation
{
    /// <summary>Bytes the access moves.</summary>
    internal int Width => Kind.Width();

    /// <summary>Whether a load sign-extends.</summary>
    internal bool Signed => Kind.Signed();

    internal override string Render(Func<int, string> calleeName) =>
        $".{(Store ? "stelem" : "ldelem")} {Kind.Term()}";
}

/// <summary>
/// A typed <c>ldelem</c> or <c>stelem</c> of the element type <paramref name="Element"/>, the raw operand's type
/// expression. <paramref name="Storage"/> is the element's inline storage, or null for a handler table's method
/// pointer.
/// </summary>
internal sealed record TypedElementAccess(bool Store, Arrays.Element? Storage, string? Element = null) : Operation
{
    // Translation does not see the layout table the term indexes, so the emitter attaches it.
    internal override string Render(Func<int, string> calleeName) =>
        $".{(Store ? "stelem_any" : "ldelem_any")} ({Element ??
            throw new InvalidOperationException("A typed element access is rendered before its element type is attached")})";
}

/// <summary>An <c>ldelem.ref</c> or <c>stelem.ref</c> on an array of class references.</summary>
internal sealed record ReferenceElementAccess(bool Store) : Operation
{
    internal override string Render(Func<int, string> calleeName) => Store ? ".stelem_ref" : ".ldelem_ref";
}

/// <summary>Frame storage of the popped byte count, zeroed as the method's declared localsinit flag says.</summary>
internal sealed record Localloc : Operation
{
    internal override string Render(Func<int, string> calleeName) => ".localloc";
}

/// <summary>The target of an overflow-checked conversion; <c>I</c> and <c>U</c> are native-sized.</summary>
internal enum ConvTarget { I1, U1, I2, U2, I4, U4, I8, U8, I, U }

/// <summary>
/// A conversion to <paramref name="Target"/> that faults on overflow, reading the operand as unsigned when
/// <paramref name="UnsignedSource"/> is set.
/// </summary>
internal sealed record CheckedConvert(ConvTarget Target, bool UnsignedSource) : Operation
{
    internal override string Render(Func<int, string> calleeName) =>
        $".conv_ovf{(UnsignedSource ? "_un" : "")} .{Target.ToString().ToLowerInvariant()}";
}

internal enum CheckedOperator { Add, Sub, Mul }

/// <summary>An overflow-checked <c>add</c>, <c>sub</c> or <c>mul</c>, rendered as its opcode's constructor.</summary>
internal sealed record CheckedArithmetic(CheckedOperator Operator, bool Signed) : Operation
{
    internal override string Render(Func<int, string> calleeName) =>
        $".{Operator.ToString().ToLowerInvariant()}_ovf{(Signed ? "" : "_un")}";
}

/// <summary>A division or, when <paramref name="Remainder"/> is set, a remainder.</summary>
internal sealed record Divide(bool Signed, bool Remainder) : Operation
{
    internal override string Render(Func<int, string> calleeName)
        => $".{(Remainder ? "rem" : "div")}{(Signed ? "" : "_un")}";
}

/// <summary>
/// A new array whose element type is <paramref name="Element"/>, the raw <c>newarr</c> operand's type expression,
/// which the extraction check compares with the token. <paramref name="Class"/> names a class element.
/// </summary>
internal sealed record NewArray(NewArray.ClassElement? Class, string? Element = null) : Operation
{
    /// <summary>The class <paramref name="Name"/> (a full name) of the assembly <paramref name="Scope"/>.</summary>
    internal sealed record ClassElement(string Scope, string Name);

    // Translation does not see the layout table the term indexes, so the emitter attaches it.
    internal override string Render(Func<int, string> calleeName) => $".newarr ({Element ??
        throw new InvalidOperationException("An array allocation is rendered before its element type is attached")})";
}

/// <summary>An <c>ldnull</c>: the null object reference.</summary>
internal sealed record LoadNull : Operation
{
    internal override string Render(Func<int, string> calleeName) => ".ldnull";
}

/// <summary>A <c>castclass</c> of the top reference to the class <paramref name="Type"/>.</summary>
internal sealed record CastClass(string Type) : Operation
{
    internal override string Render(Func<int, string> calleeName) => $".castclass ({Type})";
}

/// <summary>An <c>isinst</c> test of the top reference against the class <paramref name="Type"/>.</summary>
internal sealed record IsInstance(string Type) : Operation
{
    internal override string Render(Func<int, string> calleeName) => $".isinst ({Type})";
}

/// <summary>An initialisation of a span local from the span operation that constructs it.</summary>
internal sealed record InitializeSpanLocal(int Local, SpanSource Source) : Operation
{
    internal override string Render(Func<int, string> calleeName) =>
        $".initializeSpanLocal {Local} ({Source.SpanDescriptor})";
}

/// <summary>
/// An operation of the managed callable pointer model; the signatures are Lean terms and the targets are typed.
/// </summary>
internal abstract record ManagedPointer : Operation
{
    protected abstract string Body(Func<int, string> calleeName);

    internal sealed override string Render(Func<int, string> calleeName) => ".managed " + Body(calleeName);
}

internal sealed record TableLength : ManagedPointer
{
    protected override string Body(Func<int, string> calleeName) => ".tableLength";
}

/// <summary>An indirect call through a callable pointer of the given signature and target catalog.</summary>
internal sealed record IndirectCall(string Signature, ValueList<ManagedTarget> Catalog, bool Tail) : ManagedPointer
{
    internal override IEnumerable<int> Methods => Catalog.Select(target => target.Method);

    internal override Operation Renumber(Func<int, int> map) =>
        this with { Catalog = [.. Catalog.Select(target => target with { Method = map(target.Method) })] };

    internal override string? Link(Func<int, string> calleeName) => $".indirect {Targets(calleeName)}";

    protected override string Body(Func<int, string> calleeName) =>
        $"(.call {Signature} {Targets(calleeName)} {LeanText.Bool(Tail)})";

    string Targets(Func<int, string> calleeName) =>
        "[" + string.Join(", ", Catalog.Select(target => target.Lean(calleeName))) + "]";
}

/// <summary>The address of the managed method <paramref name="Target"/> of the given signature.</summary>
internal sealed record MethodAddress(ManagedTarget Target, string Signature) : ManagedPointer
{
    internal override IEnumerable<int> Methods => [Target.Method];

    internal override Operation Renumber(Func<int, int> map) =>
        this with { Target = Target with { Method = map(Target.Method) } };

    protected override string Body(Func<int, string> calleeName) =>
        $"(.address {Target.Lean(calleeName)} {Signature})";
}

/// <summary>A runtime memory operation.</summary>
internal sealed record Memory(MemoryOperation Operation) : Operation
{
    internal override string Render(Func<int, string> calleeName) => ".memory " + Operation.ToLean();
}

/// <summary>An intrinsic of the scalar, vector or hardware families over the given number of operands.</summary>
internal abstract record Intrinsic(int Arguments) : Operation
{
    protected abstract string Family { get; }

    internal sealed override string Render(Func<int, string> calleeName) => $".intrinsic ({Family}) {Arguments}";
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
    : Intrinsic(Arguments)
{
    /// <summary>The function counts bits, which the instruction semantics treats as pure word arithmetic.</summary>
    internal bool CountsBits => Function is ScalarFunction.PopCount or ScalarFunction.LeadingZeroCount or
        ScalarFunction.TrailingZeroCount or ScalarFunction.Log2;

    // A helper ignores the width, sign or result its Lean term leaves out, so two of them are equal
    // exactly when they render the same, as profiles merged into one template must be.
    public bool Equals(ScalarIntrinsic? other) =>
        other is not null && Arguments == other.Arguments && Family == other.Family;

    public override int GetHashCode() => HashCode.Combine(Arguments, Family);

    protected override string Family => Function switch
    {
        ScalarFunction.BigMul32 => $".scalar (.bigMul32 {LeanText.Bool(Signed)})",
        ScalarFunction.DivRem => $".scalar (.divRem {Width} {LeanText.Bool(Signed)})",
        ScalarFunction.Min => MathCall("min"),
        ScalarFunction.Max => MathCall("max"),
        ScalarFunction.Clamp => MathCall("clamp"),
        ScalarFunction.Abs => MathCall("abs"),
        ScalarFunction.Sign => MathCall("sign"),
        ScalarFunction.RotateLeft => $".scalar (.rotateLeft {Width})",
        ScalarFunction.RotateRight => $".scalar (.rotateRight {Width})",
        ScalarFunction.PopCount => Count("popCount"),
        ScalarFunction.LeadingZeroCount => Count("leadingZeroCount"),
        ScalarFunction.TrailingZeroCount => Count("trailingZeroCount"),
        ScalarFunction.Log2 => Count("log2"),
        ScalarFunction.RoundUpToPowerOf2 => $".scalar (.roundUpToPowerOf2 {Width})",
        ScalarFunction.IsPow2 => $".scalar (.isPow2 {Width} {LeanText.Bool(Signed)})",
        _ => $".scalar (.reverseEndianness {Width} {LeanText.Bool(Signed)})"
    };

    string MathCall(string name) => $".scalar (.math .{name} {Width} {LeanText.Bool(Signed)})";

    string Count(string name) => $".scalar (.{name} {Width} .word{Result})";
}

/// <summary>The vector constructor that sets the low 64-bit lane and leaves the rest unspecified.</summary>
internal sealed record VectorCreateScalarUnsafe64() : Intrinsic(1)
{
    protected override string Family => ".vector .createScalarUnsafe64";
}

/// <summary>The x86 64-bit division with remainder.</summary>
internal sealed record X86BaseDivRem64() : Intrinsic(3)
{
    protected override string Family => ".x86Base .divRem64";
}

/// <summary>A vector or hardware intrinsic no consumer inspects, held as its rendered Lean family term.</summary>
internal sealed record HardwareIntrinsic : Intrinsic
{
    readonly string family;

    internal HardwareIntrinsic(string family, int arguments) : base(arguments) => this.family = family;

    protected override string Family => family;
}

/// <summary>Which elements of an array a span covers.</summary>
internal enum ArrayRange { Whole, FromStart, Counted }

internal static class ArrayRangeText
{
    internal static string LeanName(this ArrayRange range) => range switch
    {
        ArrayRange.Whole => ".whole", ArrayRange.FromStart => ".fromStart", ArrayRange.Counted => ".counted",
        _ => throw new ArgumentOutOfRangeException(nameof(range))
    };
}
