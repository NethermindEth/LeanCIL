namespace Examples;

// Static abstract interface members select an operation and a flag at compile time through struct
// type arguments, so each closed instantiation dispatches without a receiver or boxing.
public interface IBinaryStep
{
    static abstract ulong Apply(ulong left, ulong right);
}

public interface IStepFlag
{
    static abstract bool IsActive { get; }
}

public struct AddStep : IBinaryStep
{
    public static ulong Apply(ulong left, ulong right) => left + right;
}

public struct XorStep : IBinaryStep
{
    static ulong IBinaryStep.Apply(ulong left, ulong right) => left ^ right;
}

public struct StepOn : IStepFlag
{
    public static bool IsActive => true;
}

public struct StepOff : IStepFlag
{
    public static bool IsActive => false;
}

public static class StaticInterfaces
{
    public static ulong Step<TStep, TFlag>(ulong left, ulong right)
        where TStep : struct, IBinaryStep where TFlag : struct, IStepFlag =>
        TFlag.IsActive ? TStep.Apply(left, right) + 1 : TStep.Apply(left, right);

    public static ulong AddCounted(ulong left, ulong right) => Step<AddStep, StepOn>(left, right);

    public static ulong XorPlain(ulong left, ulong right) => Step<XorStep, StepOff>(left, right);
}

// A generic static virtual slot with a default body forwards to the struct's static abstract slot.
// A struct that does not implement the generic slot runs the interface default, specialized at itself.
public interface IAllowance<TSelf> where TSelf : struct, IAllowance<TSelf>
{
    static abstract bool Spend(ref TSelf self, ulong amount);

    static virtual bool Spend<TPrice>(ref TSelf self) where TPrice : struct, IPrice =>
        TSelf.Spend(ref self, TPrice.Price);
}

public interface IPrice
{
    static abstract ulong Price { get; }
}

public struct TriplePrice : IPrice
{
    public static ulong Price => 3;
}

public struct Allowance : IAllowance<Allowance>
{
    public ulong Left;

    public static bool Spend(ref Allowance self, ulong amount)
    {
        if (self.Left < amount) return false;
        self.Left -= amount;
        return true;
    }
}

// Overrides the generic slot, so the interface default must not run for this receiver.
public struct DoublingAllowance : IAllowance<DoublingAllowance>
{
    public ulong Left;

    public static bool Spend(ref DoublingAllowance self, ulong amount)
    {
        if (self.Left < amount) return false;
        self.Left -= amount;
        return true;
    }

    static bool IAllowance<DoublingAllowance>.Spend<TPrice>(ref DoublingAllowance self) =>
        Spend(ref self, TPrice.Price * 2);
}

// Re-implements the generic slot in a derived interface, which the runtime prefers over the default body.
public interface IRefundingAllowance<TSelf> : IAllowance<TSelf> where TSelf : struct, IRefundingAllowance<TSelf>
{
    static bool IAllowance<TSelf>.Spend<TPrice>(ref TSelf self) => TSelf.Spend(ref self, TPrice.Price - 1);
}

public struct RefundingAllowance : IRefundingAllowance<RefundingAllowance>
{
    public ulong Left;

    public static bool Spend(ref RefundingAllowance self, ulong amount)
    {
        if (self.Left < amount) return false;
        self.Left -= amount;
        return true;
    }
}

public static class StaticVirtualDefaults
{
    public static ulong Spend<TAllowance, TPrice>(ref TAllowance allowance)
        where TAllowance : struct, IAllowance<TAllowance> where TPrice : struct, IPrice =>
        TAllowance.Spend<TPrice>(ref allowance) ? 1UL : 0UL;

    public static ulong SpendDefault(ref Allowance allowance) => Spend<Allowance, TriplePrice>(ref allowance);

    public static ulong SpendOverride(ref DoublingAllowance allowance) =>
        Spend<DoublingAllowance, TriplePrice>(ref allowance);

    public static ulong SpendRefunding(ref RefundingAllowance allowance) =>
        Spend<RefundingAllowance, TriplePrice>(ref allowance);
}

// A flag type argument whose static getter returns a constant selects code at compile time; the
// JIT drops the other block. Each guarded block here reads the process clock, which extraction
// rejects, so a closed instantiation extracts only when that block is dead under its flag.
public static class ConstantFlags
{
    public static ulong Trace<TFlag>(ulong value) where TFlag : struct, IStepFlag
    {
        if (TFlag.IsActive) value += (ulong)System.Environment.TickCount64;
        if (typeof(TFlag) != typeof(StepOff)) value ^= (ulong)System.Environment.TickCount64;
        return value + 1;
    }

    public static ulong Count<TFlag>(ulong value) where TFlag : struct, IStepFlag
    {
        if (TFlag.IsActive) value = value * 3 + 1;
        if (typeof(TFlag) != typeof(StepOn)) value ^= (ulong)System.Environment.TickCount64;
        return value;
    }

    public static ulong TraceOff(ulong value) => Trace<StepOff>(value);

    public static ulong TraceOn(ulong value) => Trace<StepOn>(value);

    public static ulong CountOn(ulong value) => Count<StepOn>(value);

    public static ulong TraceThenCount(ulong value) => Count<StepOn>(Trace<StepOff>(value));
}

// A static virtual slot runs its most specific interface-level body: a derived interface's
// re-implementation beats the base default, and the deepest one in a chain wins.
public interface IScale
{
    static virtual ulong Scale(ulong value) => value * 2;
}

public interface IScaleMore : IScale
{
    static ulong IScale.Scale(ulong value) => value * 4;
}

public interface IScaleMost : IScaleMore
{
    static ulong IScale.Scale(ulong value) => value * 8 + 1;
}

// Unrelated to IScaleMore; listing both leaves no most specific body.
public interface IScaleSide : IScale
{
    static ulong IScale.Scale(ulong value) => value * 3;
}

public struct ScaleMore : IScaleMore { }

public struct ScaleMost : IScaleMost { }

// The struct's own implementation beats every interface-level body.
public struct ScaleOwn : IScaleMost
{
    public static ulong Scale(ulong value) => value + 1;
}

// A derived interface supplies the body of a base `static abstract` slot.
public interface IMeasure
{
    static abstract ulong Measure(ulong value);
}

public interface IMeasureFive : IMeasure
{
    static ulong IMeasure.Measure(ulong value) => value + 5;
}

public struct MeasureFive : IMeasureFive { }

public static class MostSpecificBodies
{
    static ulong Scaled<TScale>(ulong value) where TScale : struct, IScale => TScale.Scale(value);

    static ulong Measured<TMeasure>(ulong value) where TMeasure : struct, IMeasure => TMeasure.Measure(value);

    public static ulong More(ulong value) => Scaled<ScaleMore>(value);

    public static ulong Most(ulong value) => Scaled<ScaleMost>(value);

    public static ulong Own(ulong value) => Scaled<ScaleOwn>(value);

    public static ulong Five(ulong value) => Measured<MeasureFive>(value);
}

// Flag getters supplied by a derived interface fold like any constant getter: the derived body, not
// the base default, decides which block is extracted.
public interface IQuietByDefault
{
    static virtual bool IsActive => false;
}

public interface ILoud : IQuietByDefault
{
    static bool IQuietByDefault.IsActive => true;
}

public interface ILoudByDefault
{
    static virtual bool IsActive => true;
}

public interface IQuiet : ILoudByDefault
{
    static bool ILoudByDefault.IsActive => false;
}

public struct Loud : ILoud { }

public struct Quiet : IQuiet { }

public static class DerivedFlags
{
    public static ulong Count<TFlag>(ulong value) where TFlag : struct, IQuietByDefault
    {
        if (TFlag.IsActive) value = value * 3 + 1;
        return value;
    }

    // The clock read is rejected, so this extracts only when the derived getter prunes its block.
    public static ulong Trace<TFlag>(ulong value) where TFlag : struct, ILoudByDefault
    {
        if (TFlag.IsActive) value += (ulong)System.Environment.TickCount64;
        return value + 1;
    }

    public static ulong CountLoud(ulong value) => Count<Loud>(value);

    public static ulong TraceQuiet(ulong value) => Trace<Quiet>(value);
}

// A flag getter computed from other getters, at any depth and through generic or derived-interface
// bodies, folds through each callee's own certificate. Each guarded block reads the process clock,
// which extraction rejects, so these methods extract only when their computed flag prunes it.
public struct Forced : IStepFlag
{
    public static bool IsActive => false;
}

public static class Gate<TFlag> where TFlag : struct, IStepFlag
{
    public static bool Open => TFlag.IsActive || typeof(TFlag) == typeof(Forced);
}

public static class Hush<TFlag> where TFlag : struct, ILoudByDefault
{
    public static bool Silent => !TFlag.IsActive;
}

public static class ComputedFlags
{
    static bool Both => StepOn.IsActive && StepOff.IsActive;

    static bool NotOff => !StepOff.IsActive;

    static bool Outer => Middle;

    static bool Middle => !Both;

    // A recursive pair never returns, so neither getter is a constant.
    static bool Ping => Pong;

    static bool Pong => Ping;

    public static ulong TraceBoth(ulong value)
    {
        if (Both) value += (ulong)System.Environment.TickCount64;
        return value + 1;
    }

    public static ulong TraceNotOff(ulong value)
    {
        if (!NotOff) value += (ulong)System.Environment.TickCount64;
        return value * 3;
    }

    public static ulong TraceChained(ulong value)
    {
        if (!Outer) value += (ulong)System.Environment.TickCount64;
        return value ^ 5;
    }

    public static ulong TraceGated(ulong value)
    {
        if (Gate<StepOff>.Open) value += (ulong)System.Environment.TickCount64;
        if (!Gate<Forced>.Open) value ^= (ulong)System.Environment.TickCount64;
        return value + 2;
    }

    public static ulong TraceSilent(ulong value)
    {
        if (!Hush<Quiet>.Silent) value += (ulong)System.Environment.TickCount64;
        return value + 3;
    }

    // A getter reading a static field is not a constant, so both blocks stay live.
    public static ulong CountConfigured(ulong value) => StaticScalars.ReadBoolean() ? value + 1 : value;

    public static ulong CountPing(ulong value) => Ping ? value + 1 : value;
}

// Static slots on closed generic struct receivers: the receiver's implementation is closed at its
// type arguments, and the interface it lists is instantiated through its InterfaceImpl at them, so
// the type argument both selects the interface instantiation and decides closed type tests.
public struct WordFlag<T> : IStepFlag where T : unmanaged
{
    public static bool IsActive => typeof(T) == typeof(ulong);
}

public interface IWidth<T> where T : unmanaged
{
    static abstract ulong Width(ulong value);
}

public interface IPadded<T> where T : unmanaged
{
    static virtual ulong Pad(ulong value) => typeof(T) == typeof(uint) ? value + 4 : value + 8;
}

public struct Measured<T> : IWidth<T>, IPadded<T> where T : unmanaged
{
    public static ulong Width(ulong value) => typeof(T) == typeof(uint) ? value * 4 : value * 8;
}

public static class GenericReceivers
{
    static ulong Trace<TFlag>(ulong value) where TFlag : struct, IStepFlag
    {
        if (TFlag.IsActive) value += (ulong)System.Environment.TickCount64;
        return value + 1;
    }

    static ulong Count<TFlag>(ulong value) where TFlag : struct, IStepFlag =>
        TFlag.IsActive ? value * 3 + 1 : value;

    static ulong Width<TMeasure, T>(ulong value) where TMeasure : struct, IWidth<T> where T : unmanaged =>
        TMeasure.Width(value);

    static ulong Pad<TPad, T>(ulong value) where TPad : struct, IPadded<T> where T : unmanaged =>
        TPad.Pad(value);

    // The narrow flag is false, so the clock read it guards is pruned.
    public static ulong TraceNarrow(ulong value) => Trace<WordFlag<uint>>(value);

    public static ulong CountWide(ulong value) => Count<WordFlag<ulong>>(value);

    public static ulong WidthNarrow(ulong value) => Width<Measured<uint>, uint>(value);

    public static ulong WidthWide(ulong value) => Width<Measured<ulong>, ulong>(value);

    public static ulong PadNarrow(ulong value) => Pad<Measured<uint>, uint>(value);

    public static ulong PadWide(ulong value) => Pad<Measured<ulong>, ulong>(value);
}
