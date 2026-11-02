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
