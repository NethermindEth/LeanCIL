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
