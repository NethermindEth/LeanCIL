namespace Examples;

/// <summary>A class instance; its identity is the heap allocation that holds it.</summary>
public sealed class Account
{
    /// <summary>The current balance.</summary>
    public ulong Balance;

    /// <summary>The largest single withdrawal.</summary>
    public uint Limit;

    /// <summary>The balance plus the limit, read through the instance as its receiver.</summary>
    public ulong Headroom => Balance + Limit;

    /// <summary>Adds to the balance, wrapping at 64 bits; callers reach it through <c>callvirt</c>.</summary>
    public void Deposit(ulong amount) => Balance += amount;
}

/// <summary>A class instance whose constructor sets one field and leaves the other zero.</summary>
public sealed class Tally
{
    /// <summary>The running count.</summary>
    public ulong Count;

    /// <summary>The amount each count adds, fixed at construction.</summary>
    public uint Step;

    /// <summary>Creates a tally at zero with the given step.</summary>
    public Tally(uint step) => Step = step;
}

/// <summary>A class with no fields: its instances have identity and nothing else.</summary>
public sealed class Marker
{
}

/// <summary>Reference identity and null tests on class instances.</summary>
public static class Objects
{
    /// <summary>Reference equality: the same instance, or both null.</summary>
    public static bool Same(Account left, Account right) => left == right;

    /// <summary>A null test, compiled as a comparison against <c>ldnull</c>.</summary>
    public static bool IsNull(Account? account) => account is null;

    /// <summary>A presence test, compiled as an unsigned greater-than against <c>ldnull</c>.</summary>
    public static bool IsPresent(Account? account) => account is not null;

    /// <summary>Selects one of two references through a branch on the first one's presence.</summary>
    public static Account? FirstPresent(Account? first, Account? second)
    {
        Account? selected = second;
        if (first != null) selected = first;
        return selected;
    }

    /// <summary>Reads a 64-bit field of a class instance.</summary>
    public static ulong BalanceOf(Account account) => account.Balance;

    /// <summary>Stores a field and reads it back through the same reference.</summary>
    public static ulong Replace(Account account, ulong amount)
    {
        account.Balance = amount;
        return account.Balance;
    }

    /// <summary>Stores a 32-bit field, leaving the other field of the instance unchanged.</summary>
    public static void SetLimit(Account account, uint limit) => account.Limit = limit;

    /// <summary>Adds to the balance of one account, wrapping at 64 bits.</summary>
    public static void Bump(Account account, ulong amount) => account.Balance += amount;

    /// <summary>Allocates a tally, stores into it and reads both fields back.</summary>
    public static ulong Fresh(uint step)
    {
        var tally = new Tally(step);
        tally.Count = 5;
        return tally.Count + tally.Step;
    }

    /// <summary>
    /// Deposits into two accounts through the instance method, each call checking its receiver for null;
    /// both may be the same instance.
    /// </summary>
    public static void DepositBoth(Account first, Account second, ulong amount)
    {
        first.Deposit(amount);
        second.Deposit(amount);
    }

    /// <summary>Two instances of a class with no fields are still two distinct instances.</summary>
    public static bool TwoMarkers()
    {
        var first = new Marker();
        var second = new Marker();
        return first != second;
    }

    /// <summary>Bumps two accounts through <see cref="Bump"/>; both may be the same instance.</summary>
    public static void BumpBoth(Account first, Account second, ulong amount)
    {
        Bump(first, amount);
        Bump(second, amount);
    }
}
