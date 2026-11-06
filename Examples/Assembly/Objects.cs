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

    /// <summary>Bumps two accounts through <see cref="Bump"/>; both may be the same instance.</summary>
    public static void BumpBoth(Account first, Account second, ulong amount)
    {
        Bump(first, amount);
        Bump(second, amount);
    }
}
