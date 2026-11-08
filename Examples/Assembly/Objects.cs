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

/// <summary>A singly linked node: a value and the node after it, or null at the end.</summary>
public sealed class Node
{
    /// <summary>The node's value.</summary>
    public ulong Value;

    /// <summary>The following node, or null.</summary>
    public Node? Next;
}

/// <summary>
/// A class holding a string, whose class the model does not represent: the reference is copied, compared and
/// tested for null, never read through.
/// </summary>
public sealed class Tagged
{
    /// <summary>The instance's identifier.</summary>
    public ulong Id;

    /// <summary>The tag, or null.</summary>
    public string? Tag;
}

/// <summary>A class with no fields: its instances have identity and nothing else.</summary>
public sealed class Marker
{
}

/// <summary>An abstract base class: it declares a field and a constructor but has no instances of its own.</summary>
public abstract class Shape
{
    /// <summary>The shape's identifier, the first field of every derived instance.</summary>
    public ulong Id;

    /// <summary>Sets the identifier; only the constructors of derived classes call it.</summary>
    protected Shape(ulong id) => Id = id;
}

/// <summary>A class derived from <see cref="Shape"/>: its own field follows the fields of its base.</summary>
public class Circle : Shape
{
    /// <summary>The circle's radius.</summary>
    public ulong Radius;

    /// <summary>Creates a circle, chaining to the base constructor for the identifier.</summary>
    public Circle(ulong id, ulong radius) : base(id) => Radius = radius;
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

    /// <summary>Reads the field a base class declares, through a reference of the base type.</summary>
    public static ulong IdOf(Shape shape) => shape.Id;

    /// <summary>Constructs a derived instance, whose constructor chains to its base's, and reads both fields.</summary>
    public static ulong Describe(ulong id, ulong radius)
    {
        var circle = new Circle(id, radius);
        return circle.Id + circle.Radius;
    }

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

    /// <summary>Deposits <paramref name="amount"/> <paramref name="times"/> times, one instance call per iteration.</summary>
    public static void DepositTimes(Account account, ulong amount, uint times)
    {
        for (uint i = 0; i < times; i++)
            account.Deposit(amount);
    }

    /// <summary>
    /// Deposits the balance of <paramref name="source"/> into <paramref name="account"/> <paramref name="times"/>
    /// times; <paramref name="source"/> is only read.
    /// </summary>
    public static void DepositFrom(Account account, Account source, uint times)
    {
        for (uint i = 0; i < times; i++)
            account.Deposit(source.Balance);
    }

    /// <summary>
    /// Withdraws <paramref name="amount"/> only when the balance covers it; returns what it withdrew.
    /// </summary>
    public static ulong Withdraw(Account account, ulong amount)
    {
        if (account.Balance < amount)
            return 0;
        account.Balance -= amount;
        return amount;
    }

    /// <summary>Two instances of a class with no fields are still two distinct instances.</summary>
    public static bool TwoMarkers()
    {
        var first = new Marker();
        var second = new Marker();
        return first != second;
    }

    /// <summary>Makes <paramref name="next"/> follow <paramref name="node"/>; both may be the same node.</summary>
    public static void Link(Node node, Node next) => node.Next = next;

    /// <summary>Makes <paramref name="next"/> follow both nodes; any two of the three may be the same node.</summary>
    public static void LinkBoth(Node first, Node second, Node next)
    {
        first.Next = next;
        second.Next = next;
    }

    /// <summary>The value of the node after <paramref name="node"/>.</summary>
    public static ulong SecondValue(Node node) => node.Next!.Value;

    /// <summary>Links two nodes through <see cref="Link"/> and reads the second value back.</summary>
    public static ulong LinkedValue(Node node, Node next)
    {
        Link(node, next);
        return SecondValue(node);
    }

    /// <summary>As <see cref="LinkBoth"/>, with nodes named like a proof's own hypotheses and memories.</summary>
    public static void Relink(Node held1, Node stored1, Node next)
    {
        stored1.Next = next;
        held1.Next = next;
    }

    /// <summary>Copies the tag of <paramref name="source"/> into <paramref name="target"/>, which may be it.</summary>
    public static void CopyTag(Tagged target, Tagged source) => target.Tag = source.Tag;

    /// <summary>Whether two instances hold the same tag reference, or both hold none.</summary>
    public static bool SameTag(Tagged left, Tagged right) => (object?)left.Tag == (object?)right.Tag;

    /// <summary>Whether the instance holds a tag.</summary>
    public static bool HasTag(Tagged item) => item.Tag is not null;

    /// <summary>Gives <paramref name="target"/> the tag of <paramref name="source"/> when it holds none.</summary>
    public static void FillTag(Tagged target, Tagged source)
    {
        if (target.Tag is null) target.Tag = source.Tag;
    }

    /// <summary>Removes the instance's tag.</summary>
    public static void ClearTag(Tagged item) => item.Tag = null;

    /// <summary>Unlinks the node after <paramref name="node"/> and returns it, or null at the end.</summary>
    public static Node? Detach(Node node)
    {
        var next = node.Next;
        node.Next = null;
        return next;
    }

    /// <summary>Bumps two accounts through <see cref="Bump"/>; both may be the same instance.</summary>
    public static void BumpBoth(Account first, Account second, ulong amount)
    {
        Bump(first, amount);
        Bump(second, amount);
    }
}
