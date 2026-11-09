namespace Examples;

/// <summary>A level read through a static helper that tests its word arguments.</summary>
public sealed class Gauge
{
    /// <summary>The measured level.</summary>
    public int Level;

    /// <summary>The largest level reported.</summary>
    public int Limit;

    static int Saturate(int value, int limit) => value < limit ? value : limit;

    /// <summary>The level, saturated at the limit.</summary>
    public int Current() => Saturate(Level, Limit);

    /// <summary>Records the saturated level as the limit.</summary>
    public void Settle() => Limit = Saturate(Level, Limit);

    /// <summary>The smaller of two words, through the helper alone.</summary>
    public static int Smaller(int value, int limit) => Saturate(value, limit);

    /// <summary>Sums an array by index from an instance method, wrapping at 32 bits.</summary>
    public int Total(int[] readings)
    {
        var total = 0;
        for (var index = 0; index < readings.Length; index++) total += readings[index];
        return total;
    }

    static int Within(int value, int limit) =>
        value > limit ? throw new System.InvalidOperationException() : value;

    /// <summary>A word no greater than the limit, through a helper that throws beyond it.</summary>
    public static int Bounded(int value, int limit) => Within(value, limit);

    static int Doubled(int value) => unchecked(value + value);

    /// <summary>Twice a word, wrapping at 32 bits, through a helper that only computes.</summary>
    public static int Twice(int value) => Doubled(value);
}
