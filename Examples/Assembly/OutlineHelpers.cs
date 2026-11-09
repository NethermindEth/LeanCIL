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
}
