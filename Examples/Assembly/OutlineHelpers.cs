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

    /// <summary>How far the saturated level lies below the limit, the first helper result kept in a local.</summary>
    public int Slack()
    {
        var level = Saturate(Level, Limit);
        var limit = Saturate(Limit, Limit);
        return unchecked(limit - level);
    }

    /// <summary>The gap between two saturated words, the first helper result kept in a local.</summary>
    public static int Gap(int value, int limit)
    {
        var low = Saturate(value, limit);
        var high = Saturate(limit, limit);
        return unchecked(high - low);
    }

    static int Blend(int value, int limit)
    {
        var sum = unchecked(value + limit);
        var product = unchecked(value * limit);
        return unchecked(product - sum);
    }

    /// <summary>A word mixed with the limit through a helper that keeps its own locals.</summary>
    public static int Blended(int value, int limit) => Blend(value, limit);

    static int Capped(Gauge gauge, int value) => value < gauge.Limit ? value : gauge.Limit;

    /// <summary>The level capped at the limit, through a helper that reads the gauge it is handed.</summary>
    public int CappedLevel() => Capped(this, Level);

    /// <summary>The room left above the saturated level, tested after the helper result is kept in a local.</summary>
    public int Margin()
    {
        var level = Saturate(Level, Limit);
        return level < Limit ? unchecked(Limit - level) : 0;
    }

    static int Clamp(int value, int low, int high)
    {
        var floor = value < low ? low : value;
        return floor > high ? high : floor;
    }

    /// <summary>A word held between two bounds, through a helper that tests a local of its own.</summary>
    public static int Clamped(int value, int low, int high) => Clamp(value, low, high);

    /// <summary>The gap between two capped words, the first result of the object helper kept in a local.</summary>
    public int CappedSlack()
    {
        var capped = Capped(this, Level);
        var limit = Capped(this, Limit);
        return unchecked(limit - capped);
    }

    static int Checked(Gauge gauge, int value) =>
        value > gauge.Limit ? throw new System.InvalidOperationException() : value;

    /// <summary>The level, through a helper that throws beyond the limit of the gauge it is handed.</summary>
    public int CheckedLevel() => Checked(this, Level);

    static int Raise(Gauge gauge, int value, int low)
    {
        var floor = value < low ? low : value;
        return floor > gauge.Limit ? throw new System.InvalidOperationException() : floor;
    }

    /// <summary>The level raised to zero, through a helper that throws when its local passes the limit.</summary>
    public int RaisedLevel() => Raise(this, Level, 0);
}
