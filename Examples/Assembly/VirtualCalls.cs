namespace Examples;

/// <summary>An abstract base whose slots its derived classes override: one abstract, one with a default body.</summary>
public abstract class Animal
{
    /// <summary>The number of legs; every concrete animal overrides it.</summary>
    public abstract ulong Legs();

    /// <summary>How loud the animal is; an animal that does not override it is quiet.</summary>
    public virtual ulong Loudness() => 1;
}

/// <summary>An animal that overrides both slots.</summary>
public sealed class Dog : Animal
{
    /// <summary>A dog has four legs.</summary>
    public override ulong Legs() => 4;

    /// <summary>A dog is loud.</summary>
    public override ulong Loudness() => 10;
}

/// <summary>An animal that inherits the default loudness.</summary>
public sealed class Bird : Animal
{
    /// <summary>A bird has two legs.</summary>
    public override ulong Legs() => 2;
}

/// <summary>Virtual calls whose body the receiver's runtime class selects.</summary>
public static class VirtualCalls
{
    /// <summary>The legs of any animal, through the abstract slot.</summary>
    public static ulong LegsOf(Animal animal) => animal.Legs();

    /// <summary>The loudness of any animal: an override or the inherited default.</summary>
    public static ulong LoudnessOf(Animal animal) => animal.Loudness();

    /// <summary>The legs of a fresh dog, dispatched on the instance it creates.</summary>
    public static ulong DogLegs() => new Dog().Legs();
}

/// <summary>Type tests that an instance's class lineage decides.</summary>
public static class ClassTests
{
    /// <summary>Whether the animal is a dog; null is not.</summary>
    public static bool IsDog(Animal animal) => animal is Dog;

    /// <summary>The animal as a dog; any other animal throws InvalidCastException, and null stays null.</summary>
    public static Dog AsDog(Animal animal) => (Dog)animal;
}
