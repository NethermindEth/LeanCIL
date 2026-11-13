#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BindingImage.cs
#:include StrictBindingFacts.cs
#:include MultiAssemblyFixture.cs

// Builds the small library the strict binding Lean tests decode and writes Tests/StrictBinding/Fixture.lean
// from it with `--update`; without it, checks that the checked-in module still holds a consistent image.
const string librarySource = """
using System;
using System.Runtime.InteropServices;
[assembly: System.Reflection.AssemblyVersion("1.2.3.4")]
namespace StrictFixture;
public enum Small : byte { A = 1, B = 5 }
[StructLayout(LayoutKind.Explicit, Size = 8)]
public struct Overlay { [FieldOffset(0)] public int Low; [FieldOffset(4)] public int High; }
public static class Arithmetic
{
    public static int Tiny(int x) => x + 1;
    public static int Fat(int x) { int a = x * 3; int b = a - 7; if (b > 100) b = 100; return b; }
    public static ReadOnlySpan<byte> Table => new byte[] { 1, 2, 3, 4, 5, 6, 7, 8 };
}
public class Shape { public virtual int Sides() => 0; public static int Count(Shape shape) => shape.Sides(); }
public class Triangle : Shape { public override int Sides() => 3; }
public class Square : Shape { public override int Sides() => 4; }
""";

string module = At("Tests/StrictBinding/Fixture.lean");
if (args is ["--update"])
{
    MultiAssemblyFixture fixture = new("StrictBindingFixture");
    string dll = fixture.Build("Fixture", "StrictFixture", librarySource,
        "<DebugType>none</DebugType><GenerateAssemblyInfo>false</GenerateAssemblyInfo>");
    byte[] built = File.ReadAllBytes(dll);
    Directory.CreateDirectory(Path.GetDirectoryName(module)!);
    File.WriteAllText(module, StrictBindingFacts.Module(built), new System.Text.UTF8Encoding(false));
    Console.WriteLine($"Wrote {module}: {built.Length} bytes, SHA-256 {BindingImage.Digest(built)}");
    return;
}
if (args.Length != 0) throw new ArgumentException("Usage: StrictBindingFixture.cs [--update]");
string checkedIn = File.ReadAllText(module);
byte[] image = StrictBindingFacts.ReadImage(checkedIn);
if (StrictBindingFacts.Module(image) != checkedIn.ReplaceLineEndings("\n"))
    throw new InvalidOperationException($"{module} is not what its image generates; run with --update.");
Console.WriteLine($"PASS strict binding fixture module is consistent: {image.Length} bytes, " +
    $"SHA-256 {BindingImage.Digest(image)}");
