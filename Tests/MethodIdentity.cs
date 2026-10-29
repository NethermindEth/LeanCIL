#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.RegularExpressions;

// One proof file, unedited, must verify against two builds whose extraction numbering differs:
// the second declares the helpers in the other order and adds a helper that renumbers both.
// A shape-bound proof must also survive a third build that renames both helpers.
using var verification = new Program();
var root = At("artifacts/MethodIdentity");
const string Selector = "Calls::Root(ulong,ulong)";
const string Left = "System.UInt64 Identity.Calls::Left(System.UInt64,System.UInt64)";
const string Right = "System.UInt64 Identity.Calls::Right(System.UInt64,System.UInt64)";

string Build(string name, string body)
{
    var source = Path.Combine(root, name);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Identity.csproj"), """
    <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
    """);
    File.WriteAllText(Path.Combine(source, "Identity.cs"), "namespace Identity; public static class Calls { " + body + " }");
    Run(["dotnet", "build", Path.Combine(source, "Identity.csproj"), "-c", "Release"]);
    return Path.Combine(source, "bin/Identity.dll");
}

var original = Build("Original",
    "public static ulong Left(ulong x, ulong y) => x - y; " +
    "public static ulong Right(ulong x, ulong y) => x ^ y; " +
    "public static ulong Root(ulong x, ulong y) => Right(x, y) + Left(x, y);");
var reordered = Build("Reordered",
    "public static ulong Bias(ulong x) => x; " +
    "public static ulong Right(ulong x, ulong y) => x ^ y; " +
    "public static ulong Left(ulong x, ulong y) => x - y; " +
    "public static ulong Root(ulong x, ulong y) => Right(x, y) + Bias(Left(x, y));");
var renamed = Build("Renamed",
    "public static ulong Bias(ulong x) => x; " +
    "public static ulong Exclusive(ulong x, ulong y) => x ^ y; " +
    "public static ulong Difference(ulong x, ulong y) => x - y; " +
    "public static ulong Root(ulong x, ulong y) => Exclusive(x, y) + Bias(Difference(x, y));");

Dictionary<string, int> Indices(string assembly, string name)
{
    var folder = Path.Combine(root, name + "-Extraction");
    Run(Extract("extract", assembly, "Identity", Selector, folder));
    var extracted = File.ReadAllText(Path.Combine(folder, "Extracted.lean"));
    return Regex.Matches(extracted, @"(?m)^def method(\d+)Signature : String := ""([^""]+)""")
        .ToDictionary(m => m.Groups[2].Value, m => int.Parse(m.Groups[1].Value));
}
var before = Indices(original, "Original");
var after = Indices(reordered, "Reordered");
if (before[Left] == after[Left] || before[Right] == after[Right])
    throw new InvalidOperationException("The reordered build did not renumber the helpers; the suite would prove nothing.");

string Proof(string name, string bindings, string left, string right, string parent)
{
    var path = Path.Combine(root, name + ".lean");
    File.WriteAllText(path, $$"""
    import Extracted
    import CIL.MethodIdentity
    import CIL.Safety.Execution

    open CIL
    namespace ExampleProof

    {{bindings}}

    theorem correctness (x y : W64) (memory : Safety.Memory) :
        Safety.invoke Extracted.program 4 {{left}} [.scalar (.i64 x), .scalar (.i64 y)] memory =
          .ok (memory, [.scalar (.i64 (x - y))]) ∧
        Safety.invoke Extracted.program 4 {{right}} [.scalar (.i64 x), .scalar (.i64 y)] memory =
          .ok (memory, [.scalar (.i64 (x ^^^ y))]) ∧
        Safety.invoke Extracted.program 32 {{parent}} [.scalar (.i64 x), .scalar (.i64 y)] memory =
          .ok (memory, [.scalar (.i64 ((x ^^^ y) + (x - y)))]) := by
      exact ⟨rfl, rfl, rfl⟩

    #print axioms correctness

    end ExampleProof
    """);
    return path;
}

var named = Proof("Named", $"""
    bind_method parent parentBody := "System.UInt64 Identity.Calls::Root(System.UInt64,System.UInt64)"
    bind_callee left leftBody := "{Left}" from parentBody
    bind_callee right rightBody := "{Right}" from parentBody
    """, "left", "right", "parent");
foreach (var (name, assembly) in new[] { ("Original", original), ("Reordered", reordered) })
{
    verification.Verify(assembly, "Identity", Selector, named, Path.Combine(root, name + "-Named"));
    Console.WriteLine($"PASS {name}: signature-bound proof verifies unedited");
}

// Calls with two arguments, in call order: the inserted one-argument helper is not a candidate.
var shaped = Proof("Shaped", """
    bind_method parent parentBody := "System.UInt64 Identity.Calls::Root(System.UInt64,System.UInt64)"
    bind_callee right rightBody := call 2 from parentBody [0]
    bind_callee left leftBody := call 2 from parentBody [1]
    """, "left", "right", "parent");
foreach (var (name, assembly) in new[] { ("Original", original), ("Reordered", reordered), ("Renamed", renamed) })
{
    verification.Verify(assembly, "Identity", Selector, shaped, Path.Combine(root, name + "-Shaped"));
    Console.WriteLine($"PASS {name}: shape-bound proof verifies unedited");
}
var unnamed = false;
try
{
    verification.Verify(renamed, "Identity", Selector, named, Path.Combine(root, "Renamed-Named"));
}
catch (InvalidOperationException error) when (error.Message.Contains("no extracted method has signature"))
{
    unnamed = true;
}
if (!unnamed) throw new InvalidOperationException("A signature-bound proof survived renaming; the renamed build does not exercise shape binding.");
Console.WriteLine("PASS signatures break on renaming; call shape does not");

// The positional proof that held for the original build must fail once helpers are renumbered.
var numbered = Proof("Numbered", "", before[Left].ToString(), before[Right].ToString(), "0");
verification.Verify(original, "Identity", Selector, numbered, Path.Combine(root, "Original-Numbered"));
var failed = false;
try
{
    verification.Verify(reordered, "Identity", Selector, numbered, Path.Combine(root, "Reordered-Numbered"));
}
catch (InvalidOperationException error) when (error.Message.Contains("rfl"))
{
    failed = true;
}
if (!failed) throw new InvalidOperationException("A positional proof survived renumbering; the reordered build does not exercise identity.");
Console.WriteLine("PASS positional indices break on renumbering; signatures do not");
