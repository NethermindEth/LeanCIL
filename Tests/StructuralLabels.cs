#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

// One proof file, unedited, must verify against two builds of a method with two loops and
// two calls to one helper; the second inserts a statement before the first loop.
using var verification = new Program();
var root = At("artifacts/StructuralLabels");
const string Selector = "Calls::Root(uint,uint)";

string Build(string name, string inserted)
{
    var source = Path.Combine(root, name);
    Directory.CreateDirectory(source);
    File.WriteAllText(Path.Combine(source, "Labels.csproj"), """
    <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
    """);
    File.WriteAllText(Path.Combine(source, "Labels.cs"), "namespace Labels; public static class Calls { " +
        "public static uint Step(uint x) => x + 1; " +
        "public static uint Root(uint x, uint y) { x = Step(x); " + inserted +
        "while (y != 0) { y--; } while (x > 100) { x -= 3; } return Step(x); } }");
    Run(["dotnet", "build", Path.Combine(source, "Labels.csproj"), "-c", "Release"]);
    return Path.Combine(source, "bin/Labels.dll");
}

var original = Build("Original", "");
var inserted = Build("Inserted", "y ^= x; ");

string Proof(string name, string bindings, string count, string countLatch, string reduce, string reduceLatch, string after, string callee)
{
    var path = Path.Combine(root, name + ".lean");
    File.WriteAllText(path, $$"""
    import Extracted
    import CIL.StructuralLabels

    open CIL
    namespace ExampleProof

    bind_method root rootBody := "System.UInt32 Labels.Calls::Root(System.UInt32,System.UInt32)"
    {{bindings}}

    -- Each loop body and back edge, and the final call, stated at its label.
    theorem correctness :
        (rootBody.code.drop {{count}}).take 4 = [.local 1, .const32 1, .sub, .setLocal 1] ∧
        rootBody.code[{{countLatch}}]? = some (.brnonzero {{count}}) ∧
        (rootBody.code.drop {{reduce}}).take 4 = [.local 0, .const32 3, .sub, .setLocal 0] ∧
        rootBody.code[{{reduceLatch}}]? = some (.bgtu {{reduce}}) ∧
        (rootBody.code.drop {{after}}).take 2 = [.call {{callee}} 1, .ret] :=
      ⟨rfl, rfl, rfl, rfl, rfl⟩

    end ExampleProof
    """);
    return path;
}

var labelled = Proof("Labelled", """
    bind_callee step stepBody := "System.UInt32 Labels.Calls::Step(System.UInt32)" from rootBody [1]
    bind_call after := step from rootBody [1]
    bind_loop count := rootBody [0]
    bind_loop reduce := rootBody [1]
    """, "count", "count.latch", "reduce", "reduce.latch", "after", "step");
foreach (var (name, assembly) in new[] { ("Original", original), ("Inserted", inserted) })
{
    verification.Verify(assembly, "Labels", Selector, labelled, Path.Combine(root, name + "-Labelled"));
    Console.WriteLine($"PASS {name}: loop and call-site labels verify unedited");
}

// The same claims at the original pcs hold there and must fail once the statement is inserted.
var numbered = Proof("Numbered", "", "4", "9", "11", "17", "19", "1");
verification.Verify(original, "Labels", Selector, numbered, Path.Combine(root, "Original-Numbered"));
var failed = false;
try
{
    verification.Verify(inserted, "Labels", Selector, numbered, Path.Combine(root, "Inserted-Numbered"));
}
catch (InvalidOperationException error) when (error.Message.Contains("rfl"))
{
    failed = true;
}
if (!failed) throw new InvalidOperationException("Pc-numbered claims survived the insertion; the fixture does not move the loops.");
Console.WriteLine("PASS pc-numbered claims break on insertion; structural labels do not");
