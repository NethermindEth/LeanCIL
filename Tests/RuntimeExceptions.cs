#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;

using Program verification = new();
string root = At("artifacts/RuntimeExceptions");
Directory.CreateDirectory(root);
File.WriteAllText(Path.Combine(root, "RuntimeFaults.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><Optimize>true</Optimize></PropertyGroup></Project>
""");
File.WriteAllText(Path.Combine(root, "RuntimeFaults.cs"), """
namespace RuntimeFaults;
public static class Cases
{
    public static int Add(int left, int right) => checked(left + right);
    public static int Subtract(int left, int right) => checked(left - right);
    public static int Multiply(int left, int right) => checked(left * right);
    public static byte Convert(int value) => checked((byte)value);
    public static uint Divide(uint left, uint right) => left / right;
    public static uint Remainder(uint left, uint right) => left % right;
    public static int SignedDivide(int left, int right) => left / right;
    public static int SignedRemainder(int left, int right) => left % right;
}
""");
Run(["dotnet", "build", Path.Combine(root, "RuntimeFaults.csproj"), "-c", "Release"]);
string assembly = Path.Combine(root, "bin/RuntimeFaults.dll");
Assembly runtimeAssembly = Assembly.Load(File.ReadAllBytes(assembly));
Type runtimeType = runtimeAssembly.GetType("RuntimeFaults.Cases")!;
var pending = new GeneratedQueue(verification, assembly, "RuntimeFaults");

(string Name, string Selector, string Values, string Fault, int Pc, object[] Inputs)[] cases = [
    ("Add", "int,int", "[.scalar (.i32 2147483647), .scalar (.i32 1)]", "overflow", 2, [int.MaxValue, 1]),
    ("Subtract", "int,int", "[.scalar (.i32 2147483648), .scalar (.i32 1)]", "overflow", 2, [int.MinValue, 1]),
    ("Multiply", "int,int", "[.scalar (.i32 2147483647), .scalar (.i32 2)]", "overflow", 2, [int.MaxValue, 2]),
    ("Convert", "int", "[.scalar (.i32 256)]", "overflow", 1, [256]),
    ("Divide", "uint,uint", "[.scalar (.i32 7), .scalar (.i32 0)]", "divideByZero", 2, [7U, 0U]),
    ("Remainder", "uint,uint", "[.scalar (.i32 7), .scalar (.i32 0)]", "divideByZero", 2, [7U, 0U]),
    ("SignedDivide", "int,int", "[.scalar (.i32 2147483648), .scalar (.i32 4294967295)]", "overflow", 2, [int.MinValue, -1]),
    ("SignedRemainder", "int,int", "[.scalar (.i32 2147483648), .scalar (.i32 4294967295)]", "overflow", 2, [int.MinValue, -1])
];

foreach ((string name, string selector, string values, string fault, int pc, object[] inputs) in cases)
{
    string exception = fault == "overflow" ? "System.OverflowException" : "System.DivideByZeroException";
    string wrong = fault == "overflow" ? "System.DivideByZeroException" : "System.OverflowException";
    bool observed = false;
    try
    {
        runtimeType.GetMethod(name)!.Invoke(null, inputs);
    }
    catch (TargetInvocationException error) when (error.InnerException?.GetType().FullName == exception)
    {
        observed = true;
    }
    if (!observed) throw new InvalidOperationException($"{name} did not raise {exception}");

    string proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, $$"""
import Extracted
import CIL.Safety.RuntimeExceptions
open CIL.Safety
namespace ExampleProof
def contract (exception : String) : OutcomeContract Unit where
  args _ := {{values}}
  pre _ _ := True
  footprint _ := []
  post _ _ _ _ := False
  raises _ _ := some exception
def empty : Memory := {
  allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }
theorem invoked (memory : Memory) : invoke Extracted.program 4 0 {{values}} memory =
    .error ⟨0, {{pc}}, .arithmetic .{{fault}}⟩ := rfl
theorem correctness :
    (contract "{{exception}}").HoldsCLR Extracted.program 0 ∧
    ¬ (contract "{{wrong}}").HoldsCLR Extracted.program 0 := by
  constructor
  · intro _ memory _
    exact ⟨4, ⟨0, {{pc}}, .arithmetic .{{fault}}⟩, invoked memory, rfl⟩
  · intro holds
    have raised := holds.raising (input := ()) (initial := empty) trivial rfl
    exact RaisesCLR.not_of_invoke (by simp [Settled]) (invoked empty) (by decide) raised
end ExampleProof
""");
    pending.Add(new GeneratedVerification($"Cases::{name}({selector})", proof, Path.Combine(root, name)),
        () => Console.WriteLine($"PASS {name}: runtime type, named contract and wrong-type refutation"));
}
pending.Flush();
