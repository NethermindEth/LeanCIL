#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Numerics;
using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Arguments");
Directory.CreateDirectory(root);
var cases = 0;
var queue = new GeneratedQueue(verification, assembly);

void Prove(string dll, string selector, string name, IEnumerable<string> statements)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var claims = statements.ToArray();
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 4096\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) + " := by\n  exact " +
        (claims.Length == 1 ? "rfl" : "⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩") + "\nend ExampleProof\n");
    queue.Add(new(selector, proof, output, Assembly: dll), () =>
    {
        cases += claims.Length;
        Console.WriteLine($"PASS {name}: {claims.Length} cases");
    });
}

string Returns(string arguments, BigInteger result, int width = 32, string memory = "Examples.empty") =>
    $"(CIL.Safety.invoke Extracted.program 64 0 [{arguments}] ({memory})).map Prod.snd = .ok [.scalar (.i{width} {result})]";

BigInteger[] Boundaries(int width) => [0, 1, 127, 128, 255, 256, 32767, 32768, 65535, 65536,
    BigInteger.One << (width - 1), (BigInteger.One << width) - 1];

verification.Verify(assembly, "Examples", "Arguments::Overwrite(uint,uint)",
    At("Examples/Proofs/ArgumentOverwrite.lean"), Path.Combine(root, "UniversalOverwrite"));

// Compiler-generated parameter assignment, addressing, aliases and managed calls.
var runtime = Assembly.Load(File.ReadAllBytes(assembly));
var owner = runtime.GetType("Examples.Arguments")!;
foreach (var name in new[] { "Alias", "Address", "CallerIsolation", "Native", "Narrow" })
{
    var method = owner.GetMethod(name)!;
    var width = name == "Native" ? 64 : 32;
    var claims = new List<string>();
    foreach (var bits in Boundaries(width))
    {
        object input;
        if (name == "Native") input = unchecked((nint)(ulong)bits);
        else if (name == "Narrow") input = (byte)(bits % 256);
        else input = (uint)bits;
        var result = method.Invoke(null, [input])!;
        var expected = result switch { nint x => (BigInteger)unchecked((ulong)x), byte x => x, uint x => x, _ => throw new InvalidOperationException() };
        claims.Add(Returns($".scalar (.i{width} {(name == "Narrow" ? bits % 256 : bits)})", expected, width));
    }
    Prove(assembly, $"Arguments::{name}({(name == "Native" ? "nint" : name == "Narrow" ? "byte" : "uint")})", name, claims);
}

// Reassigning a byref parameter changes the private root, not the caller's root.
// Two disjoint four-byte locations make an accidental write through the old root observable.
Prove(assembly, "Arguments::ReassignReference(uint&,uint&)", "ReassignReference",
[
    Returns("Examples.reference, .reference (.address ⟨0, 4⟩)", 17, memory: "Examples.caller"),
    "(CIL.Safety.invoke Extracted.program 64 0 [Examples.reference, .reference (.address ⟨0, 4⟩)] Examples.caller).map " +
        "(fun result => (result.1.cells 0 0).bits) = .ok 0"
]);
Prove(assembly, "Arguments::Struct(Examples.Packet)", "Struct", [Returns(".scalar (.aggregate (List.replicate 12 0))", 23, 64)]);

// A parameter address expires at return, for every input and every fuel budget.
var escapeOutput = Path.Combine(root, "Escape");
Directory.CreateDirectory(escapeOutput);
var escapeDll = Path.Combine(escapeOutput, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = new MethodDefinition("Escape", Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static,
        new ByReferenceType(module.TypeSystem.UInt32));
    method.Parameters.Add(new ParameterDefinition(module.TypeSystem.UInt32));
    module.GetType("Examples.Arguments").Methods.Add(method);
    var il = method.Body.GetILProcessor();
    il.Emit(OpCodes.Ldarga, method.Parameters[0]);
    il.Emit(OpCodes.Ret);
    module.Write(escapeDll);
}
var escapeProof = Path.Combine(escapeOutput, "EscapeProof.lean");
File.WriteAllText(escapeProof, """
    import Extracted
    import Examples.Support
    import CIL.Safety.FuelLemmas
    open CIL.Safety
    namespace ExampleProof
    def fault : LocatedFault := ⟨0, 1, .memory .expiredLifetime (.address ⟨0, 0⟩) 0⟩
    theorem witness (x : CIL.W32) :
        invoke Extracted.program 2 0 [.scalar (.i32 x)] Examples.empty = .error fault := rfl
    theorem correctness (x : CIL.W32) (fuel : Nat) (result : Memory × List Value) :
        invoke Extracted.program fuel 0 [.scalar (.i32 x)] Examples.empty ≠ .ok result :=
      invoke_fault_refutes_success _ 2 _ _ _ fault (by decide) (witness x) fuel result
    #print axioms correctness
    end ExampleProof
    """);
verification.Verify(escapeDll, "Examples", "Arguments::Escape(uint)", escapeProof, escapeOutput);

// Addresses of byref slots would require nested-reference storage, which is not admitted.
var rejectedOutput = Path.Combine(root, "RejectByrefAddress");
Directory.CreateDirectory(rejectedOutput);
var rejectedDll = Path.Combine(rejectedOutput, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(escapeDll))
{
    var method = module.GetType("Examples.Arguments").Methods.Single(m => m.Name == "Escape");
    method.Parameters[0].ParameterType = new ByReferenceType(module.TypeSystem.UInt32);
    module.Write(rejectedDll);
}
var rejection = Execute(Extract("extract", rejectedDll, "Examples", "Arguments::Escape(uint&)", rejectedOutput));
if (rejection.Code == 0 ||
    !rejection.Output.Contains("Address of managed-reference or array-root argument is unsupported"))
    throw new InvalidOperationException("Incorrect nested-reference rejection: " + rejection.Output);

// The unchanged universal overwrite contract rejects storing back into the wrong argument.
var wrongOutput = Path.Combine(root, "WrongOverwrite");
Directory.CreateDirectory(wrongOutput);
var wrongDll = Path.Combine(wrongOutput, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.Arguments").Methods.Single(m => m.Name == "Overwrite");
    method.Body.Instructions.Single(i => i.OpCode.Code is Code.Starg or Code.Starg_S).Operand = method.Parameters[1];
    module.Write(wrongDll);
}
var wrongRejected = false;
try
{
    verification.Verify(wrongDll, "Examples", "Arguments::Overwrite(uint,uint)",
        At("Examples/Proofs/ArgumentOverwrite.lean"), wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    wrongRejected = true;
}
if (!wrongRejected || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Incorrect argument assignment accepted");

// Exact full and short encodings, across every admitted integer storage type.
var types = new[] { "SByte", "Byte", "Boolean", "Int16", "UInt16", "Char", "Int32", "UInt32", "Int64", "UInt64", "IntPtr", "UIntPtr" };
foreach (var typeName in types)
foreach (var op in new[] { OpCodes.Starg, OpCodes.Starg_S, OpCodes.Ldarga, OpCodes.Ldarga_S })
{
    var name = typeName + "-" + op.Name.Replace('.', '_');
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    var width = typeName is "Int64" or "UInt64" or "IntPtr" or "UIntPtr" ? 64 : 32;
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var type = (TypeReference)typeof(TypeSystem).GetProperty(typeName)!.GetValue(module.TypeSystem)!;
        var stackType = width == 64 ? module.TypeSystem.UInt64 : module.TypeSystem.UInt32;
        var method = new MethodDefinition("Fixture", Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, stackType);
        method.Parameters.Add(new ParameterDefinition(type));
        method.Parameters.Add(new ParameterDefinition(stackType));
        module.GetType("Examples.Arguments").Methods.Add(method);
        var il = method.Body.GetILProcessor();
        if (op == OpCodes.Ldarga || op == OpCodes.Ldarga_S)
        {
            il.Emit(op, method.Parameters[0]);
            il.Emit(OpCodes.Ldarg_1);
            il.Emit(OpCodes.Stobj, type);
        }
        else
        {
            il.Emit(OpCodes.Ldarg_1);
            il.Emit(op, method.Parameters[0]);
        }
        il.Emit(OpCodes.Ldarg_0);
        il.Emit(width == 64 ? OpCodes.Conv_U8 : OpCodes.Conv_U4);
        il.Emit(OpCodes.Ret);
        selector = method.FullName;
        module.Write(dll);
    }
    var methodInfo = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Arguments")!.GetMethod("Fixture")!;
    var initial = Activator.CreateInstance(methodInfo.GetParameters()[0].ParameterType)!;
    var claims = new List<string>();
    foreach (var bits in Boundaries(width))
    {
        object value = width == 64 ? (object)(ulong)bits : (uint)bits;
        var result = methodInfo.Invoke(null, [initial, value])!;
        var expected = width == 64 ? (BigInteger)(ulong)result : (uint)result;
        claims.Add(Returns($".scalar (.i{width} 0), .scalar (.i{width} {bits})", expected, width));
    }
    Prove(dll, selector, name, claims);
}

queue.Flush();

Console.WriteLine($"Argument storage passed: {cases} runtime and memory cases.");
