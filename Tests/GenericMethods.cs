#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var fsharp = At("Examples/FSharp/bin/Examples.FSharp.dll");
var root = At("artifacts/GenericMethods");
Directory.CreateDirectory(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.GenericMethods")!;
var comparisons = 0;

string LeanValue(object value) => value switch
{
    bool x => $".scalar (.i32 {(x ? 1 : 0)})",
    byte x => $".scalar (.i32 {x})",
    int x => $".scalar (.i32 {unchecked((uint)x)})",
    uint x => $".scalar (.i32 {x})",
    ulong x => $".scalar (.i64 {x})",
    nint x => $".scalar (.i64 {unchecked((ulong)x)})",
    Enum x => $".scalar (.i32 {unchecked((uint)Convert.ToInt32(x))})",
    _ => throw new InvalidOperationException("Unexpected value")
};

object[] Values(Type type) => type == typeof(bool) ? [false, true] :
    type == typeof(byte) ? [(byte)0, (byte)1, byte.MaxValue] :
    type == typeof(int) ? [0, 1, -1, int.MinValue, int.MaxValue] :
    type == typeof(uint) ? [0U, 1U, uint.MaxValue, 0x80000000U] :
    type == typeof(ulong) ? [0UL, 1UL, ulong.MaxValue, 1UL << 63] :
    type == typeof(nint) ? [(nint)0, (nint)1, nint.MinValue, nint.MaxValue] :
    type.IsEnum ? new object[] { Enum.ToObject(type, 0), Enum.ToObject(type, -1), Enum.ToObject(type, 127), Enum.ToObject(type, -128) } :
    throw new InvalidOperationException("Unexpected parameter type");

// Universal contracts cover direct, repeated, nested and instance generic calls.
foreach (var method in new[] { "Identity64", "Repeated", "Nested" })
    verification.Verify(assembly, "Examples", $"GenericMethods::{method}(ulong)",
        At("Examples/Proofs/GenericIdentity.lean"), Path.Combine(root, method));
// The instance wrapper allocates a receiver; retain its separate fixed-memory check.
verification.Verify(assembly, "Examples", "GenericMethods::Instance(ulong)",
    At("Examples/Proofs/GenericInstance.lean"), Path.Combine(root, "Instance"));
verification.Verify(assembly, "Examples", "GenericMethods::Identity32(int)",
    At("Examples/Proofs/GenericIdentity32.lean"), Path.Combine(root, "Identity32"));
verification.Verify(fsharp, "Examples.FSharp", "GenericMethods::Identity64(ulong)",
    At("Examples/Proofs/GenericIdentity.lean"), Path.Combine(root, "FSharpIdentity"));

// Independent runtime results cover branches, several instantiations and aggregate storage.
foreach (var (dll, identity, owner, names) in new[]
{
    (assembly, "Examples", runtime, new[] { "Mixed", "Select", "PackedSize", "VectorSize", "EnumIdentity", "NativeIdentity", "TwoTypes", "SwapPacked", "ClearPacked" }),
    (fsharp, "Examples.FSharp", Assembly.Load(File.ReadAllBytes(fsharp)).GetType("Examples.FSharp.GenericMethods")!, new[] { "Select" })
})
foreach (var name in names)
{
    var method = owner.GetMethod(name)!;
    var parameters = method.GetParameters();
    var inputs = new List<object[]> { Array.Empty<object>() };
    foreach (var parameter in parameters)
        inputs = inputs.SelectMany(previous => Values(parameter.ParameterType).Select(value => previous.Append(value).ToArray())).ToList();
    var claims = inputs.Select(input =>
        $"(CIL.Safety.invoke Extracted.program 64 0 [{string.Join(", ", input.Select(LeanValue))}] Examples.empty).map Prod.snd = .ok [{LeanValue(method.Invoke(null, input)!)}]").ToList();
    var output = Path.Combine(root, identity + "-" + name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 8192\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by\n  exact " + (claims.Count == 1 ? "rfl" : "⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩") + "\nend ExampleProof\n");
    verification.Verify(dll, identity, $"GenericMethods::{name}({string.Join(",", parameters.Select(p => p.ParameterType.FullName))})", proof, output);
    comparisons += claims.Count;
    Console.WriteLine($"PASS {identity} {name}: {claims.Count} runtime comparisons");
}

// Generic loads and reference offsets retain checked memory behaviour.
foreach (var name in new[] { "Read32", "NextPacked" })
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "BoundaryProof.lean");
    var claims = name == "Read32"
        ? new[] { 0U, 1U, uint.MaxValue, 0x80000000U }.Select(value =>
            $"(CIL.Safety.invoke Extracted.program 16 0 [Examples.reference] {{ Examples.caller with cells := fun _ i => ⟨BitVec.ofNat 8 ({value} / 256^i), true⟩ }}).map Prod.snd = .ok [.scalar (.i32 {value})]").ToList()
        : new List<string>
        {
            "(CIL.Safety.invoke Extracted.program 16 0 [Examples.reference, .scalar (.i32 1)] Examples.caller).map Prod.snd = .ok [.reference (.address ⟨0, 5⟩)]",
            "((CIL.Safety.invoke Extracted.program 16 0 [Examples.reference, .scalar (.i32 2)] Examples.caller).map (fun _ => false)).mapError (fun f => match f.fault with | .memory .invalidReference _ _ => true | _ => false) = .error true"
        };
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    verification.Verify(assembly, "Examples", name == "Read32" ? "GenericMethods::Read32(int&)" : "GenericMethods::NextPacked(Examples.PackedLeaf&,int)", proof, output);
    Console.WriteLine($"PASS {name}: {claims.Count} reference checks");
}

// Distinct instantiations remain distinct, while repeated calls share one closed body.
foreach (var (directory, expected) in new[] { ("Repeated", 2), ("Nested", 3), ("Examples-Mixed", 3) })
{
    using var identity = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, directory, "identity.json")));
    var methods = identity.RootElement.GetProperty("methods");
    if (methods.GetArrayLength() != expected || methods.EnumerateArray().Skip(1).Any(method =>
        method.GetProperty("specialization").ValueKind == JsonValueKind.Null ||
        method.GetProperty("specialization").GetProperty("TypeArguments").GetArrayLength() != 1 ||
        method.GetProperty("token").GetInt32() == 0))
        throw new InvalidOperationException("Missing or duplicated generic provenance: " + directory);
}

var wrong = Path.Combine(root, "WrongIdentity");
var rejected = false;
try
{
    verification.Verify(assembly, "Examples", "GenericMethods::WrongIdentity(int)",
        At("Examples/Proofs/GenericIdentity32.lean"), wrong);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    rejected = true;
}
if (!rejected || File.Exists(Path.Combine(wrong, "verified.json")))
    throw new InvalidOperationException("Wrong generic implementation accepted");

// Reject unsupported constraints, signatures, bodies and type arguments explicitly.
foreach (var mutation in new[] { "class", "float", "byref", "arity", "return", "constraint", "flags", "constraint-encoding", "interface", "boxing", "array-local", "recursion" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    File.Delete(Path.Combine(output, "Extracted.lean"));
    File.Delete(Path.Combine(output, "identity.json"));
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var owner = module.GetType("Examples.GenericMethods");
        var caller = owner.Methods.Single(m => m.Name == "Identity32");
        var call = (GenericInstanceMethod)caller.Body.Instructions.Single(i => i.OpCode.Code == Code.Call).Operand;
        var definition = call.Resolve();
        switch (mutation)
        {
            case "class": call.GenericArguments[0] = module.TypeSystem.String; break;
            case "float": call.GenericArguments[0] = module.TypeSystem.Double; break;
            case "byref": call.GenericArguments[0] = new ByReferenceType(module.TypeSystem.Int32); break;
            case "arity": call.GenericArguments.Add(module.TypeSystem.Int32); break;
            case "return": call.ReturnType = module.TypeSystem.Int64; break;
            case "constraint": definition.GenericParameters[0].Attributes = Mono.Cecil.GenericParameterAttributes.ReferenceTypeConstraint; break;
            case "flags": definition.GenericParameters[0].Attributes = (Mono.Cecil.GenericParameterAttributes)0x80; break;
            case "constraint-encoding":
                definition.GenericParameters[0].Constraints.Add(new GenericParameterConstraint(new RequiredModifierType(
                    new TypeReference("System.Runtime.InteropServices", "UnmanagedType", module, module.TypeSystem.Int32.Scope),
                    new TypeReference("System", "ValueType", module, module.TypeSystem.Int32.Scope, true))));
                break;
            case "interface": definition.GenericParameters[0].Constraints.Add(new GenericParameterConstraint(new TypeReference("System", "IComparable", module, module.TypeSystem.Int32.Scope))); break;
            case "boxing": definition.Body.GetILProcessor().InsertBefore(definition.Body.Instructions.Last(), Instruction.Create(OpCodes.Box, definition.GenericParameters[0])); break;
            case "array-local": definition.Body.Variables.Add(new VariableDefinition(new ArrayType(definition.GenericParameters[0]))); break;
        }
        module.Write(dll);
    }
    var selector = mutation == "recursion" ? "GenericMethods::RejectRecursion(int)" : "GenericMethods::Identity32(int)";
    var result = Execute(Extract("extract", dll, "Examples", selector, output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !(result.Output.Contains("Unsupported") || result.Output.Contains("Unresolved") || result.Output.Contains("Recursive")))
        throw new InvalidOperationException("Incorrect generic rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}

// Provenance participates in regeneration-based artifact identity checks.
var provenance = Path.Combine(root, "Identity32", "identity.json");
var original = File.ReadAllText(provenance);
var changed = System.Text.Json.Nodes.JsonNode.Parse(original)!;
var format = new JsonSerializerOptions { WriteIndented = true };
if (changed.ToJsonString(format) != original)
    throw new InvalidOperationException("Provenance test must preserve manifest formatting");
changed["methods"]![1]!["specialization"]!["TypeArguments"]![0] = "System.UInt32";
File.WriteAllText(provenance, changed.ToJsonString(format));
var check = Execute(Extract("check", assembly, "Examples", "GenericMethods::Identity32(int)", Path.Combine(root, "Identity32")));
File.WriteAllText(provenance, original);
if (check.Code == 0 || !check.Output.Contains("Stale or mismatched"))
    throw new InvalidOperationException("Modified generic provenance accepted");

Console.WriteLine($"PASS {comparisons} generic runtime comparisons, six universal proofs, provenance and negative tests");
