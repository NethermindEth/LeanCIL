#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/UnsafeLayouts");
Directory.CreateDirectory(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.UnsafeLayouts")!;
using var source = ModuleDefinition.ReadModule(assembly);
var owner = source.GetType("Examples.UnsafeLayouts");
var cases = 0;

void Prove(MethodDefinition method, List<string> claims, string definitions = "")
{
    var output = Path.Combine(root, method.Name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + definitions +
        "\ntheorem correctness :\n" + string.Join(" ∧\n", claims) + " := by\n  exact " +
        (claims.Count == 1 ? "rfl" : "⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩") + "\nend ExampleProof\n");
    verification.Verify(assembly, "Examples", method.FullName, proof, output);
    cases += claims.Count;
    Console.WriteLine($"PASS {method.Name}: {claims.Count} checks");
}

// Sizes come from .NET's managed layout, including packed/nested structs and vectors.
foreach (var method in owner.Methods.Where(m => m.Name.StartsWith("Size", StringComparison.Ordinal)))
{
    var size = (int)runtime.GetMethod(method.Name)!.Invoke(null, null)!;
    Prove(method, [$"(CIL.Safety.invoke Extracted.program 8 0 [] Examples.empty).map Prod.snd = .ok [.scalar (.i32 {size})]"]);
}

// Runtime byte offsets and Lean references must agree for each element type and offset overload.
foreach (var method in owner.Methods.Where(m => m.Name.StartsWith("Add", StringComparison.Ordinal)))
{
    var suffix = method.Name[3..];
    var index = new string(suffix.TakeWhile(char.IsDigit).ToArray());
    var size = (int)runtime.GetMethod("Size" + index)!.Invoke(null, null)!;
    var measure = runtime.GetMethod("Measure" + suffix)!;
    var type = measure.GetParameters()[0].ParameterType;
    var stackWidth = type == typeof(int) ? 32 : 64;
    var claims = new List<string>();
    var memory = $"def memory : CIL.Safety.Memory := {{ Examples.empty with\n" +
        $"  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨{size * 4}, 1, []⟩, true, [{size * 4}]⟩ else none\n" +
        $"  nextIdentity := 1 }}\n";
    foreach (var count in new[] { 0, 1, 3, 4 })
    {
        object value = type == typeof(int) ? count : type == typeof(nint) ? (object)(nint)count : (nuint)count;
        var offset = (long)measure.Invoke(null, [value])!;
        claims.Add($"(CIL.Safety.invoke Extracted.program 8 0 [Examples.reference, .scalar (.i{stackWidth} {count})] memory).map Prod.snd = .ok [.reference (.address ⟨0, {offset}⟩)]");
    }

    object backwards = type == typeof(int) ? -1 : type == typeof(nint) ? (object)(nint)(-1) : nuint.MaxValue;
    var backwardsOffset = (long)measure.Invoke(null, [backwards])!;
    var backwardsBits = stackWidth == 32 ? uint.MaxValue : ulong.MaxValue;
    claims.Add($"(CIL.Safety.invoke Extracted.program 8 0 [.reference (.address ⟨0, {size * 2}⟩), .scalar (.i{stackWidth} {backwardsBits})] memory).map Prod.snd = .ok [.reference (.address ⟨0, {size * 2 + backwardsOffset}⟩)]");

    // Forming an address beyond the allocation fails before any dereference.
    claims.Add($"(CIL.Safety.invoke Extracted.program 8 0 [Examples.reference, .scalar (.i{stackWidth} 5)] memory).map Prod.snd = .error ⟨0, 2, .memory .invalidReference (.address ⟨0, 0⟩) 0⟩");
    claims.Add($"(CIL.Safety.invoke Extracted.program 8 0 [.reference .null, .scalar (.i{stackWidth} 0)] memory).map Prod.snd = .error ⟨0, 2, .memory .nullDereference .null 0⟩");
    Prove(method, claims, memory);
}

// Reject malformed generic signatures and element types before emitting any Lean.
foreach (var mutation in new[] { "class", "float", "void", "byref", "pointer", "arity", "offset", "return", "scope", "version" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.UnsafeLayouts").Methods.Single(m => m.Name == "Add14int");
        var call = (GenericInstanceMethod)method.Body.Instructions.Single(i => i.Operand is MethodReference).Operand;
        switch (mutation)
        {
            case "class": call.GenericArguments[0] = module.TypeSystem.String; break;
            case "float": call.GenericArguments[0] = module.TypeSystem.Single; break;
            case "void": call.GenericArguments[0] = module.TypeSystem.Void; break;
            case "byref": call.GenericArguments[0] = new ByReferenceType(module.TypeSystem.Int32); break;
            case "pointer": call.GenericArguments[0] = new PointerType(module.TypeSystem.Int32); break;
            case "arity": call.GenericArguments.Add(module.TypeSystem.Int32); break;
            case "offset": call.Parameters[1].ParameterType = module.TypeSystem.Int64; break;
            case "return": call.ReturnType = new ByReferenceType(module.TypeSystem.Int32); break;
            case "scope": call.DeclaringType.Scope = module; break;
            case "version": ((AssemblyNameReference)call.DeclaringType.Scope).Version = new Version(9, 0, 0, 0); break;
        }
        module.Write(dll);
    }
    var result = Execute(Extract("extract", dll, "Examples", "UnsafeLayouts::Add14int(Examples.PackedLeaf&,int)", output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !(result.Output.Contains("Unsupported") || result.Output.Contains("Unmodelled") || result.Output.Contains("Unresolved")))
        throw new InvalidOperationException("Incorrect Unsafe rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}

Console.WriteLine($"PASS {cases} layout-based Unsafe checks");
