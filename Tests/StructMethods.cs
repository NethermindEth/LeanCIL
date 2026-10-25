#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/StructMethods");
Directory.CreateDirectory(root);
var queue = new GeneratedQueue(verification, assembly);
var cases = 0;

void Compare(string dll, string name, string suffix = "")
{
    var method = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.StructMethods")!.GetMethod(name)!;
    var output = Path.Combine(root, name + suffix);
    Directory.CreateDirectory(output);
    var narrow = name == "Narrow";
    var width = narrow ? 32 : 64;
    var claims = new List<string>();
    foreach (var bits in new ulong[] { 0, 1, 127, 128, 254, 255, 65535, uint.MaxValue, 1UL << 32, long.MaxValue, 1UL << 63, ulong.MaxValue })
    {
        object value = narrow ? (object)unchecked((byte)bits) : bits;
        var expected = method.Invoke(null, [value])!;
        claims.Add($"(CIL.Safety.invoke Extracted.program 128 0 [.scalar (.i{width} {value})] Examples.empty).map Prod.snd = .ok [.scalar (.i{width} {expected})]");
    }
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 8192\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    queue.Add(new($"StructMethods::{name}({(narrow ? "byte" : "ulong")})", proof, output, Assembly: dll), () =>
    {
        cases += claims.Count;
        Console.WriteLine($"PASS {name}{suffix}: {claims.Count} runtime comparisons");
    });
}

// Mutating this, copying values, multiple argument indices and narrow parameter homes.
foreach (var name in new[] { "Mutate", "ByValue", "Arguments", "Replace", "Narrow", "ConstructLocal" })
    Compare(assembly, name);

// Exercise explicit full/short argument operands, including Cecil's implicit this parameter.
foreach (var shortForm in new[] { false, true })
{
    var output = Path.Combine(root, "Encoding-" + shortForm);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Counter").Methods.Single(m => m.Name == "Mix");
        foreach (var instruction in method.Body.Instructions)
        {
            var index = instruction.OpCode.Code switch
            {
                Code.Ldarg_0 => 0, Code.Ldarg_1 => 1, Code.Ldarg_2 => 2, Code.Ldarg_3 => 3,
                Code.Ldarg or Code.Ldarg_S => ((ParameterDefinition)instruction.Operand).Index + 1,
                _ => -1
            };
            if (index < 0) continue;
            instruction.OpCode = shortForm ? OpCodes.Ldarg_S : OpCodes.Ldarg;
            instruction.Operand = index == 0 ? method.Body.ThisParameter : method.Parameters[index - 1];
        }
        module.Write(dll);
    }
    Compare(dll, "Arguments", "-" + shortForm);
}

queue.Flush();

var contract = At("Examples/Proofs/InstanceWriteRead.lean");
verification.Verify(assembly, "Examples", "Counter::WriteRead(ulong)", contract, Path.Combine(root, "UniversalWriteRead"));
var wrongOutput = Path.Combine(root, "WrongWriteRead");
var failed = false;
try
{
    verification.Verify(assembly, "Examples", "Counter::WrongWriteRead(ulong)", contract, wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    failed = true;
}
if (!failed || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Incorrect instance mutation accepted");

// Invalid call metadata must not be mistaken for an instance or static invocation.
foreach (var mutation in new[] { "static-call", "explicit-this", "class", "constructor-return" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var type = module.GetType("Examples.Counter");
        var entry = module.GetType("Examples.StructMethods").Methods.Single(m => m.Name == "ConstructLocal");
        var constructor = type.Methods.Single(m => m.Name == ".ctor");
        switch (mutation)
        {
            case "static-call":
                var call = (MethodReference)entry.Body.Instructions.First(i => i.OpCode.Code == Code.Call).Operand;
                call.HasThis = false;
                break;
            case "explicit-this": constructor.ExplicitThis = true; break;
            case "class": type.BaseType = module.TypeSystem.Object; break;
            case "constructor-return": constructor.ReturnType = module.TypeSystem.Int32; break;
        }
        module.Write(dll);
    }
    var result = Execute(Extract("extract", dll, "Examples", "StructMethods::ConstructLocal(ulong)", output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException($"Invalid instance metadata accepted: {mutation}\n{result.Output}");
}

Console.WriteLine($"PASS {cases} instance-call runtime comparisons, universal mutation proof and metadata rejections");
