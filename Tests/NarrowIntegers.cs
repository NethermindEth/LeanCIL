#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Numerics;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/NarrowIntegers");
Directory.CreateDirectory(root);
var cases = 0;

// A universal mathematical contract over the C# compiler's conversion output.
verification.Verify(assembly, "Examples", "NarrowIntegers::UnsignedShort(int)",
    At("Examples/Proofs/UnsignedShort.lean"), Path.Combine(root, "UnsignedShort"));

BigInteger Narrow(BigInteger value, int bits, bool signed)
{
    var modulus = BigInteger.One << bits;
    var result = value % modulus;
    return signed && result >= modulus / 2 ? result - modulus : result;
}

BigInteger[] Boundaries(int width) => [0, 1, 127, 128, 255, 256, 32767, 32768, 65535, 65536,
    (BigInteger.One << (width - 1)), (BigInteger.One << width) - 1];

void VerifyCases(string dll, string selector, string output, int inputWidth,
    Func<BigInteger, BigInteger> expected, int resultWidth = 32, string? fault = null)
{
    var claims = new List<string>();

    foreach (var value in Boundaries(inputWidth))
    {
        var execution = $"CIL.Safety.invoke Extracted.program 32 0 [.scalar (.i{inputWidth} {value})] Examples.empty";
        if (fault is not null)
        {
            claims.Add($"({execution}) = .error {fault}");
        }
        else
        {
            var modulus = BigInteger.One << resultWidth;
            var result = (expected(value) % modulus + modulus) % modulus;
            claims.Add($"({execution}).map Prod.snd = .ok [.scalar (.i{resultWidth} {result})]");
        }
    }

    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 4096\n" +
        "namespace ExampleProof\ntheorem correctness :\n  " + string.Join(" ∧\n  ", claims) +
        " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    verification.Verify(dll, "Examples", selector, proof, output);
    cases += claims.Count;
    Console.WriteLine($"PASS {Path.GetFileName(output)}: {claims.Count} cases");
}

// Exercise the compiled C# examples, including an actual call and packed fields.
foreach (var (method, width, bits, signed) in new[]
{
    ("SignedByte", 32, 8, true), ("SignedShort", 64, 16, true),
    ("UnsignedShort", 32, 16, false), ("Character", 32, 16, false),
    ("Call", 32, 16, true), ("Fields", 32, 0, false)
})
{
    var output = Path.Combine(root, "CSharp" + method);
    Directory.CreateDirectory(output);
    VerifyCases(assembly, $"NarrowIntegers::{method}({(width == 32 ? "int" : "long")})", output, width,
        value => bits == 0 ? Narrow(value, 8, true) + Narrow(value, 16, true) + 2 * Narrow(value, 16, false)
            : Narrow(value, bits, signed));
}

// Exact conversion forms, including the previously missing conv.i8 identity case.
foreach (var width in new[] { 32, 64 })
foreach (var (operation, bits, signed) in new[]
{
    (OpCodes.Conv_I1, 8, true), (OpCodes.Conv_I2, 16, true), (OpCodes.Conv_U2, 16, false),
    (OpCodes.Conv_I8, width, true)
})
{
    var output = Path.Combine(root, operation.Name.Replace('.', '_') + width);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");

    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var owner = module.GetType("Examples.NarrowIntegers");
        var resultType = operation == OpCodes.Conv_I8 ? module.TypeSystem.Int64 : module.TypeSystem.Int32;
        var fixture = new MethodDefinition("Fixture", MethodAttributes.Public | MethodAttributes.Static, resultType);
        fixture.Parameters.Add(new ParameterDefinition(width == 32 ? module.TypeSystem.Int32 : module.TypeSystem.Int64));
        owner.Methods.Add(fixture);
        fixture.Body.Instructions.Add(Instruction.Create(OpCodes.Ldarg_0));
        fixture.Body.Instructions.Add(Instruction.Create(operation));
        fixture.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
        module.Write(dll);
    }

    VerifyCases(dll, $"NarrowIntegers::Fixture({(width == 32 ? "int" : "long")})", output, width,
        value => Narrow(value, bits, signed), operation == OpCodes.Conv_I8 ? 64 : 32);
}

// These fixtures deliberately omit conv instructions so each storage boundary
// must perform its own truncation and extension. C# often inserts conversions.
foreach (var (typeName, bits, signed) in new[]
{
    ("SByte", 8, true), ("Byte", 8, false), ("Int16", 16, true),
    ("UInt16", 16, false), ("Char", 16, false), ("Boolean", 8, false)
})
foreach (var scenario in new[] { "local", "argument", "return", "call", "field", "snapshot", "uninitialized", "wide-store" })
{
    var output = Path.Combine(root, typeName + "-" + scenario);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    var inputWidth = scenario == "wide-store" ? 64 : 32;

    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var owner = module.GetType("Examples.NarrowIntegers");
        var type = typeName switch
        {
            "SByte" => module.TypeSystem.SByte, "Byte" => module.TypeSystem.Byte,
            "Int16" => module.TypeSystem.Int16, "UInt16" => module.TypeSystem.UInt16,
            "Char" => module.TypeSystem.Char, "Boolean" => module.TypeSystem.Boolean,
            _ => throw new InvalidOperationException("Missing fixture type")
        };
        var fixture = new MethodDefinition("Fixture", MethodAttributes.Public | MethodAttributes.Static,
            scenario == "return" ? type : module.TypeSystem.Int32);
        fixture.Parameters.Add(new ParameterDefinition(scenario == "argument" ? type :
            inputWidth == 64 ? module.TypeSystem.Int64 : module.TypeSystem.Int32));
        owner.Methods.Add(fixture);
        var code = fixture.Body.Instructions;
        fixture.Body.InitLocals = scenario != "uninitialized";

        if (scenario is "field" or "snapshot")
        {
            var layout = new TypeDefinition("Examples", "NarrowStorage", TypeAttributes.Sealed | TypeAttributes.ExplicitLayout,
                module.GetType("Examples.NarrowPacket").BaseType) { ClassSize = bits / 8, PackingSize = 1 };
            module.Types.Add(layout);
            var field = new FieldDefinition("Value", FieldAttributes.Public, type) { Offset = 0 };
            layout.Fields.Add(field);
            fixture.Body.Variables.Add(new VariableDefinition(layout));
            code.Add(Instruction.Create(OpCodes.Ldloca_S, fixture.Body.Variables[0]));
            code.Add(Instruction.Create(OpCodes.Ldarg_0));
            code.Add(Instruction.Create(OpCodes.Stfld, field));
            code.Add(scenario == "field" ? Instruction.Create(OpCodes.Ldloca_S, fixture.Body.Variables[0]) :
                Instruction.Create(OpCodes.Ldloc_0));
            code.Add(Instruction.Create(OpCodes.Ldfld, field));
        }
        else if (scenario is "local" or "uninitialized" or "wide-store")
        {
            fixture.Body.Variables.Add(new VariableDefinition(type));
            if (scenario != "uninitialized")
            {
                code.Add(Instruction.Create(OpCodes.Ldarg_0));
                code.Add(Instruction.Create(OpCodes.Stloc_0));
            }
            code.Add(Instruction.Create(OpCodes.Ldloc_0));
        }
        else
        {
            code.Add(Instruction.Create(OpCodes.Ldarg_0));
            if (scenario == "call")
            {
                var callee = new MethodDefinition("Callee", MethodAttributes.Static, type);
                callee.Parameters.Add(new ParameterDefinition(type));
                owner.Methods.Add(callee);
                callee.Body.Instructions.Add(Instruction.Create(OpCodes.Ldarg_0));
                callee.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
                code.Add(Instruction.Create(OpCodes.Call, callee));
            }
        }

        code.Add(Instruction.Create(OpCodes.Ret));
        module.Write(dll);
    }

    var parameter = scenario == "argument" ? "System." + typeName : inputWidth == 64 ? "long" : "int";
    var fault = scenario switch
    {
        "uninitialized" => $"⟨0, 0, .memory .uninitialized (.address ⟨0, 0⟩) {bits / 8}⟩",
        "wide-store" => "⟨0, 1, .invalidState⟩",
        _ => null
    };
    VerifyCases(dll, $"NarrowIntegers::Fixture({parameter})", output, inputWidth,
        value => Narrow(value, bits, signed), fault: fault);
}

// Two-byte layouts and narrow type identities still receive strict validation.
foreach (var mutation in new[] { "overrun", "scope" })
{
    var output = Path.Combine(root, mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    var selector = "NarrowIntegers::Fields(int)";

    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        if (mutation == "overrun")
        {
            module.GetType("Examples.NarrowPacket").Fields.Single(f => f.Name == "SignedShort").Offset = 7;
        }
        else
        {
            var fake = new AssemblyNameReference("Fake.Runtime", new Version(10, 0, 0, 0));
            module.AssemblyReferences.Add(fake);
            module.GetType("Examples.NarrowIntegers").Methods.Single(m => m.Name == "SignedByte").Parameters[0].ParameterType =
                new TypeReference("System", "SByte", module, fake, true);
            selector = "NarrowIntegers::SignedByte(sbyte)";
        }
        module.Write(dll);
    }

    var result = Execute(Extract("extract", dll, "Examples", selector, output));
    var marker = mutation == "overrun" ? "Invalid field layout" : "Unsupported type identity";
    if (result.Code == 0 || !result.Output.Contains(marker))
        throw new InvalidOperationException("Incorrect narrow metadata validation: " + result.Output);
    Console.WriteLine("PASS narrow metadata rejection: " + mutation);
}

// Signed extension cannot satisfy the unchanged unsigned modulo contract.
var incorrect = Path.Combine(root, "WrongConversion");
Directory.CreateDirectory(incorrect);
var incorrectDll = Path.Combine(incorrect, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.NarrowIntegers").Methods.Single(m => m.Name == "UnsignedShort");
    method.Body.Instructions.Single(i => i.OpCode == OpCodes.Conv_U2).OpCode = OpCodes.Conv_I2;
    module.Write(incorrectDll);
}

var rejected = false;
try
{
    verification.Verify(incorrectDll, "Examples", "NarrowIntegers::UnsignedShort(int)",
        At("Examples/Proofs/UnsignedShort.lean"), incorrect);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    rejected = true;
}

if (!rejected || File.Exists(Path.Combine(incorrect, "verified.json")))
    throw new InvalidOperationException("Incorrect signed conversion accepted");

Console.WriteLine($"Narrow integer proofs passed: {cases} boundary cases; incorrect signed conversion rejected.");
