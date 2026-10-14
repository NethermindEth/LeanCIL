#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Numerics;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/IntegerOpcodes");
Directory.CreateDirectory(root);

// Prove a mathematical contract over actual C# compiler output for every input.
foreach (var width in new[] { 32, 64 })
{
    verification.Verify(assembly, "Examples", $"IntegerOperations::Negate{width}({(width == 32 ? "int" : "long")})",
        At($"Examples/Proofs/Negate{width}.lean"), Path.Combine(root, $"Negate{width}"));
}

// Cecil preserves exact encodings that C# may optimize away or choose differently.
var operations = new[] { OpCodes.Nop, OpCodes.Neg, OpCodes.Cgt, OpCodes.Bgt, OpCodes.Bgt_S,
    OpCodes.Ble, OpCodes.Ble_S, OpCodes.Ble_Un, OpCodes.Ble_Un_S };

foreach (var width in new[] { 32, 64 })
foreach (var operation in operations)
{
    var name = operation.Name.Replace('.', '_') + width;
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");

    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.IntegerOperations").Methods.Single(m => m.Name == $"Greater{width}");
        var code = method.Body.Instructions;
        code.Clear();
        method.Body.Variables.Clear();
        var unary = operation == OpCodes.Nop || operation == OpCodes.Neg;
        method.ReturnType = unary ? method.Parameters[0].ParameterType : module.TypeSystem.Int32;
        if (unary)
            method.Parameters.RemoveAt(1);

        code.Add(Instruction.Create(OpCodes.Ldarg_0));
        if (!unary)
            code.Add(Instruction.Create(OpCodes.Ldarg_1));

        if (operation.FlowControl == FlowControl.Cond_Branch)
        {
            var taken = Instruction.Create(OpCodes.Ldc_I4_1);
            code.Add(Instruction.Create(operation, taken));
            code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
            code.Add(Instruction.Create(OpCodes.Ret));
            code.Add(taken);
        }
        else
        {
            code.Add(Instruction.Create(operation));
        }

        code.Add(Instruction.Create(OpCodes.Ret));
        module.Write(dll);
    }

    // Cross-product exercises equality, both branch outcomes, signs and endpoints.
    var modulus = BigInteger.One << width;
    var sign = modulus >> 1;
    BigInteger[] values = [0, 1, sign - 1, sign, modulus - 1];
    var claims = new List<string>();

    foreach (var left in values)
    foreach (var right in values)
    {
        var unary = operation == OpCodes.Nop || operation == OpCodes.Neg;
        if (unary && right != 0)
            continue;

        var signedLeft = left >= sign ? left - modulus : left;
        var signedRight = right >= sign ? right - modulus : right;
        var result = operation.Code switch
        {
            Code.Nop => left,
            Code.Neg => (modulus - left) % modulus,
            Code.Cgt or Code.Bgt or Code.Bgt_S => signedLeft > signedRight ? 1 : 0,
            Code.Ble or Code.Ble_S => signedLeft <= signedRight ? 1 : 0,
            Code.Ble_Un or Code.Ble_Un_S => left <= right ? 1 : 0,
            _ => throw new InvalidOperationException("Missing test oracle")
        };
        var arguments = $"[.scalar (.i{width} {left})" + (unary ? "]" : $", .scalar (.i{width} {right})]");
        claims.Add($"(CIL.Safety.invoke Extracted.program 8 0 {arguments} Examples.empty).map Prod.snd = .ok [.scalar (.i{(unary ? width : 32)} {result})]");
    }

    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness :\n  " +
        string.Join(" ∧\n  ", claims) + " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    var type = width == 32 ? "int" : "long";
    var parameters = operation == OpCodes.Nop || operation == OpCodes.Neg ? type : $"{type},{type}";
    verification.Verify(dll, "Examples", $"IntegerOperations::Greater{width}({parameters})", proof, output);
    Console.WriteLine($"PASS {operation.Name} i{width}: {claims.Count} boundary cases");

    // Identity cannot satisfy the universal additive-inverse contract.
    if (operation == OpCodes.Nop)
    {
        var rejected = false;

        try
        {
            verification.Verify(dll, "Examples", $"IntegerOperations::Greater{width}({parameters})",
                At($"Examples/Proofs/Negate{width}.lean"), output);
        }
        catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
        {
            rejected = true;
        }

        if (!rejected || File.Exists(Path.Combine(output, "verified.json")))
            throw new InvalidOperationException("Incorrect negation implementation accepted");

        Console.WriteLine($"PASS incorrect negation i{width} rejected by proof checking");
    }
}

Console.WriteLine("Integer opcode proofs passed.");
