using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

partial class Program
{
    // One switched method per signature shares extraction and proofs across the three shifts.
    static void QueueNativeShiftCounts(GeneratedQueue queue, string assembly, string root)
    {
        var directory = Path.Combine(root, "NativeShiftCounts");
        Directory.CreateDirectory(directory);
        var dll = Path.Combine(directory, "Examples.dll");
        var signatures = new List<(string Name, string Selector, int Width, bool Native, bool UnsignedCount)>();
        var rejected = new List<string>();
        var operations = new[] { OpCodes.Shl, OpCodes.Shr, OpCodes.Shr_Un };
        using (var module = ModuleDefinition.ReadModule(assembly))
        {
            var owner = module.GetType("Examples.NativeIntegers");
            foreach (var (valueType, width, native) in new[]
            {
                (module.TypeSystem.Int32, 32, false), (module.TypeSystem.Int64, 64, false),
                (module.TypeSystem.IntPtr, 64, true)
            })
            foreach (var unsignedCount in new[] { false, true })
            {
                var name = $"ShiftCount{valueType.Name}{(unsignedCount ? "Unsigned" : "Signed")}";
                var method = new MethodDefinition(name,
                    Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, valueType);
                method.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
                method.Parameters.Add(new ParameterDefinition(valueType));
                method.Parameters.Add(new ParameterDefinition(unsignedCount
                    ? module.TypeSystem.UIntPtr : module.TypeSystem.IntPtr));
                owner.Methods.Add(method);
                var code = method.Body.Instructions;
                var targets = operations.Select(_ => Instruction.Create(OpCodes.Ldarg_1)).ToArray();
                code.Add(Instruction.Create(OpCodes.Ldarg_0));
                code.Add(Instruction.Create(OpCodes.Switch, targets));
                code.Add(Instruction.Create(OpCodes.Ldarg_1));
                code.Add(Instruction.Create(OpCodes.Ret));
                for (var index = 0; index < operations.Length; index++)
                {
                    code.Add(targets[index]);
                    code.Add(Instruction.Create(OpCodes.Ldarg_2));
                    code.Add(Instruction.Create(operations[index]));
                    code.Add(Instruction.Create(OpCodes.Ret));
                }
                signatures.Add((name, method.FullName, width, native, unsignedCount));
            }
            foreach (var operation in operations)
            {
                var method = new MethodDefinition("InvalidShift" + operation.Code,
                    Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Int64);
                method.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int64));
                method.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int64));
                owner.Methods.Add(method);
                foreach (var instruction in new[] { OpCodes.Ldarg_0, OpCodes.Ldarg_1, operation, OpCodes.Ret })
                    method.Body.Instructions.Add(Instruction.Create(instruction));
                rejected.Add(method.FullName);
            }
            module.Write(dll);
        }

        var runtime = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.NativeIntegers")!;
        // Paired boundaries cover both sign bits and count masking without a Cartesian product.
        const ulong signBits = 0x8000000080000001;
        (ulong Value, ulong Count)[] boundaries =
        [
            (0, 0), (1, 0), (1, 1), (ulong.MaxValue, 31), (signBits, 32), (signBits, 63),
            (ulong.MaxValue, 64), (ulong.MaxValue, 65), (signBits, ulong.MaxValue),
            (signBits, 1UL << 32), (signBits, (1UL << 32) + 1), (ulong.MaxValue, 1UL << 63)
        ];
        foreach (var signature in signatures)
        {
            var method = runtime.GetMethod(signature.Name)!;
            var claims = new List<string>();
            for (var operation = 0; operation < operations.Length; operation++)
            foreach (var (value, count) in boundaries)
            {
                object argument = signature.Native ? (object)unchecked((nint)value) :
                    signature.Width == 32 ? (object)unchecked((int)value) : unchecked((long)value);
                object amount = signature.UnsignedCount ? (object)unchecked((nuint)count) : unchecked((nint)count);
                var result = method.Invoke(null, [operation, argument, amount])!;
                var resultBits = result switch
                {
                    int word => unchecked((uint)word), long word => unchecked((ulong)word),
                    nint word => unchecked((ulong)word), _ => throw new InvalidOperationException("Invalid shift result")
                };
                var valueBits = signature.Width == 32 ? unchecked((uint)value) : value;
                claims.Add($"(CIL.Safety.invoke Extracted.program 16 0 " +
                    $"[.scalar (.i32 {operation}), .scalar (.i{signature.Width} {valueBits}), " +
                    $".scalar (.i64 {count})] Examples.empty).map Prod.snd = " +
                    $".ok [.scalar (.i{signature.Width} {resultBits})]");
            }
            var output = Path.Combine(directory, signature.Name);
            Directory.CreateDirectory(output);
            var proof = Path.Combine(output, "BoundaryProof.lean");
            File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
                "theorem correctness :\n" + string.Join(" ∧\n", claims) + " := by\n  exact ⟨" +
                string.Join(", ", claims.Select(_ => "rfl")) + "⟩\n#print axioms correctness\nend ExampleProof\n");
            queue.Add(new(signature.Selector, proof, output, Assembly: dll),
                () => Console.WriteLine($"PASS {signature.Name}: {claims.Count} native-count runtime comparisons"));
        }
        foreach (var (selector, index) in rejected.Select((selector, index) => (selector, index)))
        {
            var result = Execute(Extract("extract", dll, "Examples", selector,
                Path.Combine(directory, "Rejected" + index)));
            if (result.Code == 0 || !result.Output.Contains("Unsupported shift operand types", StringComparison.Ordinal))
                throw new InvalidOperationException("Ordinary int64 shift count was not rejected: " + result.Output);
        }
        Console.WriteLine("PASS all three shift opcodes reject ordinary int64 counts");
    }
}
