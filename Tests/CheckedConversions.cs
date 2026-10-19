#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Numerics;
using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/CheckedConversions");
Directory.CreateDirectory(root);
var cases = 0;

verification.Verify(assembly, "Examples", "CheckedConversions::Narrow(ulong)",
    At("Examples/Proofs/CheckedNarrow.lean"), Path.Combine(root, "Narrow"));

// Every integer checked-conversion encoding, including native destinations.
var operations = new (OpCode Op, int Width, bool Signed, bool UnsignedInput, bool Native)[]
{
    (OpCodes.Conv_Ovf_I1, 8, true, false, false), (OpCodes.Conv_Ovf_I1_Un, 8, true, true, false),
    (OpCodes.Conv_Ovf_U1, 8, false, false, false), (OpCodes.Conv_Ovf_U1_Un, 8, false, true, false),
    (OpCodes.Conv_Ovf_I2, 16, true, false, false), (OpCodes.Conv_Ovf_I2_Un, 16, true, true, false),
    (OpCodes.Conv_Ovf_U2, 16, false, false, false), (OpCodes.Conv_Ovf_U2_Un, 16, false, true, false),
    (OpCodes.Conv_Ovf_I4, 32, true, false, false), (OpCodes.Conv_Ovf_I4_Un, 32, true, true, false),
    (OpCodes.Conv_Ovf_U4, 32, false, false, false), (OpCodes.Conv_Ovf_U4_Un, 32, false, true, false),
    (OpCodes.Conv_Ovf_I8, 64, true, false, false), (OpCodes.Conv_Ovf_I8_Un, 64, true, true, false),
    (OpCodes.Conv_Ovf_U8, 64, false, false, false), (OpCodes.Conv_Ovf_U8_Un, 64, false, true, false),
    (OpCodes.Conv_Ovf_I, 64, true, false, true), (OpCodes.Conv_Ovf_I_Un, 64, true, true, true),
    (OpCodes.Conv_Ovf_U, 64, false, false, true), (OpCodes.Conv_Ovf_U_Un, 64, false, true, true)
};

if (IntPtr.Size != 8) throw new InvalidOperationException("Runtime comparisons require the admitted 64-bit target");

// Cases share the session warmed above and are otherwise independent; checks are dominated by process startup.
var checks = new[] { 32, 64 }.SelectMany(inputWidth => operations.Select(operation => (inputWidth, operation))).ToArray();
Parallel.ForEach(checks, new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount }, check =>
{
    var (inputWidth, (operation, width, signed, unsignedInput, native)) = check;
    var output = Path.Combine(root, operation.Name.Replace('.', '_') + "-" + inputWidth);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    var stackWidth = width <= 32 ? 32 : 64;
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.CheckedConversions").Methods.Single(m => m.Name == "Narrow");
        method.Parameters[0].ParameterType = inputWidth == 32 ? module.TypeSystem.UInt32 : module.TypeSystem.UInt64;
        method.ReturnType = stackWidth == 32 ? module.TypeSystem.UInt32 : module.TypeSystem.UInt64;
        var code = method.Body.Instructions;
        code.Clear();
        code.Add(Instruction.Create(OpCodes.Ldarg_0));
        code.Add(Instruction.Create(operation));
        if (native) code.Add(Instruction.Create(OpCodes.Conv_U8));
        code.Add(Instruction.Create(OpCodes.Ret));
        selector = method.FullName;
        module.Write(dll);
    }

    var runtime = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.CheckedConversions")!.GetMethod("Narrow")!;
    var modulus = BigInteger.One << inputWidth;
    var inputSign = modulus >> 1;
    var bound = BigInteger.One << (signed ? width - 1 : width);
    var lower = signed ? -bound : BigInteger.Zero;
    var values = new HashSet<BigInteger> { 0, 1, inputSign - 1, inputSign, inputSign + 1, modulus - 1 };
    // Include both sides of every destination boundary, encoded in the source width.
    foreach (var limit in new[] { lower, bound, new BigInteger(128), new BigInteger(256), new BigInteger(32768), new BigInteger(65536) })
    foreach (var delta in new[] { -1, 0, 1 })
        values.Add(((limit + delta) % modulus + modulus) % modulus);
    var claims = new List<string>();

    foreach (var bits in values.Order())
    {
        var number = !unsignedInput && bits >= inputSign ? bits - modulus : bits;
        var overflow = number < lower || number >= bound;
        var outputModulus = BigInteger.One << stackWidth;
        var expected = (number + outputModulus) % outputModulus;
        object argument = inputWidth == 32 ? (object)(uint)bits : (ulong)bits;
        try
        {
            var result = runtime.Invoke(null, [argument]);
            var actual = result is uint word ? new BigInteger(word) : new BigInteger((ulong)result!);
            if (overflow || actual != expected)
                throw new InvalidOperationException($"Runtime mismatch: {operation} {inputWidth}: {bits}");
        }
        catch (TargetInvocationException error) when (error.InnerException is OverflowException)
        {
            if (!overflow) throw new InvalidOperationException("Unexpected runtime overflow", error);
        }

        var outcome = overflow ? ".error ⟨0, 1, .arithmetic .overflow⟩" : $".ok [.scalar (.i{stackWidth} {expected})]";
        claims.Add($"(CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i{inputWidth} {bits})] Examples.empty).map Prod.snd = {outcome}");
    }

    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 4096\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    verification.Verify(dll, "Examples", selector, proof, output);
    Interlocked.Add(ref cases, claims.Count);
    Console.WriteLine($"PASS {operation.Name} from {inputWidth}: {claims.Count} runtime comparisons and proofs");
});

// Truncating to eight bits cannot satisfy the original 32-bit narrowing contract.
var wrongOutput = Path.Combine(root, "WrongNarrow");
Directory.CreateDirectory(wrongOutput);
var wrongDll = Path.Combine(wrongOutput, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.CheckedConversions").Methods.Single(m => m.Name == "Narrow");
    method.Body.Instructions.Single(i => i.OpCode == OpCodes.Conv_Ovf_U4_Un).OpCode = OpCodes.Conv_U1;
    module.Write(wrongDll);
}
var rejected = false;
try
{
    verification.Verify(wrongDll, "Examples", "CheckedConversions::Narrow(ulong)",
        At("Examples/Proofs/CheckedNarrow.lean"), wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    rejected = true;
}
if (!rejected || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Incorrect conversion accepted");

Console.WriteLine($"Checked conversions passed: {cases} cases; universal contract passed and incorrect conversion rejected.");
