#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include ../scripts/Checking/BatchVerification.cs
#:include PinnedMetadata.cs
#:include ContractVariants.cs

using System.Reflection;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/IntegerMath");
Directory.CreateDirectory(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.IntegerMath")!;
verification.EnsureExtractorBuilt();
var extractor = Assembly.Load(File.ReadAllBytes(ExtractorPath));
using var pinned = new PinnedMetadata(extractor, assembly);
var metadata = pinned.Module;
var flags = BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic;
var callModel = extractor.GetType("Nethermind.LeanCIL.RuntimeModels", true)!.GetMethod("CallModel", flags)!;
var select = extractor.GetType("Nethermind.LeanCIL.FeatureProfile", true)!.GetMethod("Select", flags)!;
var profile = select.Invoke(null, ["scalar"]);
var pending = new List<(GeneratedVerification Request, string Name, int Count)>();
object Value(Type type, ulong bits)
{
    if (type == typeof(sbyte)) return unchecked((sbyte)bits);
    if (type == typeof(byte)) return unchecked((byte)bits);
    if (type == typeof(nint)) return unchecked((nint)bits);
    if (type == typeof(nuint)) return unchecked((nuint)bits);
    if (type == typeof(short)) return unchecked((short)bits);
    if (type == typeof(ushort)) return unchecked((ushort)bits);
    if (type == typeof(int)) return unchecked((int)bits);
    if (type == typeof(uint)) return unchecked((uint)bits);
    if (type == typeof(long)) return unchecked((long)bits);
    if (type == typeof(ulong)) return bits;
    throw new InvalidOperationException("Unexpected fixture type: " + type);
}

ulong Bits(object value) => value switch
{
    sbyte x => unchecked((uint)x),
    byte x => x,
    short x => unchecked((uint)x),
    ushort x => x,
    int x => unchecked((uint)x),
    uint x => x,
    nint x => unchecked((ulong)x),
    nuint x => x,
    long x => unchecked((ulong)x),
    ulong x => x,
    _ => throw new InvalidOperationException("Unexpected value: " + value)
};

string Narrow(Type type, string value) => type == typeof(sbyte) ? $"(CIL.NarrowKind.signed8.extend {value})" :
    type == typeof(byte) ? $"(CIL.NarrowKind.unsigned8.extend {value})" :
    type == typeof(short) ? $"(CIL.NarrowKind.signed16.extend {value})" :
    type == typeof(ushort) ? $"(CIL.NarrowKind.unsigned16.extend {value})" : value;
int Width(Type type) => type == typeof(long) || type == typeof(ulong) || type == typeof(nint) || type == typeof(nuint) ? 64 : 32;

string Observe(MethodInfo method, object[] inputs)
{
    try { return $".ok {Bits(method.Invoke(null, inputs)!)}"; }
    catch (TargetInvocationException error) when (error.InnerException is OverflowException or ArgumentException)
    {
        return $".error .{(error.InnerException is OverflowException ? "overflow" : "invalidBounds")}";
    }
}

// Compare all overloads against the runtime, including exceptional outcomes.
foreach (var method in runtime.GetMethods(BindingFlags.Public | BindingFlags.Static).Where(m => !m.Name.StartsWith("Wrong", StringComparison.Ordinal)))
{
    var output = Path.Combine(root, method.Name);
    Directory.CreateDirectory(output);
    var parameters = method.GetParameters();
    var type = parameters[0].ParameterType;
    var operationName = new[] { "Clamp", "Min", "Max", "Abs", "Sign" }
        .Single(name => method.Name.StartsWith(name, StringComparison.Ordinal));
    var parameterTypes = parameters.Select(parameter => parameter.ParameterType).ToArray();
    var primitive = type.GetMethod(operationName, parameterTypes)!;
    var mathRuntime = typeof(Math).GetMethod(operationName, parameterTypes)!;
    if (primitive.ReturnType != method.ReturnType) throw new InvalidOperationException("Primitive result mismatch");
    var fixture = metadata.GetType("Examples.IntegerMath").Methods.Single(candidate => candidate.Name == method.Name);
    var call = (MethodReference)fixture.Body.Instructions.Single(instruction =>
        instruction.OpCode.Code == Mono.Cecil.Cil.Code.Call).Operand;
    var alias = new MethodReference(operationName, call.ReturnType, call.Parameters[0].ParameterType);
    var math = new MethodReference(operationName, call.ReturnType,
        new TypeReference("System", "Math", metadata, call.DeclaringType.Scope));
    foreach (var parameter in call.Parameters)
    {
        alias.Parameters.Add(new ParameterDefinition(parameter.ParameterType));
        math.Parameters.Add(new ParameterDefinition(parameter.ParameterType));
    }
    var originalModel = callModel.Invoke(null, [math, profile]);
    var aliasModel = callModel.Invoke(null, [alias, profile]);
    if (originalModel is not true || aliasModel is not true)
        throw new InvalidOperationException("Primitive helper must share its Math model: " + alias.FullName);
    ulong[] boundaries = [0, 1, 2, 127, 128, 255, 32767, 32768, 65535, int.MaxValue, 1UL << 31,
        uint.MaxValue, long.MaxValue, 1UL << 63, ulong.MaxValue];
    var values = boundaries.Select(x => Value(type, x)).Distinct().ToArray();
    var boundaryCases = new List<string>();
    foreach (var x in values)
    foreach (var y in parameters.Length > 1 ? values : values.Take(1))
    foreach (var z in parameters.Length > 2 ? values : values.Take(1))
    {
        object[] inputs = parameters.Length switch { 1 => [x], 2 => [x, y], _ => [x, y, z] };
        var expected = Observe(mathRuntime, inputs);
        if (Observe(primitive, inputs) != expected)
            throw new InvalidOperationException("Primitive helper runtime mismatch: " + alias.FullName);
        boundaryCases.Add($"⟨{string.Join(", ", inputs.Select(Bits))}, {expected}⟩");
    }

    var proof = Path.Combine(output, "BoundaryProof.lean");
    // Prove the extracted instruction prefix and return once, with the scalar
    // evaluator result as a hypothesis. Every runtime vector below still proves
    // the original checked invocation, including narrowing and located faults.
    var argc = parameters.Length;
    var stackWidth = Width(type);
    var resultWidth = Width(method.ReturnType);
    var variables = Enumerable.Range(0, argc).Select(i => "x" + i).ToArray();
    var inputsLean = string.Join(", ", variables.Select(x => $".scalar (.i{stackWidth} {x})"));
    var loaded = variables.Select(x => $".i{stackWidth} {Narrow(type, x)}").ToArray();
    var stack = string.Join(", ", loaded.Reverse().Select(x => $".scalar ({x})"));
    var operation = operationName.ToLowerInvariant();
    var width = type == typeof(sbyte) || type == typeof(byte) ? 8 : type == typeof(short) || type == typeof(ushort) ? 16 : stackWidth;
    var signed = type == typeof(byte) || type == typeof(ushort) || type == typeof(uint) || type == typeof(ulong) || type == typeof(nuint) ? "false" : "true";
    var binders = $"({string.Join(" ", variables)} : CIL.W{stackWidth})";
    var evaluation = $"CIL.evalIntegerMath .{operation} {width} {signed} [{string.Join(", ", loaded)}]";
    var invocation = $"CIL.Safety.invoke Extracted.program 8 0 [{inputsLean}] CIL.Safety.Memory.empty";
    var atCall = $"CIL.Safety.run Extracted.program {8 - argc} 0 {argc} [{inputsLean}] " +
        $"⟨0, [], [], 0, []⟩ [{stack}] CIL.Safety.Memory.empty";
    var usePrefix = $"  refine (wrapper_prefix {string.Join(" ", variables)}).trans ?_\n";
    // The helper keeps its call, which steps as the scalar intrinsic its model fact names.
    var fetched = $"Extracted.program_method0 Extracted.method0_instruction{argc}";
    var callStep = $"  math_wrapper_step Extracted.method0_model{argc} evaluated\n";
    var caseArguments = string.Join(" ", variables.Select(variable => "test." + variable));
    string ForCase(string expression)
    {
        foreach (var variable in variables) expression = expression.Replace(variable, "test." + variable);
        return expression;
    }
    File.WriteAllText(proof, "import Extracted\nimport CIL.Safety.Execution\nimport Tests.WrapperProofs\nset_option maxRecDepth 4096\n" +
        "namespace ExampleProof\n" +
        "/-- Loading the wrapper arguments reaches the checked arithmetic call. -/\n" +
        $"private theorem wrapper_prefix {binders} :\n    {invocation} =\n    {atCall} := Eq.symm (Eq.refl _)\n" +
        "#print axioms wrapper_prefix\n" +
        $"theorem wrapper_success_full {binders} (r : CIL.W{resultWidth})\n" +
        $"    (evaluated : {evaluation} = .ok (.i{resultWidth} r)) :\n" +
        $"    {invocation} = .ok (CIL.Safety.Memory.empty, [.scalar (.i{resultWidth} {Narrow(method.ReturnType, "r")})]) := by\n" + usePrefix +
        $"  refine (CIL.Safety.run_next {fetched}\n" +
        $"    (show CIL.Safety.step _ _ _ _ _ _ _ = .ok (.next {argc + 1} [.scalar (.i{resultWidth} r)] ⟨0, [], [], 0, []⟩ CIL.Safety.Memory.empty) from ?_)).trans (by rfl)\n" +
        callStep +
        $"theorem wrapper_fault_full {binders} (fault : CIL.ArithmeticFault)\n" +
        $"    (evaluated : {evaluation} = .error fault) :\n" +
        $"    {invocation} = .error ⟨0, {argc}, .arithmetic fault⟩ := by\n" + usePrefix +
        "  have free : CIL.Safety.HandlerFree Extracted.program := by handler_free\n" +
        $"  apply CIL.Safety.run_fault {fetched}\n" +
        $"    (unprotected := by simpa only [Extracted.program_method0, Option.all] using free.unprotected 0 {argc})\n" +
        callStep +
        "/-- One runtime comparison, including its normal result or arithmetic fault. -/\n" +
        "structure BoundaryCase where\n" +
        string.Join("\n", variables.Select(variable => $"  {variable} : CIL.W{stackWidth}")) + "\n" +
        $"  expected : Except CIL.ArithmeticFault CIL.W{resultWidth}\n" +
        "/-- Every input tuple and observed outcome from the compiled runtime fixture. -/\n" +
        "def boundaryCases : List BoundaryCase := [\n" + string.Join(",\n", boundaryCases) + "]\n" +
        "/-- The scalar evaluator produces exactly the observed result or fault. -/\n" +
        "def boundaryMatches (test : BoundaryCase) : Bool :=\n" +
        $"  match {ForCase(evaluation)}, test.expected with\n" +
        $"  | .ok (.i{resultWidth} actual), .ok expected => {Narrow(method.ReturnType, "actual")} == expected\n" +
        "  | .error actual, .error expected => actual == expected\n" +
        "  | _, _ => false\n" +
        "/-- A checked scalar outcome gives exactly the observed result or located fault. -/\n" +
        "theorem boundaryMatches_correct (test : BoundaryCase) (checked : boundaryMatches test = true) :\n" +
        $"  ({ForCase(invocation)}).map Prod.snd =\n" +
        $"    (test.expected.map (fun r => [.scalar (.i{resultWidth} r)])).mapError\n" +
        $"      (fun fault => ⟨0, {argc}, .arithmetic fault⟩) := by\n" +
        "  unfold boundaryMatches at checked\n" +
        "  split at checked\n" +
        "  · rename_i actual expected evaluated outcome\n" +
        "    have same := beq_iff_eq.mp checked\n" +
        "    simpa only [outcome, Except.map, Except.mapError, same] using\n" +
        "      (congrArg (fun result => result.map Prod.snd) " +
        $"(wrapper_success_full {caseArguments} actual evaluated))\n" +
        "  · rename_i actual expected evaluated outcome\n" +
        "    have same := beq_iff_eq.mp checked\n" +
        "    simpa only [outcome, Except.map, Except.mapError, same] using\n" +
        "      (congrArg (fun result => result.map Prod.snd) " +
        $"(wrapper_fault_full {caseArguments} actual evaluated))\n" +
        "  · simp at checked\n" +
        "#print axioms boundaryMatches_correct\n" +
        "/-- The kernel checks all recorded runtime comparisons. -/\n" +
        "theorem boundaryEvaluations : boundaryCases.all boundaryMatches = true := by decide +kernel\n" +
        "#print axioms boundaryEvaluations\n" +
        "/-- Every recorded input executes with its observed result, narrowing and located fault. -/\n" +
        "theorem correctness : ∀ test ∈ boundaryCases,\n" +
        $"  ({ForCase(invocation)}).map Prod.snd =\n" +
        $"    (test.expected.map (fun r => [.scalar (.i{resultWidth} r)])).mapError\n" +
        $"      (fun fault => ⟨0, {argc}, .arithmetic fault⟩) := by\n" +
        "  intro test member\n" +
        "  exact boundaryMatches_correct test (List.all_eq_true.mp boundaryEvaluations test member)\n" +
        "#print axioms correctness\nend ExampleProof\n");
    var selector = $"IntegerMath::{method.Name}({string.Join(",", parameters.Select(p => p.ParameterType.FullName))})";
    pending.Add((new GeneratedVerification(selector, proof, output), method.Name, boundaryCases.Count));
}
verification.VerifyGeneratedBatch(assembly, "Examples", pending.Select(item => item.Request).ToArray());
foreach (var item in pending)
    Console.WriteLine($"PASS {item.Name}: {item.Count} runtime comparisons");
var cases = pending.Sum(item => item.Count);

// A runtime helper model must never accept a forged identity or signature.
foreach (var mutation in new[] { "scope", "version", "instance", "return", "argument", "generic", "unsupported" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.IntegerMath").Methods.Single(m => m.Name == "MinInt32");
        var call = (MethodReference)method.Body.Instructions.Single(i => i.OpCode.Code == Mono.Cecil.Cil.Code.Call).Operand;
        call.DeclaringType = new TypeReference("System", "Int32", module, call.DeclaringType.Scope, true);
        switch (mutation)
        {
            case "scope": call.DeclaringType.Scope = module; break;
            case "version": ((AssemblyNameReference)call.DeclaringType.Scope).Version = new Version(9, 0, 0, 0); break;
            case "instance": call.HasThis = true; break;
            case "return": call.ReturnType = module.TypeSystem.Int64; break;
            case "argument": call.Parameters[1].ParameterType = module.TypeSystem.Int64; break;
            case "generic": call.GenericParameters.Add(new GenericParameter("T", call)); break;
            case "unsupported": call.Name = "CopySign"; break;
        }
        module.Write(dll);
    }
    string diagnostic = mutation switch
    {
        "scope" => "Unresolved call: System.Int32 System.Int32::Min(System.Int32,System.Int32)",
        "version" => "Unsupported type identity: System.Int32 [System.Runtime, Version=9.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a]",
        "instance" => "Invalid evaluation stack during reachability",
        "return" => "External managed dependency: System.Int64 System.Int32::Min(System.Int32,System.Int32)",
        "argument" => "External managed dependency: System.Int32 System.Int32::Min(System.Int32,System.Int64)",
        "generic" => "Contract imports require an exact closed generic instantiation on a non-generic declaring type.",
        "unsupported" => "External managed dependency: System.Int32 System.Int32::CopySign(System.Int32,System.Int32)",
        _ => throw new InvalidOperationException("Unknown runtime mutation: " + mutation)
    };
    foreach (string artifact in new[] { "Extracted.lean", "identity.json", "verified.json" })
        File.Delete(Path.Combine(output, artifact));
    var result = Execute(Extract("extract", dll, "Examples", "IntegerMath::MinInt32(int,int)", output));
    if (result.Code != 1 || !result.Output.Contains(diagnostic, StringComparison.Ordinal) ||
        new[] { "Extracted.lean", "identity.json", "verified.json" }.Any(artifact => File.Exists(Path.Combine(output, artifact))))
        throw new InvalidOperationException("Incorrect runtime rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}
// Both compiled entries return normally at the signed witness.
long MinimumResult(string method) => (long)runtime.GetMethod(method)!.Invoke(null, [-1L, 1L])!;
if (MinimumResult("MinInt64") != -1 || MinimumResult("WrongMin") != 1)
    throw new InvalidOperationException("The compiled entries disagree with the signed minimum witness.");

verification.VerifyContractVariant(assembly, "Examples", "IntegerMath::MinInt64(long,long)",
    Path.Combine(root, "UniversalMin"), assembly, "IntegerMath::WrongMin(long,long)", Path.Combine(root, "WrongMin"),
    """
    /-- The minimum of two signed Int64 values preserves the caller's memory. -/
    def signedMinimum : MethodContract (W64 × W64) W64 where
      args pair := [.scalar (.i64 pair.1), .scalar (.i64 pair.2)]
      results value := [.scalar (.i64 value)]
      pre _ _ := True
      footprint _ := []
      post pair before after value :=
        after = before ∧ value = BitVec.ofInt 64 (min pair.1.toInt pair.2.toInt)
    """, """
    theorem correctness : signedMinimum.Holds Extracted.program 0 := by
      rintro ⟨left, right⟩ memory -
      apply MethodContract.Holds.intro (c := signedMinimum) (input := (left, right)) memory
        (BitVec.ofInt 64 (min left.toInt right.toInt)) ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
      exact ⟨8, rfl⟩
    """, """
    /-- WrongMin returns 1 when the signed minimum is -1. -/
    theorem correctness : signedMinimum.Refuted Extracted.program 0 := by
      apply MethodContract.Refuted.of_return (c := signedMinimum) (input := (-1, 1))
        (initial := Memory.empty) (fuel := 8) (values := [.scalar (.i64 1)]) trivial rfl
      rintro ⟨_, value, encoded, _, rfl⟩
      exact (by decide : [Value.scalar (.i64 1)] ≠ [.scalar (.i64 (-1))]) encoded
    """, example: At("Examples/Proofs/IntegerMinimum.lean"));

Console.WriteLine($"PASS {cases} Math/primitive comparisons, universal signed minimum and verified maximum counterexample");
Run(["dotnet", "run", "--file", "Tests/WideProduct.cs"], streamOutput: true, progress: "BigMul checked output tests");
