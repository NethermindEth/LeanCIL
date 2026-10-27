#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/IntegerMath");
Directory.CreateDirectory(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.IntegerMath")!;
var cases = 0;
var pending = new List<(GeneratedVerification Request, string Name, int Count)>();
void Flush()
{
    if (pending.Count == 0) return;
    verification.VerifyGeneratedBatch(assembly, "Examples", pending.Select(item => item.Request).ToArray());
    foreach (var item in pending)
    {
        cases += item.Count;
        Console.WriteLine($"PASS {item.Name}: {item.Count} runtime comparisons");
    }
    pending.Clear();
}
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

string LeanValue(object value) => value switch
{
    bool x => $".scalar (.i32 {(x ? 1 : 0)})",
    sbyte x => $".scalar (.i32 {unchecked((uint)x)})",
    byte x => $".scalar (.i32 {x})",
    nint x => $".scalar (.i64 {unchecked((ulong)x)})",
    nuint x => $".scalar (.i64 {(ulong)x})",
    short x => $".scalar (.i32 {unchecked((uint)x)})",
    ushort x => $".scalar (.i32 {x})",
    int x => $".scalar (.i32 {unchecked((uint)x)})",
    uint x => $".scalar (.i32 {x})",
    long x => $".scalar (.i64 {unchecked((ulong)x)})",
    ulong x => $".scalar (.i64 {x})",
    _ => throw new InvalidOperationException("Unexpected value: " + value)
};

string Bits(object value) => LeanValue(value).Split(' ')[^1].TrimEnd(')');
string Narrow(Type type, string value) => type == typeof(sbyte) ? $"(CIL.NarrowKind.signed8.extend {value})" :
    type == typeof(byte) ? $"(CIL.NarrowKind.unsigned8.extend {value})" :
    type == typeof(short) ? $"(CIL.NarrowKind.signed16.extend {value})" :
    type == typeof(ushort) ? $"(CIL.NarrowKind.unsigned16.extend {value})" : value;
int Width(Type type) => type == typeof(long) || type == typeof(ulong) || type == typeof(nint) || type == typeof(nuint) ? 64 : 32;
// Compare all overloads against the runtime, including exceptional outcomes.
foreach (var method in runtime.GetMethods(BindingFlags.Public | BindingFlags.Static).Where(m => !m.Name.StartsWith("Wrong", StringComparison.Ordinal)))
{
    var output = Path.Combine(root, method.Name);
    Directory.CreateDirectory(output);
    var parameters = method.GetParameters();
    var type = parameters[0].ParameterType;
    var values = new ulong[] { 0, 1, 2, 127, 128, 255, 32767, 32768, 65535, int.MaxValue, 1UL << 31, uint.MaxValue, long.MaxValue, 1UL << 63, ulong.MaxValue }
        .Select(x => Value(type, x)).Distinct().ToArray();
    var boundaryCases = new List<string>();
    foreach (var x in values)
    foreach (var y in parameters.Length > 1 ? values : values.Take(1))
    foreach (var z in parameters.Length > 2 ? values : values.Take(1))
    {
        object[] inputs = parameters.Length switch { 1 => [x], 2 => [x, y], _ => [x, y, z] };
        string expected;
        try
        {
            var result = method.Invoke(null, inputs)!;
            expected = $".ok {Bits(result)}";
        }
        catch (TargetInvocationException error) when (error.InnerException is OverflowException or ArgumentException)
        {
            var fault = error.InnerException is OverflowException ? "overflow" : "invalidBounds";
            expected = $".error .{fault}";
        }
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
    var operation = method.Name.StartsWith("Clamp", StringComparison.Ordinal) ? "clamp" :
        method.Name.StartsWith("Min", StringComparison.Ordinal) ? "min" :
        method.Name.StartsWith("Max", StringComparison.Ordinal) ? "max" :
        method.Name.StartsWith("Abs", StringComparison.Ordinal) ? "abs" : "sign";
    var width = type == typeof(sbyte) || type == typeof(byte) ? 8 : type == typeof(short) || type == typeof(ushort) ? 16 : stackWidth;
    var signed = type == typeof(byte) || type == typeof(ushort) || type == typeof(uint) || type == typeof(ulong) || type == typeof(nuint) ? "false" : "true";
    var binders = $"({string.Join(" ", variables)} : CIL.W{stackWidth})";
    var evaluation = $"CIL.evalIntegerMath .{operation} {width} {signed} [{string.Join(", ", loaded)}]";
    var invocation = $"CIL.Safety.invoke Extracted.program 8 0 [{inputsLean}] Examples.empty";
    var prefix = $"  change CIL.Safety.run Extracted.program {8 - argc} 0 {argc} [{inputsLean}] ⟨0, [], [], [], 0⟩ [{stack}] Examples.empty = _\n";
    var instruction = $"(body := Extracted.method0) (op := .intrinsic (.scalar (.math .{operation} {width} {signed})) {argc})";
    var argumentsLean = string.Join(" ", variables);
    var caseArguments = string.Join(" ", variables.Select(variable => "test." + variable));
    string ForCase(string expression)
    {
        foreach (var variable in variables) expression = expression.Replace(variable, "test." + variable);
        return expression;
    }
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nimport Tests.WrapperProofs\nset_option maxRecDepth 4096\n" +
        "namespace ExampleProof\n" +
        $"theorem wrapper_success_full {binders} (r : CIL.W{resultWidth})\n" +
        $"    (evaluated : {evaluation} = .ok (.i{resultWidth} r)) :\n" +
        $"    {invocation} = .ok (Examples.empty, [.scalar (.i{resultWidth} {Narrow(method.ReturnType, "r")})]) := by\n" + prefix +
        $"  refine (CIL.Safety.run_next {instruction} (by rfl) (by rfl)\n" +
        $"    (show CIL.Safety.step _ _ _ _ _ _ _ = .ok (.next {argc + 1} [.scalar (.i{resultWidth} r)] ⟨0, [], [], [], 0⟩ Examples.empty) from ?_)).trans (by rfl)\n" +
        "  math_wrapper_step evaluated\n" +
        $"theorem wrapper_fault_full {binders} (fault : CIL.ArithmeticFault)\n" +
        $"    (evaluated : {evaluation} = .error fault) :\n" +
        $"    {invocation} = .error ⟨0, {argc}, .arithmetic fault⟩ := by\n" + prefix +
        $"  apply Tests.WrapperProofs.run_fault {instruction} (by rfl) (by rfl)\n" +
        "  math_wrapper_step evaluated\n" +
        $"theorem wrapper_success {binders} (r : CIL.W{resultWidth})\n" +
        $"    (evaluated : {evaluation} = .ok (.i{resultWidth} r)) :\n" +
        $"    ({invocation}).map Prod.snd = .ok [.scalar (.i{resultWidth} {Narrow(method.ReturnType, "r")})] :=\n" +
        "  congrArg (fun result => result.map Prod.snd) " +
        $"(wrapper_success_full {argumentsLean} r evaluated)\n" +
        $"theorem wrapper_fault {binders} (fault : CIL.ArithmeticFault)\n" +
        $"    (evaluated : {evaluation} = .error fault) :\n" +
        $"    ({invocation}).map Prod.snd = .error ⟨0, {argc}, .arithmetic fault⟩ :=\n" +
        "  congrArg (fun result => result.map Prod.snd) " +
        $"(wrapper_fault_full {argumentsLean} fault evaluated)\n" +
        "/-- One runtime comparison, including its normal result or arithmetic fault. -/\n" +
        "structure BoundaryCase where\n" +
        string.Join("\n", variables.Select(variable => $"  {variable} : CIL.W{stackWidth}")) + "\n" +
        $"  expected : Except CIL.ArithmeticFault CIL.W{resultWidth}\n" +
        "/-- Every input tuple and observed outcome from the compiled runtime fixture. -/\n" +
        "def boundaryCases : List BoundaryCase := [\n" + string.Join(",\n", boundaryCases) + "]\n" +
        "/-- The scalar evaluator produces exactly the observed result or fault. -/\n" +
        "def boundaryMatches (test : BoundaryCase) : Bool :=\n" +
        $"  match {ForCase(evaluation)}, test.expected with\n" +
        $"  | .ok (.i{resultWidth} actual), .ok expected => actual == expected\n" +
        "  | .error actual, .error expected => actual == expected\n" +
        "  | _, _ => false\n" +
        "/-- A successful table check establishes equality of the complete scalar outcome. -/\n" +
        "theorem boundaryMatches_correct (test : BoundaryCase) (checked : boundaryMatches test = true) :\n" +
        $"  {ForCase(evaluation)} = test.expected.map CIL.Value.i{resultWidth} := by\n" +
        "  unfold boundaryMatches at checked\n" +
        "  split at checked <;> simp_all [Except.map]\n" +
        "#print axioms boundaryMatches_correct\n" +
        "/-- The kernel checks all recorded runtime comparisons. -/\n" +
        "theorem boundaryEvaluations : boundaryCases.all boundaryMatches = true := by decide +kernel\n" +
        "#print axioms boundaryEvaluations\n" +
        "/-- Every recorded input executes with its observed result, narrowing and located fault. -/\n" +
        "theorem correctness : ∀ test ∈ boundaryCases,\n" +
        $"  ({ForCase(invocation)}).map Prod.snd =\n" +
        $"    (test.expected.map (fun r => [.scalar (.i{resultWidth} {Narrow(method.ReturnType, "r")})])).mapError\n" +
        $"      (fun fault => ⟨0, {argc}, .arithmetic fault⟩) := by\n" +
        "  intro test member\n" +
        "  have evaluated := boundaryMatches_correct test (List.all_eq_true.mp boundaryEvaluations test member)\n" +
        "  cases outcome : test.expected with\n" +
        "  | ok result =>\n" +
        "    rw [outcome] at evaluated\n" +
        $"    exact wrapper_success {caseArguments} result evaluated\n" +
        "  | error fault =>\n" +
        "    rw [outcome] at evaluated\n" +
        $"    exact wrapper_fault {caseArguments} fault evaluated\n" +
        "#print axioms correctness\nend ExampleProof\n");
    var selector = $"IntegerMath::{method.Name}({string.Join(",", parameters.Select(p => p.ParameterType.FullName))})";
    pending.Add((new GeneratedVerification(selector, proof, output), method.Name, boundaryCases.Count));
}
Flush();

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
        "scope" => "Unresolved call: System.Int32 System.Math::Min(System.Int32,System.Int32)",
        "version" => "Unsupported type identity: System.Int32 [System.Runtime, Version=9.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a]",
        "instance" => "Invalid evaluation stack during reachability",
        "return" => "External managed dependency: System.Int64 System.Math::Min(System.Int32,System.Int32)",
        "argument" => "External managed dependency: System.Int32 System.Math::Min(System.Int32,System.Int64)",
        "generic" => "Contract imports require an exact closed generic instantiation on a non-generic declaring type.",
        "unsupported" => "External managed dependency: System.Int32 System.Math::CopySign(System.Int32,System.Int32)",
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
// The same universal specification must reject a maximum implementation.
var contract = At("Examples/Proofs/IntegerMinimum.lean");
verification.Verify(assembly, "Examples", "IntegerMath::MinInt64(long,long)", contract, Path.Combine(root, "UniversalMin"));
var wrongOutput = Path.Combine(root, "WrongMin");
var rejected = false;
try
{
    verification.Verify(assembly, "Examples", "IntegerMath::WrongMin(long,long)", contract, wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    rejected = true;
}
if (!rejected || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Maximum implementation accepted as minimum");

Console.WriteLine($"PASS {cases} integer Math runtime comparisons, universal minimum and incorrect implementation rejection");
Run(["dotnet", "run", "--file", "Tests/WideProduct.cs"], streamOutput: true, progress: "BigMul checked output tests");
