#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/TypeTests");
Directory.CreateDirectory(root);
var rejected = new RejectedEvidence(root);
var controls = new GeneratedEvidence(Path.Combine(root, "Controls"));
var queue = new GeneratedQueue(verification, assembly);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.TypeTests")!;
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution",
    "Tests.TypeTestEvidence");

// Read each instruction from its generated lookup equation and check the method covers the complete raw body.
string[][] Ops(string folder, int length, params int[] methods)
{
    var source = File.ReadAllText(Path.Combine(folder, "Extracted.lean"));
    var probe = Path.Combine(folder, "FoldedInstructions.lean");
    var queries = methods.Select(method =>
    {
        var equations = Enumerable.Range(0, length).Select(pc => $"tag Extracted.method{method}_instruction{pc}");
        return $$"""
            example : Extracted.method{{method}}.code.length = {{length}} := rfl
            #eval IO.println ("FOLDED " ++ String.intercalate "|" [{{string.Join(", ", equations)}}])
            """;
    });
    File.WriteAllText(probe, $$"""
        {{source}}

        /-- Classify a generated instruction at its proven program counter. -/
        private def tag {code : List CIL.Instruction} {pc : Nat} {op : CIL.Instruction}
            (_ : code[pc]? = some op) : String :=
          match op with
          | .nop => ".nop"
          | .br target => ".br " ++ toString target
          | .ldc_i4 word => ".ldc_i4 " ++ toString word.toNat
          | .unadmitted opcode => ".unadmitted " ++ toString opcode
          | _ => "other"

        {{string.Join("\n", queries)}}
        """);
    const string prefix = "FOLDED ";
    var rows = Run(["lake", "env", "lean", probe], cwd: FixturePackage()).ReplaceLineEndings("\n").Split('\n')
        .Where(line => line.StartsWith(prefix, StringComparison.Ordinal))
        .Select(line => line[prefix.Length..].Split('|')).ToArray();
    if (rows.Length != methods.Length) throw new InvalidOperationException("Missing decoded instruction equations");
    return rows;
}

// A fold is exactly four emitted no-ops followed by the decided word.
List<(int Pc, string Word)> Folds(string[] ops) => Enumerable.Range(4, Math.Max(0, ops.Length - 4))
    .Where(pc => ops[(pc - 4)..pc].All(op => op == ".nop") && ops[pc].StartsWith(".ldc_i4 ", StringComparison.Ordinal))
    .Select(pc => (pc, ops[pc][".ldc_i4 ".Length..])).ToList();

void QueueRuntime(string name, string folder)
{
    var budget = name == "ReferenceCases" ? 128 : 64;
    var claims = new[] { 0, 1, -1, int.MaxValue, int.MinValue }.Select(input =>
        $"(CIL.Safety.invoke Extracted.program {budget} 0 " +
        $"[.scalar (.i32 {unchecked((uint)input)})] CIL.Safety.Memory.empty).map Prod.snd = " +
        $".ok [.scalar (.i32 {unchecked((uint)(int)runtime.GetMethod(name)!.Invoke(null, [input])!)})]").ToList();
    var proof = Path.Combine(folder, "BoundaryProof.lean");
    File.WriteAllText(proof,
        "import Extracted\nimport CIL.Safety.Execution\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) +
        "⟩\n#print axioms correctness\nend ExampleProof\n");
    queue.Add(new($"TypeTests::{name}(int)", proof, Path.Combine(root, name + "-Verified")),
        () => Console.WriteLine($"PASS {name}: {claims.Count} runtime comparisons"));
}

// Matching and non-matching type arguments decide opposite edges and prune the dead code.
using var examples = ModuleDefinition.ReadModule(assembly);
var bodies = examples.GetType("Examples.TypeTests").Methods;
var classify = bodies.Single(method => method.Name == "Classify").Body.Instructions;
var comparisonPcs = classify.Where(op => op.OpCode.Code == Code.Call && op.Operand is MethodReference
    { Name: "op_Equality" or "op_Inequality" }).Select(classify.IndexOf).ToArray();
int longPc = -1;
foreach (var (name, expected, offset) in new[] { ("Marker", new[] { "1" }, 1), ("Other", new[] { "0", "1" }, 2) })
{
    var folder = Path.Combine(root, name);
    Run(Extract("extract", assembly, "Examples", $"TypeTests::{name}(int)", folder));
    var source = File.ReadAllText(Path.Combine(folder, "Extracted.lean"));
    var ops = Ops(folder, classify.Count, 1).Single();
    var folds = Folds(ops);
    // Each pruned pc is a hole carrying the raw opcode at that pc of the shared generic body.
    var holes = Enumerable.Range(0, ops.Length)
        .Where(pc => ops[pc].StartsWith(".unadmitted ", StringComparison.Ordinal)).ToArray();
    if (!folds.Select(fold => fold.Word).SequenceEqual(expected) ||
        !folds.Select(fold => fold.Pc).SequenceEqual(comparisonPcs.Take(expected.Length)) ||
        holes.Length == 0 || holes.Any(pc => ops[pc] != $".unadmitted {(ushort)classify[pc].OpCode.Value}") ||
        ops.Where((op, pc) => folds.All(fold => fold.Pc != pc)).Count(op => op.StartsWith(".ldc_i4", StringComparison.Ordinal)) != 1 ||
        !ops.Contains($".ldc_i4 {offset}"))
        throw new InvalidOperationException($"Unexpected folded body for {name}: {string.Join(" | ", ops)}");
    Console.WriteLine($"PASS {name}: folded {string.Join(", ", expected)}, dead branches pruned and certificate checked");

    QueueRuntime(name, folder);
    if (name == "Marker") longPc = holes.First(pc => classify[pc].OpCode.Code == Code.Ldarg_0);

    // The lookup equations follow the forged definition, so only the feature certificate can reject the word.
    var forged = expected[0] == "1" ? ".ldc_i4 0" : ".ldc_i4 1";
    var mutated = Path.Combine(root, name + "-forged.lean");
    const string obligation = "method1_features_validated";
    var control = Path.Combine(root, name + "-control.lean");
    var evidence = NarrowEvidence(source, obligation);
    File.WriteAllText(control, evidence);
    controls.Add(control, $"PASS unchanged type-test feature obligation: {name}", obligation);
    File.WriteAllText(mutated, ForgeDecodedInstruction(evidence, 1, comparisonPcs[0],
        $"fun _ => {forged}"));
    rejected.Add(mutated, $"PASS {name}: forged type-test word rejected by the feature certificate",
        "Extraction.FeatureFlowValid", FeatureObligation(1), "is false");
}

// A two-byte opcode at a pruned pc is written as 0xFE00 plus its second byte, here the long form of ldarg.
const int TwoBytePrefix = 0xFE00, LdargSecondByte = 0x09;
var longFolder = Path.Combine(root, "LongOpcode");
Directory.CreateDirectory(longFolder);
var longDll = Path.Combine(longFolder, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.TypeTests").Methods.Single(m => m.Name == "Classify");
    var code = method.Body.Instructions;
    code[longPc].OpCode = OpCodes.Ldarg;
    code[longPc].Operand = method.Parameters[0];
    module.Write(longDll);
}
Run(Extract("extract", longDll, "Examples", "TypeTests::Marker(int)", longFolder));
var longOps = Ops(longFolder, classify.Count, 1).Single();
if (longOps[longPc] != $".unadmitted {TwoBytePrefix + LdargSecondByte}")
    throw new InvalidOperationException($"Two-byte opcode hole at pc {longPc}: {string.Join(" | ", longOps)}");
Console.WriteLine($"PASS two-byte opcode hole: pc {longPc} carries {TwoBytePrefix + LdargSecondByte}");

var referenceFolder = Path.Combine(root, "ReferenceCases");
Run(Extract("extract", assembly, "Examples", "TypeTests::ReferenceCases(int)", referenceFolder));
var reference = bodies.Single(method => method.Name == "ReferenceClassify").Body.Instructions;
var referenceOps = Ops(referenceFolder, reference.Count, 1, 2, 3);
if (referenceOps.Any(ops => ops.Length == 0) ||
    !referenceOps.SelectMany(ops => Folds(ops).Select(fold => fold.Word)).Order().SequenceEqual(["0", "0", "1"]) ||
    referenceOps.Sum(ops => Enumerable.Range(4, ops.Length - 4).Count(pc =>
        ops[(pc - 4)..pc].All(op => op == ".nop") &&
        ops[pc].StartsWith(".br ", StringComparison.Ordinal))) != 3)
    throw new InvalidOperationException("Missing exact typeof result or branch folds");
QueueRuntime("ReferenceCases", referenceFolder);
queue.Flush();
controls.Check(replay: false);
rejected.Check();

// A fold never hides reachable unsupported code.
var live = Execute(Extract("extract", assembly, "Examples", "TypeTests::Word(int)", Path.Combine(root, "Word")));
if (live.Code == 0 || !live.Output.Contains("External managed dependency: System.Int32 System.Environment::get_ProcessorCount()"))
    throw new InvalidOperationException("Reachable unsupported code after a fold was accepted:\n" + live.Output);
Console.WriteLine("PASS Word: the live non-matching branch is still validated");

// Anything other than the exact closed encoding stays unsupported.
const string externalTypeCall = "External managed dependency: System.Type System.Type::GetTypeFromHandle";
foreach (var (mutation, marker) in new[]
{
    ("handle-return-scope", externalTypeCall),
    ("handle-parameter-scope", externalTypeCall),
    ("equality-parameter-scope", externalTypeCall),
    ("vararg-handle", externalTypeCall),
    ("operand-gap", externalTypeCall),
    ("type-local", "Unsupported type: System.Type"),
    ("forwarded-scope", externalTypeCall),
    ("reference-equality", externalTypeCall),
    ("interior-branch", "Branch into a folded type comparison"),
    ("branch-forwarded-scope", externalTypeCall),
    ("branch-interior-branch", "Branch into a folded type comparison")
})
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var branchFold = mutation.StartsWith("branch-", StringComparison.Ordinal);
        var method = module.GetType("Examples.TypeTests").Methods.Single(m =>
            m.Name == (branchFold ? "ReferenceClassify" : "Classify"));
        var body = method.Body;
        var code = body.Instructions;
        var il = body.GetILProcessor();
        var at = branchFold ? code.IndexOf(code.First(i => i.OpCode.Code == Code.Bne_Un_S)) - 4 : 0;
        if (code[at].OpCode.Code != Code.Ldtoken || code[at + 2].OpCode.Code != Code.Ldtoken ||
            code[at + 4].OpCode.Code != (branchFold ? Code.Bne_Un_S : Code.Call))
            throw new InvalidOperationException("Unexpected compiled type test");
        var fromHandle = (MethodReference)code[at + 1].Operand;
        switch (branchFold ? mutation["branch-".Length..] : mutation)
        {
            case "handle-return-scope":
            case "handle-parameter-scope":
            case "equality-parameter-scope":
                var wrongScope = new AssemblyNameReference("TypeSignatureFixture", new Version(1, 0, 0, 0));
                module.AssemblyReferences.Add(wrongScope);
                var equality = (MethodReference)code[at + 4].Operand;
                if (mutation == "handle-parameter-scope")
                    fromHandle.Parameters[0].ParameterType = new TypeReference("System", "RuntimeTypeHandle",
                        module, wrongScope, valueType: true);
                else if (mutation == "handle-return-scope")
                    fromHandle.ReturnType = new TypeReference("System", "Type", module, wrongScope);
                else equality.Parameters[1].ParameterType = new TypeReference("System", "Type", module, wrongScope);
                break;
            case "vararg-handle":
                fromHandle.CallingConvention = MethodCallingConvention.VarArg;
                break;
            case "operand-gap": il.InsertAfter(code[at + 1], il.Create(OpCodes.Nop)); break;
            case "type-local":
                var local = new VariableDefinition(fromHandle.ReturnType);
                body.Variables.Add(local);
                il.InsertAfter(code[at + 1], il.Create(OpCodes.Ldloc, local));
                il.InsertAfter(code[at + 1], il.Create(OpCodes.Stloc, local));
                break;
            case "forwarded-scope":
                var forwarder = new AssemblyNameReference("Forwarder", new Version(1, 0, 0, 0));
                module.AssemblyReferences.Add(forwarder);
                code[at + 2].Operand = new TypeReference("Examples", "TypeMarker", module, forwarder, true);
                break;
            case "reference-equality":
                code[at + 4].Operand = module.ImportReference(typeof(object).GetMethod(nameof(ReferenceEquals))!);
                break;
            case "interior-branch":
                var target = code[at + 2];
                il.InsertBefore(code[at], il.Create(OpCodes.Br, target));
                il.InsertBefore(code[at], il.Create(OpCodes.Call, fromHandle));
                il.InsertBefore(code[at], il.Create(OpCodes.Ldtoken, module.ImportReference(typeof(int))));
                break;
        }
        module.Write(dll);
    }
    var selector = mutation.StartsWith("branch-", StringComparison.Ordinal)
        ? "TypeTests::ReferenceCases(int)" : "TypeTests::Marker(int)";
    var result = Execute(Extract("extract", dll, "Examples", selector, output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) || !result.Output.Contains(marker))
        throw new InvalidOperationException("Incorrect type-test rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}
Console.WriteLine("PASS closed typeof folding, pruning, runtime comparisons, forged words and exact-pattern rejection");
