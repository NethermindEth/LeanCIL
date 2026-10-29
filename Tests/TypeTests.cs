#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using System.Text.RegularExpressions;
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

string[] Ops(string source, int method) => Regex.Matches(source,
    $@"(?m)^@\[cil_code ↓\] theorem method{method}_instruction\d+ : method{method}\.code\[\d+\]\? = some \((.*) : Op\) := rfl\r?$")
    .Select(match => match.Groups[1].Value).ToArray();

// A fold is exactly four emitted no-ops followed by the decided word.
List<(int Pc, string Word)> Folds(string[] ops) => Enumerable.Range(4, Math.Max(0, ops.Length - 4))
    .Where(pc => ops[(pc - 4)..pc].All(op => op == ".nop") && ops[pc].StartsWith(".const32 ", StringComparison.Ordinal))
    .Select(pc => (pc, ops[pc][".const32 ".Length..])).ToList();

void QueueRuntime(string name, string folder)
{
    var budget = name == "ReferenceCases" ? 128 : 64;
    var claims = new[] { 0, 1, -1, int.MaxValue, int.MinValue }.Select(input =>
        $"(CIL.Safety.invoke Extracted.program {budget} 0 " +
        $"[.scalar (.i32 {unchecked((uint)input)})] Examples.empty).map Prod.snd = " +
        $".ok [.scalar (.i32 {unchecked((uint)(int)runtime.GetMethod(name)!.Invoke(null, [input])!)})]").ToList();
    var proof = Path.Combine(folder, "BoundaryProof.lean");
    File.WriteAllText(proof,
        "import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) +
        "⟩\n#print axioms correctness\nend ExampleProof\n");
    queue.Add(new($"TypeTests::{name}(int)", proof, Path.Combine(root, name + "-Verified")),
        () => Console.WriteLine($"PASS {name}: {claims.Count} runtime comparisons"));
}

// Matching and non-matching type arguments decide opposite edges and prune the dead code.
foreach (var (name, expected, offset) in new[] { ("Marker", new[] { "1" }, 1), ("Other", new[] { "0", "1" }, 2) })
{
    var folder = Path.Combine(root, name);
    Run(Extract("extract", assembly, "Examples", $"TypeTests::{name}(int)", folder));
    var source = File.ReadAllText(Path.Combine(folder, "Extracted.lean"));
    var ops = Ops(source, 1);
    var folds = Folds(ops);
    if (!folds.Select(fold => fold.Word).SequenceEqual(expected) ||
        !ops.Any(op => op.StartsWith(".unsupported", StringComparison.Ordinal)) ||
        ops.Where((op, pc) => folds.All(fold => fold.Pc != pc)).Count(op => op.StartsWith(".const32", StringComparison.Ordinal)) != 1 ||
        !ops.Contains($".const32 {offset}"))
        throw new InvalidOperationException($"Unexpected folded body for {name}: {string.Join(" | ", ops)}");
    Console.WriteLine($"PASS {name}: folded {string.Join(", ", expected)}, dead branches pruned and certificate checked");

    QueueRuntime(name, folder);

    // A forged word must fail independently of the emitted instruction lemma.
    var pc = folds[0].Pc;
    var lines = source.Split('\n');
    var start = Array.FindIndex(lines, line => line.StartsWith("def method1 : Method :=", StringComparison.Ordinal));
    var forged = expected[0] == "1" ? ".const32 0" : ".const32 1";
    var site = start + 1 + pc;
    if (lines[site].Trim().TrimEnd(',') != $".const32 {expected[0]}")
        throw new InvalidOperationException("Could not locate the folded site in " + name);
    lines[site] = lines[site].Replace($".const32 {expected[0]}", forged);
    var lemma = Array.FindIndex(lines, line => line.StartsWith($"@[cil_code ↓] theorem method1_instruction{pc} :", StringComparison.Ordinal));
    lines[lemma] = lines[lemma].Replace($"(.const32 {expected[0]} : Op)", $"({forged} : Op)");
    var mutated = Path.Combine(root, name + "-forged.lean");
    const string obligation = "method1_features_validated";
    var control = Path.Combine(root, name + "-control.lean");
    File.WriteAllText(control, NarrowEvidence(source, obligation));
    controls.Add(control, "PASS unchanged type-test feature obligation: " + name, obligation);
    File.WriteAllText(mutated, NarrowEvidence(string.Join('\n', lines), obligation));
    rejected.Add(mutated, $"PASS {name}: forged type-test word rejected by the feature certificate",
        "Extraction.FeatureFlowValid rawLayouts.toArray method1Closed", "is false");
}

var referenceFolder = Path.Combine(root, "ReferenceCases");
Run(Extract("extract", assembly, "Examples", "TypeTests::ReferenceCases(int)", referenceFolder));
var referenceSource = File.ReadAllText(Path.Combine(referenceFolder, "Extracted.lean"));
var referenceOps = Enumerable.Range(1, 3).Select(index => Ops(referenceSource, index)).ToArray();
if (referenceOps.Any(ops => ops.Length == 0) ||
    referenceOps.Sum(ops => ops.Count(op => op.StartsWith(".branch ", StringComparison.Ordinal))) != 3)
    throw new InvalidOperationException("Missing three decided typeof branch transfers");
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
foreach (var (mutation, marker) in new[]
{
    ("operand-gap", "External managed dependency: System.Type System.Type::GetTypeFromHandle"),
    ("type-local", "Unsupported type: System.Type"),
    ("forwarded-scope", "External managed dependency: System.Type System.Type::GetTypeFromHandle"),
    ("reference-equality", "External managed dependency: System.Type System.Type::GetTypeFromHandle"),
    ("interior-branch", "Branch into a folded type comparison"),
    ("branch-forwarded-scope", "External managed dependency: System.Type System.Type::GetTypeFromHandle"),
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
        if (code[0].OpCode.Code != Code.Ldtoken || code[2].OpCode.Code != Code.Ldtoken ||
            code[4].OpCode.Code != (branchFold ? Code.Bne_Un_S : Code.Call))
            throw new InvalidOperationException("Unexpected compiled type test");
        var fromHandle = (MethodReference)code[1].Operand;
        switch (branchFold ? mutation["branch-".Length..] : mutation)
        {
            case "operand-gap": il.InsertAfter(code[1], il.Create(OpCodes.Nop)); break;
            case "type-local":
                var local = new VariableDefinition(fromHandle.ReturnType);
                body.Variables.Add(local);
                il.InsertAfter(code[1], il.Create(OpCodes.Ldloc, local));
                il.InsertAfter(code[1], il.Create(OpCodes.Stloc, local));
                break;
            case "forwarded-scope":
                var forwarder = new AssemblyNameReference("Forwarder", new Version(1, 0, 0, 0));
                module.AssemblyReferences.Add(forwarder);
                code[2].Operand = new TypeReference("Examples", "TypeMarker", module, forwarder, true);
                break;
            case "reference-equality":
                code[4].Operand = module.ImportReference(typeof(object).GetMethod(nameof(ReferenceEquals))!);
                break;
            case "interior-branch":
                var target = code[2];
                il.InsertBefore(code[0], il.Create(OpCodes.Br, target));
                il.InsertBefore(code[0], il.Create(OpCodes.Call, fromHandle));
                il.InsertBefore(code[0], il.Create(OpCodes.Ldtoken, module.ImportReference(typeof(int))));
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
