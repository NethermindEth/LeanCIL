#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs
#:include ../scripts/Checking/BatchVerification.cs

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
    var probe = Path.Combine(folder, "DecodedInstructions.lean");
    var queries = methods.Select(method =>
    {
        var equations = Enumerable.Range(0, length).Select(pc => $"tag Extracted.method{method}_instruction{pc}");
        return $$"""
            example : Extracted.method{{method}}.code.length = {{length}} := rfl
            #eval IO.println ("DECODED " ++ String.intercalate "|" [{{string.Join(", ", equations)}}])
            """;
    });
    File.WriteAllText(probe, $$"""
        {{source}}

        /-- Classify a generated instruction at its proven program counter. -/
        private def tag {code : List CIL.Instruction} {pc : Nat} {op : CIL.Instruction}
            (_ : code[pc]? = some op) : String :=
          match op with
          | .nop => ".nop"
          | .ldtoken (.type t) => ".ldtoken " ++ String.ofList ((CIL.Extraction.plainTypeName t).getD [])
          | .call method _ => ".call " ++ method.name.display
          | .ceq => ".ceq"
          | .beq target => ".beq " ++ toString target
          | .bne_un target => ".bne.un " ++ toString target
          | .br target => ".br " ++ toString target
          | .ldc_i4 word => ".ldc_i4 " ++ toString word.toNat
          | .unadmitted opcode => ".unadmitted " ++ toString opcode
          | _ => "other"

        {{string.Join("\n", queries)}}
        """);
    const string prefix = "DECODED ";
    var rows = Run(["lake", "env", "lean", probe], cwd: FixturePackage()).ReplaceLineEndings("\n").Split('\n')
        .Where(line => line.StartsWith(prefix, StringComparison.Ordinal))
        .Select(line => line[prefix.Length..].Split('|')).ToArray();
    if (rows.Length != methods.Length) throw new InvalidOperationException("Missing decoded instruction equations");
    return rows;
}

// Compare each reachable typeof sequence with its source operands, closed generic argument and branch target.
static int[] CheckComparisons(string[] ops, IList<Instruction> body, string argument)
{
    List<int> checkedPcs = [];
    for (int pc = 4; pc < ops.Length; pc++)
    {
        if (body[pc - 4].OpCode.Code != Code.Ldtoken || body[pc - 2].OpCode.Code != Code.Ldtoken || ops[pc].StartsWith(".unadmitted ", StringComparison.Ordinal))
            continue;
        string Token(int at) => ".ldtoken " + (body[at].Operand is GenericParameter
            ? argument : ((TypeReference)body[at].Operand).FullName);
        string comparison = body[pc].OpCode.Code switch
        {
            Code.Call => ".call " + ((MethodReference)body[pc].Operand).Name,
            Code.Ceq => ".ceq",
            Code.Beq or Code.Beq_S => ".beq " + body.IndexOf((Instruction)body[pc].Operand),
            Code.Bne_Un or Code.Bne_Un_S => ".bne.un " + body.IndexOf((Instruction)body[pc].Operand),
            _ => throw new InvalidOperationException($"Unknown comparison at pc {pc}")
        };
        string[] expected = [Token(pc - 4), ".call GetTypeFromHandle", Token(pc - 2), ".call GetTypeFromHandle", comparison];
        if (!ops[(pc - 4)..(pc + 1)].SequenceEqual(expected))
            throw new InvalidOperationException($"Changed typeof instruction at pc {pc}: {string.Join(" | ", ops)}");
        checkedPcs.Add(pc);
    }
    return [.. checkedPcs];
}

static string Comparison(string theorem, int pc, bool same, bool equality)
{
    return $$"""
        theorem {{theorem}} (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) :
            SegmentRun Extracted.program 1 {{pc}} {{pc + 5}} 5 args ⟨frame, stack, memory⟩
              ⟨frame, .scalar (.i32 {{(same == equality ? 1 : 0)}}) :: stack, memory⟩ := by
          exact SegmentRun.compareRuntimeTypes (pc := {{pc}}) (same := {{(same ? "true" : "false")}})
            Extracted.program_method1 Extracted.method1_instruction{{pc}} Extracted.method1_instruction{{pc + 1}}
            Extracted.method1_instruction{{pc + 2}} Extracted.method1_instruction{{pc + 3}}
            Extracted.method1_instruction{{pc + 4}} Extracted.method1_link{{pc + 1}} Extracted.method1_link{{pc + 3}}
            Extracted.method1_link{{pc + 4}} Extracted.method1_model{{pc + 1}} Extracted.method1_model{{pc + 4}}
            Extracted.method1_typeIdentity{{pc + 4}} args frame stack memory
        #print axioms {{theorem}}
        """;
}

void QueueRuntime(string name, string folder)
{
    var budget = name == "ReferenceCases" ? 128 : 64;
    int[] boundaries = [0, 1, -1, int.MaxValue, int.MinValue];
    var claims = boundaries.Select(input =>
        $"(CIL.Safety.invoke Extracted.program {budget} 0 " +
        $"[.scalar (.i32 {unchecked((uint)input)})] CIL.Safety.Memory.empty).map Prod.snd = " +
        $".ok [.scalar (.i32 {unchecked((uint)(int)runtime.GetMethod(name)!.Invoke(null, [input])!)})]").ToList();
    var (initial, result) = name switch
    {
        "Marker" => ("(initial : CIL.Safety.Memory)", "value + 1"),
        "Other" => ("(initial : CIL.Safety.Memory)", "value + 2"),
        "ReferenceCases" => ("", "(value + 4 + 1) + (value + 2) + (value + 3)"),
        _ => throw new ArgumentOutOfRangeException(nameof(name))
    };
    var memory = initial.Length == 0 ? "CIL.Safety.Memory.empty" : "initial";
    var proof = Path.Combine(folder, "BoundaryProof.lean");
    var allInputs = $"(∀ (value : CIL.W32) {initial}, (CIL.Safety.invoke Extracted.program {budget} 0 " +
        $"[.scalar (.i32 value)] {memory}).map Prod.snd = .ok [.scalar (.i32 ({result}))])";
    var comparisonPath = name == "Other" ? """
        apply (firstComparison args frame [] initial 57).trans
        apply (run_next (fuel := 56) Extracted.program_method1 Extracted.method1_instruction5
          (show step _ _ 5 args frame [.scalar (.i32 0)] initial = .ok (.next 10 [] frame initial) from rfl)).trans
        exact (secondComparison args frame [] initial 51).trans (by rfl)
        """ : "exact (firstComparison args frame [] initial 57).trans (by rfl)";
    var general = name == "ReferenceCases" ? """
        by
          intro value
          have raw : (CIL.Safety.invoke Extracted.program 128 0 [.scalar (.i32 value)]
              CIL.Safety.Memory.empty).map Prod.snd =
              .ok [.scalar (.i32 ((value + 4 + 1) + (value + 0 + 2) + (value + 0 + 3)))] := rfl
          have zero : value + (0 : CIL.W32) = value := BitVec.add_zero value
          rw [zero] at raw
          exact raw
        """ : $$"""
        by
          intro value initial
          let args : List Value := [.scalar (.i32 value)]
          let result : List Value := [.scalar (.i32 (value + {{(name == "Marker" ? 1 : 2)}}))]
          let frame : Frame := ⟨initial.nextIdentity, [], [], 0, []⟩
          have child : invoke Extracted.program 62 1 args initial = .ok (initial, result) := by
            apply invoke_of_run (frame := frame) (entered := initial) Extracted.program_method1 rfl rfl
            {{comparisonPath.Replace("\n", "\n    ")}}
          have returned : invoke Extracted.program 64 0 args initial = .ok (initial, result) := by
            apply invoke_of_run (frame := frame) (entered := initial) Extracted.program_method0 rfl rfl
            apply Eq.trans (run_next (fuel := 63) Extracted.program_method0 Extracted.method0_instruction0
              (show step _ _ 0 args frame [] initial = .ok (.next 1 args frame initial) from rfl))
            exact run_call_of_invoke (fuel := 62) (rest := []) Extracted.program_method0
              Extracted.method0_instruction1 rfl child rfl
          change (invoke Extracted.program 64 0 args initial).map Prod.snd = .ok result
          rw [returned]
          rfl
        """;
    var comparisons = name switch
    {
        "Marker" => Comparison("firstComparison", 0, same: true, equality: true),
        "Other" => Comparison("firstComparison", 0, same: false, equality: true) + "\n" +
            Comparison("secondComparison", 10, same: false, equality: false),
        _ => ""
    };
    File.WriteAllText(proof, $$"""
        import Extracted
        import CIL.Safety.RuntimeTypeSegment
        import CIL.Safety.CallComposition
        namespace ExampleProof
        open CIL.Safety
        {{comparisons}}
        theorem allInputs : {{allInputs}} := {{general}}
        #print axioms allInputs
        theorem correctness : {{allInputs}} ∧
          {{string.Join(" ∧\n  ", claims)}} := by
          exact ⟨allInputs, {{string.Join(", ", boundaries.Select(input =>
              $"allInputs {unchecked((uint)input)}" + (initial.Length == 0 ? "" : " Memory.empty")))}}⟩
        #print axioms correctness
        end ExampleProof
        """);
    queue.Add(new($"TypeTests::{name}(int)", proof, Path.Combine(root, name + "-Verified")),
        () => Console.WriteLine($"PASS {name}: all 32-bit inputs and {claims.Count} runtime comparisons"));
}

// Matching and non-matching type arguments decide opposite edges and prune the dead code.
using var examples = ModuleDefinition.ReadModule(assembly);
var bodies = examples.GetType("Examples.TypeTests").Methods;
var classify = bodies.Single(method => method.Name == "Classify").Body.Instructions;
var comparisonPcs = classify.Where(op => op.OpCode.Code == Code.Call && op.Operand is MethodReference
    { Name: "op_Equality" or "op_Inequality" }).Select(classify.IndexOf).ToArray();
int longPc = -1;
foreach (var (name, argument, liveTests, offset) in new[] { ("Marker", "Examples.TypeMarker", 1, 1), ("Other", "Examples.OtherMarker", 2, 2) })
{
    var folder = Path.Combine(root, name);
    Run(Extract("extract", assembly, "Examples", $"TypeTests::{name}(int)", folder));
    var source = File.ReadAllText(Path.Combine(folder, "Extracted.lean"));
    var ops = Ops(folder, classify.Count, 1).Single();
    var comparisons = CheckComparisons(ops, classify, argument);
    // Each pruned pc is a hole carrying the raw opcode at that pc of the shared generic body.
    var holes = Enumerable.Range(0, ops.Length)
        .Where(pc => ops[pc].StartsWith(".unadmitted ", StringComparison.Ordinal)).ToArray();
    if (!comparisons.SequenceEqual(comparisonPcs.Take(liveTests)) ||
        holes.Length == 0 || holes.Any(pc => ops[pc] != $".unadmitted {(ushort)classify[pc].OpCode.Value}") ||
        ops.Count(op => op.StartsWith(".ldc_i4", StringComparison.Ordinal)) != 1 ||
        !ops.Contains($".ldc_i4 {offset}"))
        throw new InvalidOperationException($"Unexpected decoded body for {name}: {string.Join(" | ", ops)}");
    Console.WriteLine($"PASS {name}: {liveTests} original type comparisons, dead branches pruned and certificate checked");

    QueueRuntime(name, folder);
    if (name == "Marker") longPc = holes.First(pc => classify[pc].OpCode.Code == Code.Ldarg_0);

    // The feature certificate must reject replacing the call with its correctly predicted result.
    var forged = name == "Marker" ? ".ldc_i4 1" : ".ldc_i4 0";
    var mutated = Path.Combine(root, name + "-forged.lean");
    const string obligation = "method1_features_validated";
    var control = Path.Combine(root, name + "-control.lean");
    var evidence = NarrowEvidence(source, obligation);
    File.WriteAllText(control, evidence);
    controls.Add(control, $"PASS unchanged type-test feature obligation: {name}", obligation);
    File.WriteAllText(mutated, ForgeDecodedInstruction(evidence, 1, comparisonPcs[0],
        $"fun _ => {forged}"));
    rejected.Add(mutated, $"PASS {name}: constant substituted for a type comparison rejected by the feature certificate",
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
var referenceArguments = new List<string>();
foreach (var ops in referenceOps)
{
    var firstToken = ops.First(op => op.StartsWith(".ldtoken ", StringComparison.Ordinal));
    var argument = firstToken[".ldtoken ".Length..];
    var comparisons = CheckComparisons(ops, reference, argument);
    if (comparisons.Length != (argument == "Examples.TypeMarker" ? 2 : 3) ||
        ops[comparisons[0]] != ".ceq" ||
        comparisons.Skip(1).Any(pc => reference[pc].Operand is not Instruction))
        throw new InvalidOperationException($"Missing reference comparisons for {argument}");
    referenceArguments.Add(argument);
}
if (!referenceArguments.Order(StringComparer.Ordinal).SequenceEqual(["Examples.OtherMarker", "Examples.TypeMarker", "System.UInt64"]))
    throw new InvalidOperationException("Unexpected closed generic arguments in the reference cases");
QueueRuntime("ReferenceCases", referenceFolder);
queue.Flush();
controls.Check(replay: false);
rejected.Check();

// A reachable unsupported call after the comparison must stop extraction.
var live = Execute(Extract("extract", assembly, "Examples", "TypeTests::Word(int)", Path.Combine(root, "Word")));
if (live.Code == 0 || !live.Output.Contains("External managed dependency: System.Int32 System.Environment::get_ProcessorCount()"))
    throw new InvalidOperationException("Reachable unsupported code after a type comparison was accepted:\n" + live.Output);
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
Console.WriteLine("PASS closed typeof instructions, reachability, CLR comparisons and rejection of forged operands");
