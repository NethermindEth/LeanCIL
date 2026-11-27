#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

// An object pool with an intrusive free list: Rent reuses the free-list head, creates an item while
// under capacity, throws when every item is rented out, and faults on a null pool. Each mutation breaks one stated
// postcondition, so the unchanged proof must fail inside the theorem that states it.
using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/ItemPool");
Directory.CreateDirectory(root);
const string Rent = "ItemPool::Rent()";
var proof = At("Examples/Proofs/PoolRent.lean");
var proofLines = File.ReadAllLines(proof);
verification.Verify(assembly, "Examples", Rent, proof, Path.Combine(root, "Rent"));
Console.WriteLine("PASS Rent reuses the free-list head, creates under capacity, throws when exhausted or null");

// Rent's exhausted throw binds to CoreLib constructor rows after its three local methods. One set of shared
// templates must bind every row of both profiles' extractions, and must refuse the CoreLib head moved to another row.
string[] templateProfiles = ["scalar", "x64-v3"];
// Rent's three local methods and the six CoreLib rows of its exception's constructor.
const int BoundProgramLength = 9;
var shared = Path.Combine(root, "Templates");
var profiled = templateProfiles.Select(profile => Path.Combine(root, "Rent-" + profile)).ToArray();
for (var index = 0; index < templateProfiles.Length; index++)
    Run(Extract("extract", assembly, "Examples", Rent, profiled[index], templateProfiles[index]));
Run(["dotnet", ExtractorPath, "templates", shared, .. profiled]);
var sharedPath = shared + Path.PathSeparator + FixtureLeanPath();
CompileModule(shared, "Templates", sharedPath);
for (var index = 0; index < profiled.Length; index++)
{
    var path = profiled[index] + Path.PathSeparator + sharedPath;
    CompileModule(profiled[index], "Extracted", path);
    var binding = "TemplateBindings" + index;
    var bindings = File.ReadAllText(Path.Combine(shared, binding + ".lean"));
    if (Regex.Matches(bindings, @"theorem method\d+_template :").Count != BoundProgramLength)
        throw new InvalidOperationException($"Expected a binding for each of Rent's {BoundProgramLength} methods");
    if (index == 0)
    {
        const int firstRuntime = 3;
        bindings += "\nopen Extracted\n";
        for (var method = firstRuntime; method < BoundProgramLength; method++)
            bindings += $"example : constructorImage.rowMethod? localMethods profile environment " +
                $"{method - firstRuntime} = some method{method} := method{method}_decoder_eq\n";
        bindings += """
            example : True := by
              fail_if_success
                have wrong : constructorImage.rowMethod? localMethods profile environment 1 = some method3 :=
                  CIL.Runtime.Net11WinX64.ConstructorImage.rowMethod?_of_validated runtimeRows_eq
                    runtime_validated (by cil_kernel_rfl)
              trivial
            """;
    }
    File.WriteAllText(Path.Combine(profiled[index], binding + ".lean"), bindings);
    CompileModule(profiled[index], binding, path);
}
// Rent's callees are its two local helpers, then the first CoreLib row.
var movedHead = File.ReadAllLines(Path.Combine(shared, "TemplateBindings0.lean"));
var rentBinding = Array.FindIndex(movedHead, line =>
    line.Contains("theorem method0_template :", StringComparison.Ordinal));
const string RentCallees = "Extracted.environment 1 2 3)";
if (rentBinding < 0 || !movedHead[rentBinding + 1].Contains(RentCallees, StringComparison.Ordinal))
    throw new InvalidOperationException("Rent's template binding does not name callees 1, 2 and 3");
movedHead[rentBinding + 1] = movedHead[rentBinding + 1].Replace(RentCallees, "Extracted.environment 1 2 4)",
    StringComparison.Ordinal);
File.WriteAllLines(Path.Combine(profiled[0], "MovedHead.lean"), movedHead);
var movedRefusal = "";
try { CompileModule(profiled[0], "MovedHead", profiled[0] + Path.PathSeparator + sharedPath); }
catch (InvalidOperationException error) when (error.Message.Contains("error:"))
{
    movedRefusal = error.Message;
}
RequireFailureIn([.. movedHead.Select(line => line.Replace("@[cil_code] ", "", StringComparison.Ordinal))],
    ["method0_template"], "moved-head", movedRefusal);
Console.WriteLine("PASS shared templates bind Rent's local and CoreLib rows in two profiles and refuse a moved row");

// Both paths share the final IsRented store, and the capacity test decides between creating and throwing,
// so those mutations break two theorems each.
foreach (var (mutation, theorems) in new[]
{
    ("unmarked", new[] { "rent_reuses", "rent_creates" }),
    ("stale-link", new[] { "rent_reuses" }),
    ("double-count", new[] { "rent_reuses" }),
    ("repeated-id", new[] { "rent_creates" }),
    ("inverted-capacity", new[] { "rent_creates", "rent_exhausted_throws" })
})
{
    var output = Path.Combine(root, "Mutated-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var pool = module.GetType("Examples.ItemPool");
        var item = module.GetType("Examples.PooledItem");
        var method = pool.Methods.Single(candidate => candidate.Name == "Rent");
        var code = method.Body.GetILProcessor();
        var instructions = method.Body.Instructions;
        switch (mutation)
        {
            case "unmarked":
                // item.IsRented = false
                var marking = instructions.Single(instruction => instruction.Operand is MethodReference called &&
                    called.Name == "set_IsRented");
                Require(marking.Previous, OpCodes.Ldc_I4_1).OpCode = OpCodes.Ldc_I4_0;
                break;
            case "stale-link":
                // item.NextFree = item.NextFree, so the rented item still links into the free list
                var next = item.Fields.Single(field => field.Name == "NextFree");
                var unlink = instructions.Single(instruction => instruction.OpCode == OpCodes.Ldnull);
                var receiver = unlink.Previous;
                if (receiver.OpCode.Code is not (Code.Ldloc_0 or Code.Ldloc_S or Code.Ldloc))
                    throw new InvalidOperationException("The null store does not follow a local load: " + receiver);
                code.InsertBefore(unlink, receiver.Operand is VariableDefinition local
                    ? Instruction.Create(receiver.OpCode, local)
                    : Instruction.Create(receiver.OpCode));
                code.Replace(unlink, Instruction.Create(OpCodes.Ldfld, next));
                break;
            case "double-count":
                // _freeCount -= 2
                var decrement = instructions.Single(instruction => instruction.OpCode == OpCodes.Sub);
                Require(decrement.Previous, OpCodes.Ldc_I4_1).OpCode = OpCodes.Ldc_I4_2;
                break;
            case "repeated-id":
                // _nextId += 0, so the next item created repeats this item's id
                var counter = instructions.Single(instruction => instruction.OpCode == OpCodes.Stfld &&
                    instruction.Operand is FieldReference field && field.Name == "_nextId");
                Require(Require(counter.Previous, OpCodes.Add).Previous, OpCodes.Ldc_I4_1).OpCode = OpCodes.Ldc_I4_0;
                break;
            case "inverted-capacity":
                // creates a new item exactly when every item the capacity allows is alive
                var capacity = instructions.Single(instruction => instruction.Operand is FieldReference field &&
                    field.Name == "_capacity");
                var test = capacity.Next;
                test.OpCode = test.OpCode.Code switch
                {
                    Code.Bne_Un_S => OpCodes.Beq_S,
                    Code.Bne_Un => OpCodes.Beq,
                    _ => throw new InvalidOperationException("The capacity test is not bne.un: " + test)
                };
                break;
        }
        module.Write(dll);
    }
    var refusal = "";
    try { verification.Verify(dll, "Examples", Rent, proof, output); }
    catch (InvalidOperationException error) when (error.Message.Contains("error:"))
    {
        refusal = error.Message;
    }
    if (refusal.Length == 0 || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException($"Rent satisfied its proof after the {mutation} mutation");
    RequireFailureIn(proofLines, theorems, mutation, refusal);
    Console.WriteLine($"PASS {mutation} mutation fails {string.Join(" and ", theorems)}");
}

// A null message could reach the exception's resource getter, so the site stays folded: the throw raises the
// folded exception and no CoreLib constructor joins the program's three local methods.
var unbound = Path.Combine(root, "Mutated-null-message");
Directory.CreateDirectory(unbound);
var unboundDll = Path.Combine(unbound, "Examples.dll");
int foldedPc;
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var instructions = module.GetType("Examples.ItemPool").Methods.Single(candidate => candidate.Name == "Rent")
        .Body.Instructions;
    var message = instructions.Single(instruction => instruction.OpCode == OpCodes.Ldstr);
    message.OpCode = OpCodes.Ldnull;
    message.Operand = null;
    var raised = message.Next.Next;
    if (raised.OpCode != OpCodes.Throw)
        throw new InvalidOperationException("The exhausted message does not reach a throw: " + raised);
    foldedPc = instructions.IndexOf(raised);
    module.Write(unboundDll);
}
var foldedProof = Path.Combine(unbound, "Folded.lean");
File.WriteAllText(foldedProof, $$"""
    import Extracted
    namespace ExampleProof
    /-- The throw raises the folded exception, and the program holds only the local methods. -/
    theorem correctness : Extracted.method0.code[{{foldedPc}}]? = some (.throw (some .invalidOperation)) ∧
        Extracted.program.length = 3 :=
      ⟨Extracted.method0_instruction{{foldedPc}}, by cil_kernel_rfl⟩
    #print axioms correctness
    end ExampleProof
    """);
verification.Verify(unboundDll, "Examples", Rent, foldedProof, unbound);
Console.WriteLine("PASS a null exception message keeps Rent's throw folded");

// IsIdle walks the free list through an object local; answering false on a match must break its contract.
const string IsIdle = "ItemPool::IsIdle(Examples.PooledItem)";
var idleProof = At("Examples/Proofs/PoolIdle.lean");
verification.Verify(assembly, "Examples", IsIdle, idleProof, Path.Combine(root, "IsIdle"));
Console.WriteLine("PASS IsIdle answers whether the item is on the null-terminated free list");
var unmatched = Path.Combine(root, "Mutated-unmatched");
Directory.CreateDirectory(unmatched);
var unmatchedDll = Path.Combine(unmatched, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.ItemPool").Methods.Single(candidate => candidate.Name == "IsIdle");
    // return false where the walk meets the item
    method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Ldc_I4_1).OpCode = OpCodes.Ldc_I4_0;
    module.Write(unmatchedDll);
}
var idleRefusal = "";
try { verification.Verify(unmatchedDll, "Examples", IsIdle, idleProof, unmatched); }
catch (InvalidOperationException error) when (error.Message.Contains("error:"))
{
    idleRefusal = error.Message;
}
if (idleRefusal.Length == 0 || File.Exists(Path.Combine(unmatched, "verified.json")))
    throw new InvalidOperationException("IsIdle satisfied its proof after the unmatched mutation");
RequireFailureIn(File.ReadAllLines(idleProof), ["idle_holds"], "unmatched", idleRefusal);
Console.WriteLine("PASS unmatched mutation fails idle_holds");
Console.WriteLine("PASS item pool: Rent and IsIdle proofs and the mutations each postcondition rejects");

void CompileModule(string directory, string module, string leanPath)
{
    var output = Run(["lean", "--root=" + directory, "-o", Path.Combine(directory, module + ".olean"),
        Path.Combine(directory, module + ".lean")], leanPath: leanPath, progress: "Checking " + module);
    if (output.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException("Admitted declaration in " + module);
}

Instruction Require(Instruction instruction, OpCode expected) => instruction.OpCode == expected
    ? instruction
    : throw new InvalidOperationException($"Expected {expected} before the mutated store, found {instruction}");

// A failure outside the stated theorems would mean the mutation broke the proof's scaffolding,
// not the postconditions it targets; each stated theorem must fail.
void RequireFailureIn(string[] source, string[] theorems, string mutation, string refusal)
{
    var ranges = theorems.Select(theorem => TheoremLines(source, theorem)).ToArray();
    var lines = Regex.Matches(refusal, @"\.lean:(\d+):\d+: error").Select(match => int.Parse(match.Groups[1].Value))
        .ToArray();
    bool Inside(int line, (int Start, int End) range) => line > range.Start && line <= range.End + 1;
    var stray = lines.Length == 0 || lines.Any(line => !ranges.Any(range => Inside(line, range)));
    if (stray || ranges.Any(range => !lines.Any(line => Inside(line, range))))
        throw new InvalidOperationException(
            $"The {mutation} mutation did not fail exactly inside {string.Join(", ", theorems)}:\n{refusal}");
}

(int Start, int End) TheoremLines(string[] lines, string theorem)
{
    var start = Array.FindIndex(lines, line => line.StartsWith($"theorem {theorem} ", StringComparison.Ordinal));
    var end = Array.FindIndex(lines, line => line == $"#print axioms {theorem}");
    return start < 0 || end < start
        ? throw new InvalidDataException("The pool proofs do not state " + theorem)
        : (start, end);
}
