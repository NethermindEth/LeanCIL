#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

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
