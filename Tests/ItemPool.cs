#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

// An object pool with an intrusive free list: Rent reuses the free-list head, throws when every
// item is rented out, and faults on a null pool. Each mutation breaks one stated postcondition, so
// the unchanged proof must fail inside the theorem that states it.
using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/ItemPool");
Directory.CreateDirectory(root);
const string Rent = "ItemPool::Rent()";
var proof = At("Examples/Proofs/PoolRent.lean");
var proofLines = File.ReadAllLines(proof);
verification.Verify(assembly, "Examples", Rent, proof, Path.Combine(root, "Rent"));
Console.WriteLine("PASS Rent reuses the free-list head, throws when exhausted and faults on a null pool");

foreach (var (mutation, theorem) in new[]
{
    ("unmarked", "rent_reuses"),
    ("stale-link", "rent_reuses"),
    ("double-count", "rent_reuses"),
    ("inverted-capacity", "rent_exhausted_throws")
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
    RequireFailureIn(theorem, mutation, refusal);
    Console.WriteLine($"PASS {mutation} mutation fails {theorem}");
}
Console.WriteLine("PASS item pool: Rent proofs and the mutations each postcondition rejects");

Instruction Require(Instruction instruction, OpCode expected) => instruction.OpCode == expected
    ? instruction
    : throw new InvalidOperationException($"Expected {expected} before the mutated store, found {instruction}");

// A failure outside the stated theorem would mean the mutation broke the proof's scaffolding,
// not the postcondition it targets.
void RequireFailureIn(string theorem, string mutation, string refusal)
{
    var start = Array.FindIndex(proofLines, line => line.StartsWith($"theorem {theorem} ", StringComparison.Ordinal));
    var end = Array.FindIndex(proofLines, line => line == $"#print axioms {theorem}");
    if (start < 0 || end < start)
        throw new InvalidDataException("Examples/Proofs/PoolRent.lean does not state " + theorem);
    var lines = Regex.Matches(refusal, @"\.lean:(\d+):\d+: error").Select(match => int.Parse(match.Groups[1].Value))
        .ToArray();
    if (lines.Length == 0 || lines.Any(line => line <= start || line > end + 1))
        throw new InvalidOperationException($"The {mutation} mutation did not fail only inside {theorem}:\n{refusal}");
}
