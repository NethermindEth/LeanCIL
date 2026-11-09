#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/WordReaderOutlines");
Directory.CreateDirectory(root);
var readerType = System.Reflection.Assembly.LoadFile(assembly).GetType("Examples.WordReader")!;
foreach (var (method, position, remaining, expected) in new[]
    { ("Read", 0u, 3u, 11), ("Read", 2u, 1u, 33), ("SkipAndPeek", 0u, 3u, 22) })
{
    var reader = Activator.CreateInstance(readerType)!;
    readerType.GetField("Position")!.SetValue(reader, position);
    readerType.GetField("Remaining")!.SetValue(reader, remaining);
    var result = readerType.GetMethod(method)!.Invoke(reader, [new[] { 11, 22, 33 }]);
    if (!Equals(result, expected) || !Equals(readerType.GetField("Position")!.GetValue(reader), position + 1) ||
        !Equals(readerType.GetField("Remaining")!.GetValue(reader), remaining - 1))
        throw new InvalidOperationException($"Unexpected runtime cursor behavior for {method}");
}
const string selector = "WordReader::Read(int[])";
var extraction = Path.Combine(root, "Read");
Run(Extract("extract", assembly, "Examples", selector, extraction));
var outline = Path.Combine(root, "Proof.lean");
File.Delete(outline);
Run(Cli("new-proof", extraction, outline));
var source = File.ReadAllText(outline);
if (source.Contains("-- not outlined:", StringComparison.Ordinal))
    throw new InvalidOperationException("The cursor read was not fully outlined:\n" + source);
source = FillReader(source, skip: false);
if (Regex.IsMatch(source, @"(?<![`\w])sorry(?![`\w])"))
    throw new InvalidOperationException("The cursor proof has unfilled obligations:\n" + source);
File.WriteAllText(outline, source);
Verify(extraction, outline, expected: true);

foreach (var field in new[] { "Position", "Remaining" })
{
    var premise = $"SpanApart values1.storage (WordReader.{field}.entry wordReader)";
    if (!source.Contains(premise, StringComparison.Ordinal))
        throw new InvalidOperationException($"The cursor proof is missing its {field} separation premise");
    var missingSeparation = Path.Combine(root, "Missing" + field + "Separation.lean");
    File.WriteAllText(missingSeparation, source.Replace(premise, "True", StringComparison.Ordinal));
    Verify(extraction, missingSeparation, expected: false);
}

foreach (var mutation in new[]
    { "HelperDecrements", "RemainingIncreases", "WrongIndex", "CorruptElement", "ScalarLocal" })
{
    var changed = Path.Combine(root, mutation + ".dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var reader = module.GetType("Examples.WordReader");
        var read = reader.Methods.Single(method => method.Name == "Read");
        if (mutation == "HelperDecrements")
            reader.Methods.Single(method => method.Name == "Advance").Body.Instructions
                .Single(instruction => instruction.OpCode == OpCodes.Add).OpCode = OpCodes.Sub;
        else if (mutation == "RemainingIncreases")
            read.Body.Instructions.First(instruction => instruction.OpCode == OpCodes.Sub).OpCode = OpCodes.Add;
        else
        {
            var load = read.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Ldelem_I4);
            var il = read.Body.GetILProcessor();
            if (mutation == "ScalarLocal")
            {
                read.Body.Variables.Add(new VariableDefinition(module.TypeSystem.UInt32));
                read.Body.InitLocals = true;
                il.InsertBefore(load, Instruction.Create(OpCodes.Stloc_0));
                il.InsertBefore(load, Instruction.Create(OpCodes.Ldloc_0));
            }
            else if (mutation == "WrongIndex")
            {
                il.InsertBefore(load, Instruction.Create(OpCodes.Ldc_I4_1));
                il.InsertBefore(load, Instruction.Create(OpCodes.Add));
            }
            else
            {
                il.InsertBefore(load, Instruction.Create(OpCodes.Ldarg_1));
                il.InsertBefore(load, Instruction.Create(OpCodes.Ldarg_0));
                il.InsertBefore(load, Instruction.Create(OpCodes.Ldfld,
                    reader.Fields.Single(field => field.Name == "Position")));
                il.InsertBefore(load, Instruction.Create(OpCodes.Ldc_I4_1));
                il.InsertBefore(load, Instruction.Create(OpCodes.Sub));
                il.InsertBefore(load, Instruction.Create(OpCodes.Ldc_I4_0));
                il.InsertBefore(load, Instruction.Create(OpCodes.Stelem_I4));
            }
        }
        module.Write(changed);
    }
    var rejected = Path.Combine(root, mutation);
    Run(Extract("extract", changed, "Examples", selector, rejected));
    if (mutation == "ScalarLocal")
    {
        var unsupported = Path.Combine(root, "ScalarLocal.lean");
        File.Delete(unsupported);
        Run(Cli("new-proof", rejected, unsupported));
        if (!File.ReadAllText(unsupported).Contains("scalar local homes in a class method",
            StringComparison.Ordinal))
            throw new InvalidOperationException("A class method with scalar local homes must leave an explicit hole");
        continue;
    }
    Verify(rejected, outline, expected: false);
}

var skipExtraction = Path.Combine(root, "SkipAndPeek");
Run(Extract("extract", assembly, "Examples", "WordReader::SkipAndPeek(int[])", skipExtraction));
var skipOutline = Path.Combine(root, "SkipAndPeek.lean");
File.Delete(skipOutline);
Run(Cli("new-proof", skipExtraction, skipOutline));
var skipSource = FillReader(File.ReadAllText(skipOutline), skip: true);
File.WriteAllText(skipOutline, skipSource);
Verify(skipExtraction, skipOutline, expected: true);
var insufficient = Path.Combine(root, "InsufficientRemaining.lean");
File.WriteAllText(insufficient, skipSource.Replace("1 < (WordReader.Remaining",
    "0 < (WordReader.Remaining", StringComparison.Ordinal));
Verify(skipExtraction, insufficient, expected: false);

Console.WriteLine("PASS cursor read and skip/peek consumption proofs; changed helper, bookkeeping, index, " +
    "element and insufficient bounds are rejected");

static string[] Cli(params string[] arguments) => ["dotnet", ExtractorPath, .. arguments];

static void Verify(string extraction, string proof, bool expected)
{
    File.Delete(Path.Combine(extraction, "verified.json"));
    var result = Execute(Cli("verify", extraction, "--proof", proof));
    if ((result.Code == 0) != expected ||
        expected && !result.Stdout.StartsWith("Verified:", StringComparison.Ordinal) ||
        !expected && !result.Output.Contains("Stage: proof checking", StringComparison.Ordinal) ||
        !expected && File.Exists(Path.Combine(extraction, "verified.json")))
        throw new InvalidOperationException($"Unexpected cursor verification result:\n{result.Output}");
}

static string FillReader(string source, bool skip)
{
    source = Regex.Replace(source, @"(def Precondition[\s\S]*?: Prop :=) sorry", """
        $1
          0 < (WordReader.Remaining.of initial wordReader).toNat ∧
          (WordReader.Position.of initial wordReader).toNat +
            (WordReader.Remaining.of initial wordReader).toNat = values1Elements.length ∧
          values1Elements.length < 2 ^ 32
        """);
    if (skip) source = source.Replace("0 < (WordReader.Remaining", "1 < (WordReader.Remaining",
        StringComparison.Ordinal);
    source = Regex.Replace(source, @"(def Postcondition[\s\S]*?: Prop :=) sorry", """
        $1
          values1Elements[(WordReader.Position.of initial wordReader).toNat]? = some result ∧
          (WordReader.Position.of final wordReader).toNat =
            (WordReader.Position.of initial wordReader).toNat + 1 ∧
          (WordReader.Remaining.of final wordReader).toNat + 1 =
            (WordReader.Remaining.of initial wordReader).toNat ∧
          (WordReader.Position.of final wordReader).toNat +
            (WordReader.Remaining.of final wordReader).toNat = values1Elements.length
        """);
    if (skip) source = source.Replace("values1Elements[(WordReader.Position.of initial wordReader).toNat]?",
        "values1Elements[(WordReader.Position.of initial wordReader).toNat + 1]?", StringComparison.Ordinal);
    source = source.Replace("sorry -- Postcondition of the returned value, with `held1`, `held2` the stored fields",
        """
        have positionHeld : WordReader.Position.Holds stored2 wordReader
            (WordReader.Position.of initial wordReader + 1) :=
              held1.after_confined framed2 (apart_of_entries rfl)
          have remainingBefore := (wordReaderRemaining.frame framed1 (apart_of_entries rfl)).2
          dsimp only [Precondition] at assumed
          have next : (WordReader.Position.of initial wordReader + 1).toNat =
              (WordReader.Position.of initial wordReader).toNat + 1 := by
            simp [BitVec.toNat_add]
            omega
          have consumed : (WordReader.Remaining.of initial wordReader - 1).toNat + 1 =
              (WordReader.Remaining.of initial wordReader).toNat := by
            simp [BitVec.toNat_sub]
            omega
          dsimp only [Postcondition, leaveFrame, List.foldl_nil]
          refine ⟨?_, ?_⟩
          · have index : (4294967295 + ((WordReader.Position.of initial wordReader).toNat + 1)) %
                4294967296 = (WordReader.Position.of initial wordReader).toNat := by omega
            simp (disch := omega) [numericOfWidth, BitVec.ofNat_toNat, positionHeld.2, next, index,
              List.getElem?_eq_getElem, Nat.mod_eq_of_lt]
          · rw [positionHeld.2, held2.2, remainingBefore]
            exact ⟨next, consumed, by omega⟩
        """, StringComparison.Ordinal);
    source = source.Replace("sorry -- the index in the current memory is within the supplied array", """
        have positionHeld : WordReader.Position.Holds stored2 wordReader
              (WordReader.Position.of initial wordReader + 1) :=
                held1.after_confined framed2 (apart_of_entries rfl)
            rw [positionHeld.2]
            dsimp only [Precondition] at assumed
            simp [BitVec.toNat_add, BitVec.toNat_sub]
            omega
        """, StringComparison.Ordinal);
    return source;
}
