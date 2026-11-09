#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include WordReaderOutlineSupport.cs

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
source = FillWordReaderOutline(source, skip: false);
if (Regex.IsMatch(source, @"(?<![`\w])sorry(?![`\w])"))
    throw new InvalidOperationException("The cursor proof has unfilled obligations:\n" + source);
File.WriteAllText(outline, source);
VerifyWordReaderOutline(extraction, outline, expected: true);

foreach (var field in new[] { "Position", "Remaining" })
{
    var premise = $"SpanApart values1.storage (WordReader.{field}.entry wordReader)";
    if (!source.Contains(premise, StringComparison.Ordinal))
        throw new InvalidOperationException($"The cursor proof is missing its {field} separation premise");
    var missingSeparation = Path.Combine(root, "Missing" + field + "Separation.lean");
    File.WriteAllText(missingSeparation, source.Replace(premise, "True", StringComparison.Ordinal));
    VerifyWordReaderOutline(extraction, missingSeparation, expected: false);
}

foreach (var mutation in new[]
    { "HelperDecrements", "RemainingIncreases", "WrongIndex", "CorruptElement" })
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
            if (mutation == "WrongIndex")
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
    VerifyWordReaderOutline(rejected, outline, expected: false);
}

var skipExtraction = Path.Combine(root, "SkipAndPeek");
Run(Extract("extract", assembly, "Examples", "WordReader::SkipAndPeek(int[])", skipExtraction));
var skipOutline = Path.Combine(root, "SkipAndPeek.lean");
File.Delete(skipOutline);
Run(Cli("new-proof", skipExtraction, skipOutline));
var skipSource = FillWordReaderOutline(File.ReadAllText(skipOutline), skip: true);
File.WriteAllText(skipOutline, skipSource);
VerifyWordReaderOutline(skipExtraction, skipOutline, expected: true);
var insufficient = Path.Combine(root, "InsufficientRemaining.lean");
File.WriteAllText(insufficient, skipSource.Replace("1 < (WordReader.Remaining",
    "0 < (WordReader.Remaining", StringComparison.Ordinal));
VerifyWordReaderOutline(skipExtraction, insufficient, expected: false);

Console.WriteLine("PASS cursor read and skip/peek consumption proofs; changed helper, bookkeeping, index, " +
    "element and insufficient bounds are rejected");

static string[] Cli(params string[] arguments) => ["dotnet", ExtractorPath, .. arguments];
