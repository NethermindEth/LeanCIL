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
var root = At("artifacts/SavedWordReaderOutlines");
Directory.CreateDirectory(root);
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var reader = module.GetType("Examples.WordReader");
    foreach (var (name, count, type) in new[]
        {
            ("Reserve", 1, MetadataType.UInt32), ("ReadSaved", 2, MetadataType.UInt32),
            ("RangeEnd", 1, MetadataType.UInt32), ("ReplaceRemainingWide", 1, MetadataType.UInt64)
        })
    {
        var method = reader.Methods.Single(candidate => candidate.Name == name);
        if (!method.Body.InitLocals || method.Body.Variables.Count != count ||
            method.Body.Variables.Any(local => local.VariableType.MetadataType != type))
            throw new InvalidOperationException($"{name} must exercise {count} initialized {type} local homes");
    }
}
var readerType = System.Reflection.Assembly.LoadFile(assembly).GetType("Examples.WordReader")!;
foreach (var (method, arguments, result, position, remaining) in new[]
    {
        ("ReadSaved", new object[] { new[] { 11, 22, 33 } }, (object)22, 2u, 1u),
        ("ReplaceRemaining", new object[] { 5u }, (object)3u, 1u, 5u),
        ("ReplaceRemainingWide", new object[] { 5u }, (object)3ul, 1u, 5u)
    })
{
    var reader = Activator.CreateInstance(readerType)!;
    readerType.GetField("Position")!.SetValue(reader, 1u);
    readerType.GetField("Remaining")!.SetValue(reader, 2u);
    if (!Equals(readerType.GetMethod(method)!.Invoke(reader, arguments), result) ||
        !Equals(readerType.GetField("Position")!.GetValue(reader), position) ||
        !Equals(readerType.GetField("Remaining")!.GetValue(reader), remaining))
        throw new InvalidOperationException($"Unexpected saved-position runtime behavior for {method}");
}
foreach (var method in new[] { "ReadSaved", "ReplaceRemaining", "ReplaceRemainingWide" })
{
    var selector = $"WordReader::{method}({(method == "ReadSaved" ? "int[]" : "uint")})";
    var extraction = Path.Combine(root, method);
    Run(Extract("extract", assembly, "Examples", selector, extraction));
    var outline = Path.Combine(root, method + ".lean");
    File.Delete(outline);
    Run(Cli("new-proof", extraction, outline));
    var source = File.ReadAllText(outline);
    if (source.Contains("-- not outlined:", StringComparison.Ordinal))
        throw new InvalidOperationException($"The saved-position {method} was not fully outlined:\n{source}");
    source = Fill(source, method);
    File.WriteAllText(outline, source);
    VerifyWordReaderOutline(extraction, outline, expected: true);

    foreach (var mutation in method == "ReadSaved"
        ? new[] { "WrongSavedPosition", "WrongAdvance", "WrongIndex", "WrongSavedRemaining" }
        : method == "ReplaceRemaining" ? new[] { "WrongRangeEnd", "WrongRemaining" }
        : new[] { "WrongWideRangeEnd" })
    {
        var changed = Path.Combine(root, mutation + ".dll");
        using (var module = ModuleDefinition.ReadModule(assembly))
        {
            var reader = module.GetType("Examples.WordReader");
            var target = reader.Methods.Single(candidate => candidate.Name ==
                (mutation is "WrongSavedPosition" or "WrongAdvance" ? "Reserve" :
                mutation == "WrongRangeEnd" ? "RangeEnd" : method));
            if (mutation == "WrongSavedRemaining")
            {
                var save = target.Body.Instructions.First(instruction => instruction.OpCode == OpCodes.Stloc_0);
                var il = target.Body.GetILProcessor();
                il.InsertBefore(save, Instruction.Create(OpCodes.Ldc_I4_1));
                il.InsertBefore(save, Instruction.Create(OpCodes.Add));
            }
            else if (mutation is "WrongAdvance" or "WrongRangeEnd" or "WrongWideRangeEnd")
                target.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Add)
                    .OpCode = OpCodes.Sub;
            else
            {
                var before = target.Body.Instructions.Single(instruction =>
                    instruction.OpCode == (mutation == "WrongIndex" ? OpCodes.Ldelem_I4 :
                    mutation == "WrongRemaining" ? OpCodes.Stfld : OpCodes.Ret));
                var il = target.Body.GetILProcessor();
                il.InsertBefore(before, Instruction.Create(OpCodes.Ldc_I4_1));
                il.InsertBefore(before, Instruction.Create(OpCodes.Add));
            }
            module.Write(changed);
        }
        var rejected = Path.Combine(root, mutation);
        Run(Extract("extract", changed, "Examples", selector, rejected));
        VerifyWordReaderOutline(rejected, outline, expected: false);
    }
    Console.WriteLine($"PASS {method} filled outline and semantic mutation rejection");
}
var collisionAssembly = Path.Combine(root, "ParameterCollision.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    module.GetType("Examples.WordReader").Methods.Single(method => method.Name == "ReplaceRemaining")
        .Parameters[0].Name = "localHome0";
    module.Write(collisionAssembly);
}
var collisionExtraction = Path.Combine(root, "ParameterCollision");
Run(Extract("extract", collisionAssembly, "Examples", "WordReader::ReplaceRemaining(uint)", collisionExtraction));
var collisionProof = Path.Combine(root, "ParameterCollision.lean");
File.Delete(collisionProof);
Run(Cli("new-proof", collisionExtraction, collisionProof));
File.WriteAllText(collisionProof, Fill(File.ReadAllText(collisionProof), "ReplaceRemaining"));
VerifyWordReaderOutline(collisionExtraction, collisionProof, expected: true);

foreach (var shape in new[] { "UninitializedLocals", "EscapedLocal", "MixedLocals" })
{
    var changed = Path.Combine(root, shape + ".dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var reserve = module.GetType("Examples.WordReader").Methods.Single(method => method.Name == "Reserve");
        if (shape == "UninitializedLocals") reserve.Body.InitLocals = false;
        else if (shape == "MixedLocals")
            reserve.Body.Variables.Add(new VariableDefinition(module.GetType("Examples.WordReader")));
        else
        {
            reserve.ReturnType = new ByReferenceType(module.TypeSystem.UInt32);
            var returned = reserve.Body.Instructions.Last(instruction => instruction.OpCode == OpCodes.Ldloc_0);
            returned.OpCode = OpCodes.Ldloca_S;
            returned.Operand = reserve.Body.Variables[0];
        }
        module.Write(changed);
    }
    var extraction = Path.Combine(root, shape);
    var extracted = Execute(Extract("extract", changed, "Examples", "WordReader::Reserve()", extraction));
    if (shape == "EscapedLocal" && extracted.Code != 0)
    {
        if (!extracted.Output.Contains("unsupported", StringComparison.OrdinalIgnoreCase))
            throw new InvalidOperationException("Escaped-local extraction failed without an unsupported diagnostic:\n" +
                extracted.Output);
        continue;
    }
    if (extracted.Code != 0)
        throw new InvalidOperationException($"Unexpected {shape} extraction failure:\n{extracted.Output}");
    var outline = Path.Combine(root, shape + ".lean");
    File.Delete(outline);
    var generated = Execute(Cli("new-proof", extraction, outline));
    var diagnostic = generated.Output + (File.Exists(outline) ? File.ReadAllText(outline) : "");
    var expected = shape == "UninitializedLocals" ? "supported initial values" :
        shape == "EscapedLocal" ? "returns System.UInt32&" : "mixed";
    if (!diagnostic.Contains(expected, StringComparison.OrdinalIgnoreCase) ||
        generated.Code == 0 && !diagnostic.Contains("not outlined:", StringComparison.Ordinal))
        throw new InvalidOperationException($"The {shape} frame did not receive its named refusal:\n{diagnostic}");
}
Console.WriteLine("PASS saved-position helper and caller frames; field-preserving helper and mutation rejection");

static string[] Cli(params string[] arguments) => ["dotnet", ExtractorPath, .. arguments];

static string Fill(string source, string method)
{
    if (method == "ReadSaved")
    {
        source = FillWordReaderSpecification(source, skip: false);
        return source.Replace(
            "sorry -- Postcondition of the returned value, with `held3`, `held5` the stored fields", """
            dsimp only [Precondition] at assumed
              have next : (WordReader.Position.of initial wordReader + 1).toNat =
                  (WordReader.Position.of initial wordReader).toNat + 1 := by
                simp [BitVec.toNat_add]
                omega
              have consumed : (WordReader.Remaining.of initial wordReader - 1).toNat + 1 =
                  (WordReader.Remaining.of initial wordReader).toNat := by
                simp [BitVec.toNat_sub]
                omega
              dsimp only [Postcondition]
              refine ⟨?_, ?_⟩
              · simp [numericOfWidth, BitVec.ofNat_toNat, List.getElem?_eq_getElem, values1Read13Bound]
              · simp only [objectEntry.frame] at held3Final held5Final
                rw [held3Final.2, held5Final.2]
                exact ⟨next, consumed, by omega⟩
            """, StringComparison.Ordinal);
    }
    source = Regex.Replace(source, @"(def Precondition[\s\S]*?: Prop :=) sorry", "$1 True");
    if (method == "ReplaceRemainingWide")
    {
        source = Regex.Replace(source, @"(def Postcondition[\s\S]*?: Prop :=) sorry", """
            $1
              result.toNat = (WordReader.Remaining.of initial wordReader).toNat +
                (WordReader.Position.of initial wordReader).toNat ∧
              WordReader.Remaining.of final wordReader = remaining
            """);
        return source.Replace("sorry -- Postcondition of the returned value, with `held3` the stored fields", """
            constructor
              · have positionBound := (WordReader.Position.of initial wordReader).isLt
                have remainingBound := (WordReader.Remaining.of initial wordReader).isLt
                simp [BitVec.toNat_add, BitVec.toNat_setWidth]
                omega
              · simpa only [objectEntry.frame] using held3Final.2
            """, StringComparison.Ordinal);
    }
    var parameter = Regex.Match(source, @"def Precondition \(wordReader : Reference\) \((\w+) : W32\)")
        .Groups[1].Value;
    if (parameter.Length == 0) throw new InvalidOperationException("Missing replacement parameter in outline");
    source = Regex.Replace(source, @"(def Postcondition[\s\S]*?: Prop :=) sorry", """
        $1
          result = WordReader.Remaining.of initial wordReader +
            WordReader.Position.of initial wordReader ∧
          WordReader.Remaining.Holds final wordReader remaining
        """);
    source = source.Replace("WordReader.Remaining.Holds final wordReader remaining",
        $"WordReader.Remaining.Holds final wordReader {parameter}", StringComparison.Ordinal);
    return source.Replace("sorry -- Postcondition of the returned value, with `held3` the stored fields",
        "exact ⟨rfl, held3Final⟩", StringComparison.Ordinal);
}
