#!/usr/bin/env dotnet
#:property PublishAot=false
#:property AssemblyName=LeanCIL.IdentityTests
#:project ../Extractor/Extractor.csproj
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include GeneratedEvidence.cs

extern alias IdentityExtractor;

using System.Reflection;
using Mono.Cecil.Cil;
using IdentityExtractor::Nethermind.LeanCIL;

// The extractor predicts which methods Lean's decoder defines from its own opcode table. Lean decides that the
// table holds exactly the opcodes of `Instruction.valueOpcode`, so the prediction cannot drift from the decoder.
var opcodes = typeof(OpCodes).GetFields(BindingFlags.Public | BindingFlags.Static)
    .Select(field => (OpCode)field.GetValue(null)!).ToArray();
var table = opcodes.Where(opcode => GenericEvidence.DecodedOpcodes.Contains(opcode.Code))
    .Select(opcode => (ushort)opcode.Value).Order().ToArray();
if (table.Length != GenericEvidence.DecodedOpcodes.Count)
    throw new InvalidOperationException("A decoded opcode has no Cecil opcode value.");
var directory = At("artifacts/DecodedOpcodes");
Directory.CreateDirectory(directory);
var path = Path.Combine(directory, "Table.lean");
File.WriteAllText(path, $$"""
    import CIL.Extraction.ValueDecoding

    /-- The opcodes the extractor predicts `Instruction.ofRaw?` decodes. -/
    def table : List Nat := [{{string.Join(", ", table)}}]

    /-- Every one-byte opcode and every two-byte opcode `0xFE nn`, numbered as raw instructions are. -/
    def opcodes : List Nat := List.range 256 ++ (List.range 256).map (65024 + ·)

    /-- The table holds an opcode exactly when `Instruction.valueOpcode` does. -/
    theorem table_is_valueOpcode :
        (opcodes.all fun opcode =>
          CIL.Instruction.valueOpcode opcode == table.contains opcode) = true := by
      decide +kernel
    #print axioms table_is_valueOpcode
    """ + "\n");
Run(["lake", "env", "lean", path], cwd: FixturePackage());
Console.WriteLine($"PASS the extractor's {table.Length} decoded opcodes are those of Instruction.valueOpcode");

// The decoder reads every pc, but the feature check requires a hole at each pc the reachability certificate rules
// out, so a body of decoded opcodes with an unreachable tail must keep its literal and still build.
var deadDirectory = Path.Combine(directory, "UnreachableTail");
Directory.CreateDirectory(deadDirectory);
var deadAssembly = Path.Combine(deadDirectory, "Examples.dll");
// The examples assembly carries the identity and target framework extraction admits.
using (var module = Mono.Cecil.ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll")))
{
    var owner = new Mono.Cecil.TypeDefinition("Examples", "UnreachableTail", Mono.Cecil.TypeAttributes.Public |
        Mono.Cecil.TypeAttributes.Abstract | Mono.Cecil.TypeAttributes.Sealed, module.TypeSystem.Object);
    module.Types.Add(owner);
    var method = new Mono.Cecil.MethodDefinition("One",
        Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Int32);
    owner.Methods.Add(method);
    var il = method.Body.GetILProcessor();
    foreach (var opcode in new[] { OpCodes.Ldc_I4_1, OpCodes.Ret, OpCodes.Ldc_I4_0, OpCodes.Ret }) il.Emit(opcode);
    module.Write(deadAssembly);
}
var deadOutput = Path.Combine(deadDirectory, "Extraction");
Run(["dotnet", ExtractorPath, "extract", deadAssembly, "UnreachableTail::One()", deadOutput]);
var deadSource = Path.Combine(deadOutput, "Extracted.lean");
var deadText = File.ReadAllText(deadSource).ReplaceLineEndings("\n");
string[] literal = [.. ExtractedInstructions(deadText).Where(instruction => instruction.Method == 0)
    .Select(instruction => instruction.Op)];
string[] expectedLiteral =
    [".ldc_i4 1", ".ret", $".unadmitted {OpCodes.Ldc_I4_0.Value}", $".unadmitted {OpCodes.Ret.Value}"];
if (IsDecodedMethod(deadText, 0) ||
    !literal.SequenceEqual(expectedLiteral, StringComparer.Ordinal))
    throw new InvalidOperationException("A method with an unreachable tail must keep its literal with a hole " +
        "at each dead pc, found:\n" + string.Join('\n', literal));
Run(["lake", "env", "lean", deadSource], cwd: FixturePackage());
Console.WriteLine("PASS a method with an unreachable tail keeps its literal, with holes at its dead pcs, and builds");
