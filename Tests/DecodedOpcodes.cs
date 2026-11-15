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
