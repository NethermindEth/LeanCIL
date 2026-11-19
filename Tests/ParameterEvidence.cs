#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs

using Mono.Cecil;
using Mono.Cecil.Cil;

var output = At("artifacts/ParameterEvidence");
Directory.CreateDirectory(output);
var rejected = new RejectedEvidence(output);
var evidence = new GeneratedEvidence(output, args.Contains("--measure", StringComparer.Ordinal));
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution");
RequireLeanFixtures("Tests.ExtractionParameters");
var assembly = At("Examples/Assembly/bin/Examples.dll");
const string instanceParameter = "Counter::Parameter(byte)";
var literalControl = Path.Combine(output, "StringLoad");
var samples = new[]
{
    "Arguments::Overwrite(uint,uint)", "Arguments::Alias(uint)", "Arguments::Address(uint)",
    "Arguments::Native(nint)", "Arguments::Narrow(byte)",
    "Arguments::ReassignReference(uint&,uint&)", "Arguments::Struct(Examples.Packet)", instanceParameter
};
ExtractBatch("extract", "Examples", samples.Select((selector, index) =>
    new GeneratedExtraction(assembly, selector, Path.Combine(output, index.ToString()))));
foreach (var (selector, index) in samples.Select((selector, index) => (selector, index)))
{
    var folder = Path.Combine(output, index.ToString());
    evidence.Add(Path.Combine(folder, "Extracted.lean"), "PASS checked extraction: " + selector);
}

// C# uses short forms here; independently exercise long-form argument opcodes too.
using (var module = ModuleDefinition.ReadModule(assembly))
{
    foreach (var method in module.GetType("Examples.Arguments").Methods.Where(method => method.HasBody))
        foreach (var instruction in method.Body.Instructions)
        {
            if (instruction.OpCode.Code is Code.Ldarg_0 or Code.Ldarg_1 or Code.Ldarg_2 or Code.Ldarg_3)
            {
                var index = instruction.OpCode.Code switch { Code.Ldarg_0 => 0, Code.Ldarg_1 => 1, Code.Ldarg_2 => 2, _ => 3 };
                instruction.OpCode = OpCodes.Ldarg;
                instruction.Operand = method.Parameters[index];
            }
            else if (instruction.OpCode.Code == Code.Ldarg_S) instruction.OpCode = OpCodes.Ldarg;
            else if (instruction.OpCode.Code == Code.Starg_S) instruction.OpCode = OpCodes.Starg;
            else if (instruction.OpCode.Code == Code.Ldarga_S) instruction.OpCode = OpCodes.Ldarga;
        }
    // A string load is admitted and has no decoding, so this body keeps a literal with a hole at its first pc.
    var counter = module.GetType("Examples.Counter").Methods.Single(method => method.Name == "Parameter");
    var processor = counter.Body.GetILProcessor();
    var entry = counter.Body.Instructions[0];
    processor.InsertBefore(entry, processor.Create(OpCodes.Ldstr, "literal"));
    processor.InsertBefore(entry, processor.Create(OpCodes.Pop));
    var longAssembly = Path.Combine(output, "LongArguments.dll");
    module.Write(longAssembly);
    ExtractBatch("extract", "Examples", samples.Take(3).Select((selector, index) =>
        new GeneratedExtraction(longAssembly, selector, Path.Combine(output, "Long" + index)))
        .Append(new GeneratedExtraction(longAssembly, instanceParameter, literalControl)));
    foreach (var selector in samples.Take(3))
    {
        var folder = Path.Combine(output, "Long" + Array.IndexOf(samples, selector));
        evidence.Add(Path.Combine(folder, "Extracted.lean"), "PASS checked extraction: " + selector);
    }
}

evidence.Add(Path.Combine(literalControl, "Extracted.lean"), "PASS literal instance parameter after a string load");
evidence.Check();
var decoded = File.ReadAllText(Path.Combine(output, "0", "Extracted.lean"));
var baseline = File.ReadAllText(Path.Combine(literalControl, "Extracted.lean"));
if (!IsDecodedMethod(decoded, 0) || IsDecodedMethod(baseline, 0) || !DefinedMethods(baseline).Contains(0))
    throw new InvalidOperationException(
        "Overwrite must decode and the instance method with a string load must have a literal body");
void Reject(string name, string mutated, string? source = null)
{
    if (mutated == (source ?? baseline))
        throw new InvalidOperationException("Mutation did not change generated source: " + name);
    var path = Path.Combine(output, name + ".lean");
    File.WriteAllText(path, mutated);
    rejected.Add(path, "PASS parameter evidence rejects " + name, "decide");
}

// Argument 1 is the homed byte and argument 0 the receiver. Mutate lookup lemmas along with code so their rfl
// proofs cannot cause the rejection.
const string home = "[(1, .narrow .unsigned8)]";
Reject("omitted-home", baseline.Replace(home, "[]"));
Reject("wrong-argument", baseline.Replace(".starg 1", ".starg 0"));
// The home slot follows the declared locals, so naming it as a local is refused for a store and a load.
Reject("home-slot-store", baseline.Replace(".starg 1", ".stloc 0"));
Reject("home-slot-load", baseline.Replace(".ldarg 1", ".ldloc 0"));
Reject("wrong-home-type", baseline.Replace(home, "[(1, .word32)]"));
// The homes the decoder computes are checked against the raw argument sites as a literal's are.
Reject("omitted-raw-site",
    decoded.Replace(".load 1, .store 0, .load 0, .other", ".load 1, .other, .load 0, .other"), decoded);
rejected.Check();
Console.WriteLine("PASS complete parameter-home mapping, argument types, instance indices and long/short encodings");
