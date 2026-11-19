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
var instanceControl = Path.Combine(output, "StaticFieldLoad");
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
    // The decoded instance method homes argument 1 after the platform field load.
    var counter = module.GetType("Examples.Counter").Methods.Single(method => method.Name == "Parameter");
    var processor = counter.Body.GetILProcessor();
    var entry = counter.Body.Instructions[0];
    var endian = module.GetType("Examples.Capabilities").Methods.Single(method => method.Name == "Endian");
    var load = endian.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Ldsfld);
    processor.InsertBefore(entry, processor.Create(OpCodes.Ldsfld, (FieldReference)load.Operand));
    processor.InsertBefore(entry, processor.Create(OpCodes.Pop));
    var longAssembly = Path.Combine(output, "LongArguments.dll");
    module.Write(longAssembly);
    ExtractBatch("extract", "Examples", samples.Take(3).Select((selector, index) =>
        new GeneratedExtraction(longAssembly, selector, Path.Combine(output, "Long" + index)))
        .Append(new GeneratedExtraction(longAssembly, instanceParameter, instanceControl)));
    foreach (var selector in samples.Take(3))
    {
        var folder = Path.Combine(output, "Long" + Array.IndexOf(samples, selector));
        evidence.Add(Path.Combine(folder, "Extracted.lean"), "PASS checked extraction: " + selector);
    }
}

evidence.Add(Path.Combine(instanceControl, "Extracted.lean"), "PASS decoded instance parameter after a field load");
evidence.Check();
var decoded = File.ReadAllText(Path.Combine(output, "0", "Extracted.lean"));
var baseline = File.ReadAllText(Path.Combine(instanceControl, "Extracted.lean"));
if (!IsDecodedMethod(decoded, 0) || !IsDecodedMethod(baseline, 0))
    throw new InvalidOperationException("Both parameter controls must decode.");

const string obligation = "method0_parameters_validated";
void Reject(string name, string source, string before, string after)
{
    var control = NarrowEvidence(source, obligation);
    var mutated = control.Replace(before, after, StringComparison.Ordinal);
    if (mutated == control)
        throw new InvalidOperationException($"Missing parameter obligation for {name}");
    var path = Path.Combine(output, name + ".lean");
    File.WriteAllText(path, mutated);
    rejected.Add(path, $"PASS parameter evidence rejects {name}", "ParameterHomesValid");
}

// Argument 1 is the homed byte and argument 0 is the receiver.
void RejectMethod(string name, string update) =>
    Reject(name, baseline, "method0Reachable method0 :=", $$"""method0Reachable { method0 with {{update}} } :=""");
RejectMethod("omitted-home", "parameterHomes := []");
RejectMethod("wrong-home-type", "parameterHomes := [(1, .word32)]");
RejectMethod("wrong-argument", "code := method0.code.set 6 (.starg 0)");
RejectMethod("home-slot-store", "code := method0.code.set 6 (.stloc 0)");
RejectMethod("home-slot-load", "code := method0.code.set 2 (.ldloc 0)");
Reject("omitted-raw-site", decoded, "computedLayouts method0RawArguments method0Reachable",
    "computedLayouts { method0RawArguments with code := method0RawArguments.code.set 1 .other } method0Reachable");
rejected.Check();
Console.WriteLine("PASS complete parameter-home mapping, argument types, instance indices and long/short encodings");
