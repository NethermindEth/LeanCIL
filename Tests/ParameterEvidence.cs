#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include GeneratedEvidence.cs

using Mono.Cecil;
using Mono.Cecil.Cil;

var output = At("artifacts/ParameterEvidence");
Directory.CreateDirectory(output);
var evidence = new GeneratedEvidence(output, args.Contains("--measure", StringComparer.Ordinal));
Run(["lake", "build", "CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution"]);
Run(["lake", "env", "lean", "Tests/ExtractionParameters.lean"]);
var assembly = At("Examples/Assembly/bin/Examples.dll");
var samples = new[]
{
    "Arguments::Overwrite(uint,uint)", "Arguments::Alias(uint)", "Arguments::Address(uint)",
    "Arguments::Native(nint)", "Arguments::Narrow(byte)",
    "Arguments::ReassignReference(uint&,uint&)", "Arguments::Struct(Examples.Packet)", "Counter::Parameter(byte)"
};
foreach (var (selector, index) in samples.Select((selector, index) => (selector, index)))
{
    var folder = Path.Combine(output, index.ToString());
    Run(Extract("extract", assembly, "Examples", selector, folder));
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
    var longAssembly = Path.Combine(output, "LongArguments.dll");
    module.Write(longAssembly);
    foreach (var selector in samples.Take(3))
    {
        var folder = Path.Combine(output, "Long" + Array.IndexOf(samples, selector));
        Run(Extract("extract", longAssembly, "Examples", selector, folder));
        evidence.Add(Path.Combine(folder, "Extracted.lean"), "PASS checked extraction: " + selector);
    }
}

evidence.Check();
var baseline = File.ReadAllText(Path.Combine(output, "0", "Extracted.lean"));
void Reject(string name, string mutated)
{
    if (mutated == baseline) throw new InvalidOperationException("Mutation did not change generated source: " + name);
    var path = Path.Combine(output, name + ".lean");
    File.WriteAllText(path, mutated);
    var result = Execute(["lake", "env", "lean", path]);
    if (result.Code == 0 || !result.Output.Contains("decide"))
        throw new InvalidOperationException("Invalid home mapping was not rejected: " + name + "\n" + result.Output);
    Console.WriteLine("PASS parameter evidence rejects " + name);
}

// Mutate lookup lemmas along with code so their rfl proofs cannot cause the rejection.
Reject("omitted-home", baseline.Replace("[(0, .word32)]", "[]"));
Reject("wrong-slot", baseline.Replace(".setLocal 0", ".setLocal 1").Replace(".local 0", ".local 1"));
Reject("omitted-redirection", baseline.Replace(".local 0", ".arg 0"));
Reject("wrong-home-type", baseline.Replace("[(0, .word32)]", "[(0, .word64)]"));
Reject("omitted-raw-site", baseline.Replace(".load 1, .store 0, .load 0, .other", ".load 1, .other, .load 0, .other"));
Console.WriteLine("PASS complete parameter-home mapping, argument types, instance indices and long/short encodings");
