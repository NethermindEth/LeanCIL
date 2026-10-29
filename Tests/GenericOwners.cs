#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Reflection;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/GenericOwners");
Directory.CreateDirectory(root);
// Foreign owners cannot be serialized as distinct CLI slots; check the in-memory metadata boundary.
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var caller = module.Types.Single(type => type.Name == "GenericOwners").Methods
        .Single(method => method.Name == "Identity");
    var target = (MethodReference)caller.Body.Instructions.Single(instruction =>
        instruction.OpCode.Code == Code.Call).Operand;
    var foreignOwner = module.Types.Single(type => type.Name == "OwnerOuter`1");
    target.Resolve().Body.Variables.Add(new VariableDefinition(foreignOwner.GenericParameters[0]));
    var specialization = Assembly.LoadFrom(ExtractorPath).GetType("Nethermind.LeanCIL.MethodSpecialization")!;
    var instance = Activator.CreateInstance(specialization, BindingFlags.Instance | BindingFlags.Public |
        BindingFlags.NonPublic, null, [module, "scalar"], null)!;
    try
    {
        specialization.GetMethod("Instantiate", BindingFlags.Instance | BindingFlags.NonPublic)!
            .Invoke(instance, [target]);
        throw new InvalidOperationException("Foreign generic owner was accepted");
    }
    catch (TargetInvocationException error) when (error.InnerException is InvalidDataException invalid &&
        invalid.Message.Contains("Foreign generic parameter owner", StringComparison.Ordinal))
    {
        Console.WriteLine("PASS rejected foreign generic parameter owner");
    }
}
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution");
var evidence = new GeneratedEvidence(root);
var rejected = new RejectedEvidence(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.GenericOwners")!;

string ChangeDefinition(string source, string name, Func<string, string> change)
{
    var matches = Regex.Matches(source, @"(?m)^def " + Regex.Escape(name) + @" : [^\r\n]+\r?$");
    if (matches.Count != 1) throw new InvalidOperationException("Missing unique definition: " + name);
    var match = matches[0];
    var replacement = change(match.Value);
    if (replacement == match.Value) throw new InvalidOperationException("Mutation did not change " + name);
    return source[..match.Index] + replacement + source[(match.Index + match.Length)..];
}

foreach (var name in new[] { "Identity", "Combined", "Nested", "Repeated", "Address" })
{
    var expected = name == "Repeated" ? 84u : 42u;
    if (!Equals(runtime.GetMethod(name)!.Invoke(null, [42u]), expected))
        throw new InvalidOperationException("Unexpected CLR generic-owner result: " + name);
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"GenericOwners::{name}(uint)", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    if (Regex.Matches(source, @"(?m)^def method\d+ : Method :=").Count != 2)
        throw new InvalidOperationException("Closed specialization was duplicated: " + name);
    var proof = source + $$"""

        /-- The compiled closed-owner call agrees with the CLR, including repeated cached calls. -/
        theorem generic_owner_result :
            (CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i32 42)]
              { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩,
                views := [], nextIdentity := 0 }).map Prod.snd = .ok [.scalar (.i32 {{expected}})] := rfl
        #print axioms generic_owner_result
        """;
    if (name == "Combined")
    {
        var specialization = NarrowEvidence(source, "method1_specialization_validated");
        var calls = NarrowEvidence(source, "method0_calls_validated");
        proof += "\n" + CheckedEvidenceControl(source, specialization, ["method1_specialization_validated"], 0);
        proof += "\n" + CheckedEvidenceControl(source, calls, ["method0_calls_validated"], 1);
        var cases = new (string Name, string Source)[]
        {
            ("swapped", ChangeDefinition(specialization, "method1TypeArgumentsRaw", line =>
                line.Replace("System.UInt32", "TemporaryType", StringComparison.Ordinal)
                    .Replace("System.UInt64", "System.UInt32", StringComparison.Ordinal)
                    .Replace("TemporaryType", "System.UInt64", StringComparison.Ordinal))),
            ("omitted", ChangeDefinition(specialization, "method1TypeArgumentsRaw", line =>
                line.Replace(", .atom Extraction.runtimeScope \"System.UInt64\"", "", StringComparison.Ordinal))),
            ("arity", ChangeDefinition(calls, "method0Closed", line =>
                line.Replace("ownerArgumentCount := 1", "ownerArgumentCount := 0", StringComparison.Ordinal))),
            ("owner", ChangeDefinition(calls, "method0Closed", line =>
                line.Replace("Examples.OwnerHelper", "Examples.OwnerOuter", StringComparison.Ordinal)))
        };
        foreach (var mutation in cases)
        {
            var path = Path.Combine(root, mutation.Name + ".lean");
            File.WriteAllText(path, mutation.Source);
            rejected.Add(path, "PASS independently rejected generic owner evidence: " + mutation.Name);
        }
    }
    var proofPath = Path.Combine(root, name + ".lean");
    File.WriteAllText(proofPath, proof);
    evidence.Add(proofPath, "PASS closed generic owner: " + name);
}
evidence.Check();
rejected.Check();
