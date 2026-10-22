#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/SkipInitialization");
Directory.CreateDirectory(root);
Run(["lake", "build", "Tests.UnsafeCallEvidence"]);

verification.Verify(assembly, "Examples", "SkipInitialization::Skip(Examples.FourLimbs&)",
    At("Examples/Proofs/SkipInitialization.lean"), Path.Combine(root, "Skip"));
Console.WriteLine("PASS compiled SkipInit preserves caller bytes and initialization flags");

const string memory = """
def memory : CIL.Safety.Memory := { Examples.caller with
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨32, 1, []⟩, true, [32]⟩ else none
  cells := fun _ _ => ⟨37, false⟩
  views := [⟨0, 0, 32, true, true⟩] }
""";
void Prove(string name, string selector, string claim)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + memory +
        "\ntheorem correctness : " + claim + " := by rfl\nend ExampleProof\n");
    verification.Verify(assembly, "Examples", selector, proof, output);
    Console.WriteLine("PASS " + name);
}

Prove("Read", "SkipInitialization::Read(ulong&)",
    "CIL.Safety.invoke Extracted.program 8 0 [Examples.reference] memory = " +
    ".error ⟨0, 3, .memory .uninitialized (.address ⟨0, 0⟩) 8⟩");
Prove("Store", "SkipInitialization::Store(Examples.FourLimbs&,ulong,ulong,ulong,ulong)", """
    (CIL.Safety.invoke Extracted.program 32 0
      [Examples.reference, .scalar (.i64 1), .scalar (.i64 2), .scalar (.i64 3), .scalar (.i64 4)] memory).map
      (fun (final, values) => (values, [0, 8, 16, 24].map fun offset =>
        CIL.Safety.loadValue final (.address ⟨0, offset⟩) 8)) =
      .ok ([], [.ok (.i64 1), .ok (.i64 2), .ok (.i64 3), .ok (.i64 4)])
    """);

foreach (var mutation in new[] { "class", "float", "void", "byref", "pointer", "arity", "parameter", "return", "instance", "scope", "version" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.SkipInitialization").Methods.Single(m => m.Name == "Skip");
        var call = (GenericInstanceMethod)method.Body.Instructions.Single(i => i.Operand is MethodReference).Operand;
        switch (mutation)
        {
            case "class": call.GenericArguments[0] = module.TypeSystem.String; break;
            case "float": call.GenericArguments[0] = module.TypeSystem.Single; break;
            case "void": call.GenericArguments[0] = module.TypeSystem.Void; break;
            case "byref": call.GenericArguments[0] = new ByReferenceType(module.TypeSystem.Int32); break;
            case "pointer": call.GenericArguments[0] = new PointerType(module.TypeSystem.Int32); break;
            case "arity": call.GenericArguments.Add(module.TypeSystem.Int32); break;
            case "parameter": call.Parameters[0].ParameterType = module.TypeSystem.Int32; break;
            case "return": call.ReturnType = module.TypeSystem.Int32; break;
            case "instance": call.ElementMethod.HasThis = true; break;
            case "scope": call.DeclaringType.Scope = module; break;
            case "version": ((AssemblyNameReference)call.DeclaringType.Scope).Version = new Version(9, 0, 0, 0); break;
        }
        module.Write(dll);
    }
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var result = Execute(Extract("extract", dll, "Examples", "SkipInitialization::Skip(Examples.FourLimbs&)", output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !(result.Output.Contains("Unsupported") || result.Output.Contains("Unmodelled") || result.Output.Contains("Unresolved") ||
          (mutation == "instance" && result.Output.Contains("Invalid evaluation stack during reachability"))))
        throw new InvalidOperationException("Incorrect SkipInit rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS SkipInit rejection: " + mutation);
}
