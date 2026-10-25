#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var queue = new GeneratedQueue(verification, assembly);
var root = At("artifacts/UnsafeReferences");
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
    queue.Add(new(selector, proof, output),
        () => Console.WriteLine("PASS checked byref reinterpretation: " + name));
}
foreach (var name in new[] { "Word", "Half", "Vector", "Mutable" })
    Prove(name, $"UnsafeReferences::{name}(Examples.FourLimbs&)",
        "CIL.Safety.invoke Extracted.program 4 0 [Examples.reference] memory = .ok (memory, [Examples.reference])");
Prove("Null", "UnsafeReferences::Word(Examples.FourLimbs&)",
    "CIL.Safety.invoke Extracted.program 4 0 [.reference .null] memory = .ok (memory, [.reference .null])");
Prove("Expired", "UnsafeReferences::Word(Examples.FourLimbs&)",
    "CIL.Safety.invoke Extracted.program 4 0 [Examples.reference] (CIL.Safety.expire memory 0) = .error ⟨0, 0, .memory .expiredLifetime (.address ⟨0, 0⟩) 0⟩");
Prove("VectorUninitialized", "UnsafeReferences::ReadHalf(Examples.FourLimbs&)",
    "CIL.Safety.invoke Extracted.program 8 0 [Examples.reference] memory = .ok (memory, [.scalar (.snapshot .vector128 (List.replicate 16 (37, false)))])");
Prove("VectorBounds", "UnsafeReferences::ReadHalf(Examples.FourLimbs&)", """
    CIL.Safety.invoke Extracted.program 8 0 [Examples.reference]
      { memory with
        allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
        views := [⟨0, 0, 8, true, true⟩] } =
      .error ⟨0, 2, .memory .outsideAllocation (.address ⟨0, 0⟩) 16⟩
    """);
verification.Verify(assembly, "Examples", "UnsafeReferences::Word(Examples.FourLimbs&)",
    At("Examples/Proofs/UnsafeReference.lean"), Path.Combine(root, "Preservation"));
Console.WriteLine("PASS reference reinterpretation preserves arbitrary caller memory and provenance");
Prove("Store", "UnsafeReferences::Store(Examples.FourLimbs&,ulong,ulong,ulong,ulong)", """
    (CIL.Safety.invoke Extracted.program 32 0
      [Examples.reference, .scalar (.i64 1), .scalar (.i64 2), .scalar (.i64 3), .scalar (.i64 18446744073709551615)] memory).map
      (fun (final, values) => (values, [0, 8, 16, 24].map fun offset =>
        CIL.Safety.loadValue final (.address ⟨0, offset⟩) 8)) =
      .ok ([.scalar (.i64 18446744073709551615)], [.ok (.i64 1), .ok (.i64 2), .ok (.i64 3), .ok (.i64 18446744073709551615)])
    """);
Prove("Uninitialized", "UnsafeReferences::Read(Examples.FourLimbs&)",
    "CIL.Safety.invoke Extracted.program 8 0 [Examples.reference] memory = .error ⟨0, 2, .memory .uninitialized (.address ⟨0, 0⟩) 8⟩");
Prove("PastEnd", "UnsafeReferences::PastEnd(Examples.FourLimbs&)",
    "CIL.Safety.invoke Extracted.program 8 0 [Examples.reference] memory = .error ⟨0, 4, .memory .outsideAllocation (.address ⟨0, 32⟩) 8⟩");
queue.Flush();

foreach (var mutation in new[] { "reference-field", "class", "pointer", "arity", "parameter", "return", "instance", "scope", "version" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.UnsafeReferences").Methods.Single(m => m.Name == "Word");
        var call = (GenericInstanceMethod)method.Body.Instructions.Single(i => i.Operand is MethodReference).Operand;
        switch (mutation)
        {
            case "reference-field": module.GetType("Examples.FourLimbs").Fields[0].FieldType = module.TypeSystem.String; break;
            case "class": call.GenericArguments[1] = module.TypeSystem.String; break;
            case "pointer": call.GenericArguments[1] = new PointerType(module.TypeSystem.UInt64); break;
            case "arity": call.GenericArguments.Add(module.TypeSystem.UInt64); break;
            case "parameter": call.Parameters[0].ParameterType = module.TypeSystem.UInt64; break;
            case "return": call.ReturnType = new ByReferenceType(call.ElementMethod.GenericParameters[0]); break;
            case "instance": call.ElementMethod.HasThis = true; break;
            case "scope": call.DeclaringType.Scope = module; break;
            case "version": ((AssemblyNameReference)call.DeclaringType.Scope).Version = new Version(9, 0, 0, 0); break;
        }
        module.Write(dll);
    }
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var result = Execute(Extract("extract", dll, "Examples", "UnsafeReferences::Word(Examples.FourLimbs&)", output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException("Unsafe byref mutation accepted: " + mutation);
    Console.WriteLine("PASS unsafe byref rejection: " + mutation);
}
