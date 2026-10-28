#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using Mono.Cecil;
using System.Reflection;
using System.Runtime.CompilerServices;

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
        "\ntheorem correctness : " + claim + " := by rfl\n#print axioms correctness\nend ExampleProof\n");
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

var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.UnsafeReferences")!;
var bytes = new byte[32];
foreach (var name in new[] { "AreSame", "Less", "Greater", "ByteOffset", "AddSigned", "AddUnsigned", "Subtract" })
{
    var offset = name is "AddSigned" or "AddUnsigned" or "Subtract";
    var selector = $"UnsafeReferences::{name}(System.Byte&," +
        (offset ? name == "AddUnsigned" ? "System.UIntPtr)" : "System.IntPtr)" : "System.Byte&)");
    var method = runtime.GetMethod(name)!;
    long expected;
    if (name == "ByteOffset")
        expected = method.CreateDelegate<ReferenceDifference>()(ref bytes[5], ref bytes[2]);
    else if (offset)
    {
        ref var result = ref (name == "AddUnsigned"
            ? ref method.CreateDelegate<UnsignedReferenceOffset>()(ref bytes[5], 3)
            : ref method.CreateDelegate<SignedReferenceOffset>()(ref bytes[5], 3));
        expected = Unsafe.ByteOffset(ref bytes[0], ref result);
    }
    else expected = method.CreateDelegate<ReferenceComparison>()(ref bytes[5], ref bytes[2]) ? 1 : 0;
    var argument = offset ? ".scalar (.i64 3)" : ".reference (.address ⟨0, 2⟩)";
    var resultValue = offset ? $".reference (.address ⟨0, {expected}⟩)" :
        $".scalar (.{(name == "ByteOffset" ? "i64" : "i32")} ({expected}))";
    Prove(name, selector,
        $"CIL.Safety.invoke Extracted.program 8 0 [.reference (.address ⟨0, 5⟩), {argument}] memory = " +
        $".ok (memory, [{resultValue}])");
}
void Boundary(string name, string theorem, string arguments, string result, string initial = "memory")
{
    File.AppendAllText(Path.Combine(root, name, "Proof.lean"), $$"""

        namespace ExampleProof
        /-- Reference helpers retain checked allocation boundaries without granting authority. -/
        theorem {{theorem}} : CIL.Safety.invoke Extracted.program 8 0
            {{arguments}} ({{initial}}) = {{result}} := by rfl
        #print axioms {{theorem}}
        end ExampleProof

        """);
}
const string backward = ".ok (memory, [.scalar (.i64 (-3))])";
Boundary("ByteOffset", "readonly_difference",
    "[.readOnlyReference (.address ⟨0, 5⟩), .readOnlyReference (.address ⟨0, 2⟩)]", backward);
Boundary("ByteOffset", "difference_needs_no_authority",
    "[.reference (.address ⟨0, 5⟩), .reference (.address ⟨0, 2⟩)]",
    ".ok ({ memory with views := [] }, [.scalar (.i64 (-3))])", "{ memory with views := [] }");
Boundary("ByteOffset", "end_pointer_difference",
    "[.reference (.address ⟨0, 32⟩), .reference (.address ⟨0, 0⟩)]",
    ".ok (memory, [.scalar (.i64 (-32))])");
Boundary("ByteOffset", "cross_allocation_unsupported",
    "[.reference (.address ⟨0, 5⟩), .reference (.address ⟨1, 2⟩)]",
    ".error ⟨0, 2, .unsupported \"Cross-allocation pointer arithmetic\"⟩",
    "{ memory with allocations := fun _ => some ⟨.callerStack, ⟨32, 1, []⟩, true, [32]⟩ }");
Boundary("ByteOffset", "expired_difference",
    "[.reference (.address ⟨0, 5⟩), .reference (.address ⟨0, 2⟩)]",
    ".error ⟨0, 2, .memory .expiredLifetime (.address ⟨0, 2⟩) 0⟩", "CIL.Safety.expire memory 0");
Boundary("AreSame", "null_equality", "[.reference .null, .reference .null]",
    ".ok (memory, [.scalar (.i32 1)])");
Boundary("AddSigned", "negative_byte_offset", "[.reference (.address ⟨0, 5⟩), .scalar (.i64 (-3))]",
    ".ok (memory, [.reference (.address ⟨0, 2⟩)])");
Boundary("AddUnsigned", "end_byte_offset", "[.reference (.address ⟨0, 5⟩), .scalar (.i64 27)]",
    ".ok (memory, [.reference (.address ⟨0, 32⟩)])");
Boundary("AddUnsigned", "outside_byte_offset", "[.reference (.address ⟨0, 5⟩), .scalar (.i64 28)]",
    ".error ⟨0, 2, .memory .outsideAllocation (.address ⟨0, 5⟩) 0⟩");
Boundary("Subtract", "negative_subtraction", "[.reference (.address ⟨0, 5⟩), .scalar (.i64 (-3))]",
    ".ok (memory, [.reference (.address ⟨0, 8⟩)])");
queue.Flush();

var rejected = new RejectedEvidence(Path.Combine(root, "EvidenceRejections"));
foreach (var (name, before, after) in new[]
{
    ("AreSame", ".eq", ".ltu"),
    ("ByteOffset", ".memory .byteOffset", ".sub"),
    ("AddSigned", ".memory (.add 1 true)", ".memory (.add 8 true)"),
    ("AddUnsigned", ".memory (.add 1 false)", ".memory (.add 1 true)"),
    ("Subtract", ".sub", ".add")
})
{
    var source = File.ReadAllText(Path.Combine(root, name, "Extracted.lean"));
    var narrowed = NarrowEvidence(source, "method0_unsafe_validated");
    if (!narrowed.Contains(before, StringComparison.Ordinal))
        throw new InvalidOperationException("Missing mutation target: " + name);
    var path = Path.Combine(root, name, "WrongOperation.lean");
    File.WriteAllText(path, narrowed.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(path, "PASS exact Unsafe operation rejection: " + name, "UnsafeCallsValid");
}
var byteOffsetSource = NarrowEvidence(File.ReadAllText(Path.Combine(root, "ByteOffset", "Extracted.lean")),
    "method0_unsafe_validated");
foreach (var (name, before, after) in new[]
{
    ("scope", "declaringType := .atom Extraction.runtimeScope", "declaringType := .atom \"forged\""),
    ("identity", "target := .external externalIdentity0", "target := .external \"forged\""),
    ("result", "returnType := .atom Extraction.runtimeScope \"System.IntPtr\"",
        "returnType := .atom Extraction.runtimeScope \"System.UIntPtr\""),
    ("generic", "typeArguments := [.atom Extraction.runtimeScope \"System.Byte\"]",
        "typeArguments := [.byref (.atom Extraction.runtimeScope \"System.Byte\")]")
})
{
    if (!byteOffsetSource.Contains(before, StringComparison.Ordinal))
        throw new InvalidOperationException("Missing identity mutation target: " + name);
    var path = Path.Combine(root, "ByteOffset", "Wrong-" + name + ".lean");
    File.WriteAllText(path, byteOffsetSource.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(path, "PASS exact Unsafe identity rejection: " + name, "UnsafeCallsValid");
}
rejected.Check();

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

foreach (var mutation in new[] { "parameter", "return", "generic", "scope" })
{
    var output = Path.Combine(root, "Reject-ByteOffset-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.UnsafeReferences").Methods.Single(method => method.Name == "ByteOffset");
        var call = (GenericInstanceMethod)method.Body.Instructions.Single(i => i.Operand is MethodReference).Operand;
        switch (mutation)
        {
            case "parameter": call.Parameters[1].ParameterType = module.TypeSystem.IntPtr; break;
            case "return": call.ReturnType = module.TypeSystem.UIntPtr; break;
            case "generic": call.GenericArguments[0] = module.TypeSystem.String; break;
            case "scope": call.DeclaringType.Scope = module; break;
        }
        module.Write(dll);
    }
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var result = Execute(Extract("extract", dll, "Examples",
        "UnsafeReferences::ByteOffset(System.Byte&,System.Byte&)", output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException("Unsafe ByteOffset mutation accepted: " + mutation);
    Console.WriteLine("PASS unsafe ByteOffset metadata rejection: " + mutation);
}

delegate bool ReferenceComparison(ref byte origin, ref byte target);
delegate nint ReferenceDifference(ref byte origin, ref byte target);
delegate ref byte SignedReferenceOffset(ref byte origin, nint offset);
delegate ref byte UnsignedReferenceOffset(ref byte origin, nuint offset);
