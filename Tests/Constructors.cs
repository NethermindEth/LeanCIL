#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Constructors");
Directory.CreateDirectory(root);
var cases = 0;
var queue = new GeneratedQueue(verification, assembly);

void Compare(string dll, string name, string suffix = "")
{
    var method = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Constructors")!.GetMethod(name)!;
    var output = Path.Combine(root, name + suffix);
    Directory.CreateDirectory(output);
    var claims = new List<string>();
    var values = name == "Default" ? new ulong[] { 0 } :
        [0, 1, 127, 128, 255, 65535, uint.MaxValue, 1UL << 32, long.MaxValue, 1UL << 63, ulong.MaxValue];
    foreach (var bits in values)
    {
        object[] inputs = name == "Default" ? [] : [bits];
        var invocation = $"CIL.Safety.invoke Extracted.program 128 0 [{(inputs.Length == 0 ? "" : $".scalar (.i64 {bits})")}] CIL.Safety.Memory.empty";
        try
        {
            var expected = (ulong)method.Invoke(null, inputs)!;
            claims.Add($"({invocation}).map Prod.snd = .ok [.scalar (.i64 {expected})]");
        }
        catch (TargetInvocationException error) when (error.InnerException is OverflowException)
        {
            claims.Add($"(match {invocation} with | .error fault => fault.fault = .arithmetic .overflow | .ok _ => False)");
        }
    }
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport CIL.Safety.Execution\nset_option maxRecDepth 8192\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) + " := by\n  exact " +
        (claims.Count == 1 ? "rfl" : "⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩") + "\nend ExampleProof\n");
    var selector = $"Constructors::{name}({(name == "Default" ? "" : "ulong")})";
    queue.Add(new(selector, proof, output, Assembly: dll), () =>
    {
        cases += claims.Count;
        Console.WriteLine($"PASS {name}{suffix}: {claims.Count} runtime comparisons");
    });
}

foreach (var name in new[] { "Read", "Packed", "Nested", "Default", "Checked" }) Compare(assembly, name);

// newobj itself zero-initializes storage, even when a constructor does not write it.
var zeroed = Path.Combine(root, "Zeroed.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var constructor = module.GetType("Examples.Counter").Methods.Single(m => m.Name == ".ctor");
    constructor.Body.Instructions.Clear();
    constructor.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
    module.Write(zeroed);
}
Compare(zeroed, "Read", "-Zeroed");
queue.Flush();

var contract = At("Examples/Proofs/ConstructorValue.lean");
verification.Verify(assembly, "Examples", "Constructors::Return(ulong)", contract, Path.Combine(root, "UniversalValue"));
var wrongOutput = Path.Combine(root, "WrongValue");
var failed = false;
try
{
    verification.Verify(assembly, "Examples", "Constructors::WrongReturn(ulong)", contract, wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    failed = true;
}
if (!failed || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Incorrect constructed value accepted");

// Writes Examples with Counter or its constructor rewritten by one named mutation.
string Mutate(string mutation, string output)
{
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using var module = ModuleDefinition.ReadModule(assembly);
    var type = module.GetType("Examples.Counter");
    var entry = module.GetType("Examples.Constructors").Methods.Single(m => m.Name == "Return");
    var instruction = entry.Body.Instructions.Single(i => i.OpCode.Code == Code.Newobj);
    var constructor = type.Methods.Single(m => m.Name == ".ctor");
    switch (mutation)
    {
        case "not-constructor": instruction.Operand = type.Methods.Single(m => m.Name == "WriteRead"); break;
        case "static": constructor.HasThis = false; constructor.IsStatic = true; break;
        case "class": type.BaseType = module.TypeSystem.Object; break;
        case "base":
            type.BaseType = new TypeReference("System", "Exception", module, module.TypeSystem.CoreLibrary);
            break;
        case "return": constructor.ReturnType = module.TypeSystem.Int32; break;
        case "cycle":
            constructor.Body.Instructions.Clear();
            var il = constructor.Body.GetILProcessor();
            il.Emit(OpCodes.Ldarg_1);
            il.Emit(OpCodes.Call, entry);
            il.Emit(OpCodes.Pop);
            il.Emit(OpCodes.Ret);
            break;
    }
    module.Write(dll);
    return dll;
}

foreach (var mutation in new[] { "not-constructor", "static", "base", "return", "cycle" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    var dll = Mutate(mutation, output);
    var result = Execute(Extract("extract", dll, "Examples", "Constructors::Return(ulong)", output));
    var marker = mutation switch
    {
        "cycle" => "Recursive managed dependency",
        "base" => "Only classes deriving from System.Object through admitted classes are modelled",
        _ => "Unsupported",
    };
    if (result.Code == 0 || !result.Output.Contains(marker) || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException($"Invalid constructor accepted: {mutation}\n{result.Output}");
}

// Counter re-declared as a class: newobj must allocate a heap instance charged to the heap
// budget, never construct struct storage.
var classOutput = Path.Combine(root, "Class");
var classDll = Mutate("class", classOutput);
var classExtraction = Path.Combine(classOutput, "Extraction");
Run(Extract("extract", classDll, "Examples", "Constructors::Return(ulong)", classExtraction));
var classLean = File.ReadAllText(Path.Combine(classExtraction, "Extracted.lean"));
if (!classLean.Contains(".newObject ", StringComparison.Ordinal) ||
    classLean.Contains(".newAggregate ", StringComparison.Ordinal))
    throw new InvalidOperationException("Class construction was not extracted as a heap allocation:\n" + classLean);
var classProof = Path.Combine(classOutput, "ClassProof.lean");
File.WriteAllText(classProof, """
import Extracted
import CIL.Safety.Execution
set_option maxRecDepth 8192
namespace ExampleProof
open CIL.Safety

/-- With heap budget `Return` yields an object reference; without, its 8-byte instance faults. -/
theorem correctness :
    (match invoke Extracted.program 128 0 [.scalar (.i64 5)]
        { Memory.empty with heapBudget := 64 } with
      | .ok (_, [.object (.address _)]) => true
      | _ => false) = true ∧
    (match invoke Extracted.program 128 0 [.scalar (.i64 5)] Memory.empty with
      | .error failure => failure.fault = .allocationFailure 8 0
      | .ok _ => False) := ⟨rfl, rfl⟩

end ExampleProof
""");
verification.Verify(classDll, "Examples", "Constructors::Return(ulong)", classProof,
    Path.Combine(classOutput, "Verified"));
Console.WriteLine("PASS class: newobj allocates a heap instance and faults without heap budget");

Console.WriteLine($"PASS {cases} constructor comparisons, universal value proof, class allocation and " +
    "five malformed constructor rejections");
