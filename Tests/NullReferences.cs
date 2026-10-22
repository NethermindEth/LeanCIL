#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/NullReferences");
Directory.CreateDirectory(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly));
var owner = runtime.GetType("Examples.NullReferences")!;
var limbs = runtime.GetType("Examples.FourLimbs")!;
using var source = ModuleDefinition.ReadModule(assembly);
var methods = source.GetType("Examples.NullReferences").Methods;
Run(["lake", "build", "Tests.UnsafeCallEvidence"]);

// Every byte of the caller's 32-byte struct is 0x25, so each limb is 0x2525252525252525.
const string memory = """
def memory : CIL.Safety.Memory := { Examples.caller with
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨32, 1, []⟩, true, [32]⟩ else none
  cells := fun _ _ => ⟨37, true⟩
  views := [⟨0, 0, 32, true, true⟩] }
""";
object caller = Activator.CreateInstance(limbs)!;
limbs.GetField("A")!.SetValue(caller, 0x2525252525252525UL);

// .NET decides each outcome; a NullReferenceException must be the modelled null-dereference fault at `fault`.
string Claim(string name, object[] input, string args, string state, string fault)
{
    string outcome;
    try
    {
        outcome = owner.GetMethod(name)!.Invoke(null, input) switch
        {
            null => ".ok []",
            bool value => $".ok [.scalar (.i32 {(value ? 1 : 0)})]",
            ulong value => $".ok [.scalar (.i64 {value})]",
            var value => throw new InvalidOperationException($"Unexpected result {value} from {name}")
        };
    }
    catch (TargetInvocationException error) when (error.InnerException is NullReferenceException)
    {
        if (fault.Length == 0) throw new InvalidOperationException($"{name} unexpectedly dereferenced null");
        outcome = $".error ⟨0, {fault}⟩";
    }
    return $"(CIL.Safety.invoke Extracted.program 16 0 [{args}] {state}).map Prod.snd = {outcome}";
}

var cases = new (string Name, string[] Claims)[]
{
    ("IsNull", [Claim("IsNull", [], "", "Examples.empty", "")]),
    ("IsLive", [Claim("IsLive", [0UL], "Examples.reference", "Examples.caller", "")]),
    ("Read", [Claim("Read", [], "", "Examples.empty", "1, .memory .nullDereference .null 8")]),
    ("Write", [Claim("Write", [7UL], ".scalar (.i64 7)", "Examples.empty", "2, .memory .nullDereference .null 0")]),
    ("ReadField", [Claim("ReadField", [], "", "Examples.empty", "1, .memory .nullDereference .null 0")]),
    ("WriteField", [Claim("WriteField", [7UL], ".scalar (.i64 7)", "Examples.empty", "2, .memory .nullDereference .null 0")]),
    ("Optional", [
        Claim("Optional", [caller, false], "Examples.reference, .scalar (.i32 0)", "memory", ""),
        Claim("Optional", [caller, true], "Examples.reference, .scalar (.i32 1)", "memory", "")]),
    ("Unchecked", [
        Claim("Unchecked", [caller, false], "Examples.reference, .scalar (.i32 0)", "memory", "7, .memory .nullDereference .null 0"),
        Claim("Unchecked", [caller, true], "Examples.reference, .scalar (.i32 1)", "memory", "")])
};
var requests = cases.Select(item =>
{
    var output = Path.Combine(root, item.Name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + memory +
        "\ntheorem correctness :\n" + string.Join(" ∧\n", item.Claims) + " := by\n  exact " +
        (item.Claims.Length == 1 ? "rfl" : "⟨" + string.Join(", ", item.Claims.Select(_ => "rfl")) + "⟩") + "\nend ExampleProof\n");
    return new GeneratedVerification(methods.Single(m => m.Name == item.Name).FullName, proof, output);
}).ToArray();
verification.VerifyGeneratedBatch(assembly, "Examples", requests);
foreach (var item in cases) Console.WriteLine($"PASS {item.Name}: {item.Claims.Length} runtime comparisons");

// An operation with the helper's stack effect cannot stand in for it: only the call binding rejects these.
foreach (var (name, helper, forgery) in new[]
{
    ("IsNull", ".memory .nullRef", ".const64 0"),
    ("IsLive", ".memory .isNullRef", ".memory .asRef")
})
{
    var extracted = File.ReadAllText(Path.Combine(root, name, "Extracted.lean"));
    if (!extracted.Contains(helper)) throw new InvalidOperationException($"{name} does not emit {helper}");
    var mutated = Path.Combine(root, name + "-forged.lean");
    File.WriteAllText(mutated, extracted.Replace(helper, forgery));
    var result = Execute(["lake", "env", "lean", mutated]);
    if (result.Code == 0 || !result.Output.Contains("Extraction.UnsafeCallsValid rawLayouts method0Closed") ||
        !result.Output.Contains("is false") || result.Output.Contains("FeatureFlowValid"))
        throw new InvalidOperationException($"Forged {helper} was accepted for {name}\n{result.Output}");
    Console.WriteLine($"PASS {name}: forged {helper} rejected by the call binding");
}

foreach (var (name, selector) in new[] { ("Read", "NullReferences::Read()"), ("IsLive", "NullReferences::IsLive(ulong&)") })
foreach (var mutation in new[] { "class", "float", "void", "byref", "pointer", "arity", "parameter", "return", "instance", "scope", "version" })
{
    var output = Path.Combine(root, $"Reject-{name}-{mutation}");
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.NullReferences").Methods.Single(m => m.Name == name);
        var call = (GenericInstanceMethod)method.Body.Instructions.Single(i => i.Operand is MethodReference).Operand;
        switch (mutation)
        {
            case "class": call.GenericArguments[0] = module.TypeSystem.String; break;
            case "float": call.GenericArguments[0] = module.TypeSystem.Single; break;
            case "void": call.GenericArguments[0] = module.TypeSystem.Void; break;
            case "byref": call.GenericArguments[0] = new ByReferenceType(module.TypeSystem.Int32); break;
            case "pointer": call.GenericArguments[0] = new PointerType(module.TypeSystem.Int32); break;
            case "arity": call.GenericArguments.Add(module.TypeSystem.Int32); break;
            case "parameter":
                if (call.Parameters.Count == 0) call.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
                else call.Parameters[0].ParameterType = module.TypeSystem.Int32;
                break;
            case "return": call.ReturnType = module.TypeSystem.Int32; break;
            case "instance": call.ElementMethod.HasThis = true; break;
            case "scope": call.DeclaringType.Scope = module; break;
            case "version": ((AssemblyNameReference)call.DeclaringType.Scope).Version = new Version(9, 0, 0, 0); break;
        }
        module.Write(dll);
    }
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var result = Execute(Extract("extract", dll, "Examples", selector, output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !(result.Output.Contains("Unsupported") || result.Output.Contains("Unmodelled") || result.Output.Contains("Unresolved") ||
          result.Output.Contains("Invalid evaluation stack during reachability")))
        throw new InvalidOperationException($"Incorrect {name} rejection: {mutation}\n{result.Output}");
    Console.WriteLine($"PASS {name} rejection: {mutation}");
}
Console.WriteLine("PASS null references: detection, faulting accesses, optional references, forged bindings and metadata rejection");
