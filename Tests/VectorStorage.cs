#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Reflection;
using System.Runtime.Intrinsics;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var root = At("artifacts/VectorStorage");
var source = Path.Combine(root, "Assembly");
Directory.CreateDirectory(source);
File.WriteAllText(Path.Combine(source, "Storage.csproj"), """
<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework><AllowUnsafeBlocks>true</AllowUnsafeBlocks><Optimize>true</Optimize></PropertyGroup></Project>
""");
var elements = new[] { ("byte", typeof(byte)), ("int", typeof(int)), ("uint", typeof(uint)),
    ("long", typeof(long)), ("ulong", typeof(ulong)) };
var cases = (from bits in new[] { 128, 256, 512 } from element in elements
    select (Bits: bits, Element: element.Item1, Type: element.Item2)).ToArray();
var methods = cases.Select(item => $$"""
    public static Vector{{item.Bits}}<{{item.Element}}> Roundtrip{{item.Bits}}{{item.Element}}(
        ref Vector{{item.Bits}}<{{item.Element}}> destination, Vector{{item.Bits}}<{{item.Element}}> value)
    {
        destination = default;
        value = Pass(value);
        destination = value;
        var saved = destination;
        return Pass(saved);
    }
    """);
var copies = new[] { 128, 256, 512 }.Select(bits =>
    $"public static Vector{bits}<uint> Copy{bits}(ref Vector{bits}<uint> destination, " +
    $"ref Vector{bits}<uint> source) {{ destination = source; return destination; }}");
var fields = new[] { 128, 256 }.Select(bits => $$"""
    [StructLayout(LayoutKind.Explicit, Pack = 1, Size = {{bits / 8 + 3}})]
    public struct Holder{{bits}} { [FieldOffset(3)] public Vector{{bits}}<uint> Value; }
    public static Vector{{bits}}<uint> Field{{bits}}(ref Holder{{bits}} holder, Vector{{bits}}<uint> value)
    { holder.Value = value; return holder.Value; }
    """);
File.WriteAllText(Path.Combine(source, "Storage.cs"),
    "using System.Runtime.Intrinsics; using System.Runtime.InteropServices;\n" +
    "public static unsafe class Storage {\n" +
    "static T Pass<T>(T value) where T : unmanaged => value;\n" +
    string.Join('\n', methods.Concat(copies).Concat(fields)) +
    "\npublic static int Sizes() => " + string.Join(" + ", cases.Select(item =>
        $"sizeof(Vector{item.Bits}<{item.Element}>)")) + ";\n}\n");
Run(["dotnet", "build", Path.Combine(source, "Storage.csproj"), "-c", "Release"]);
var assembly = Path.Combine(root, "Storage.dll");
using (var module = ModuleDefinition.ReadModule(Path.Combine(source, "bin/Storage.dll")))
{
    // Roslyn can choose ldobj/stobj; exercise the independently specified cpobj form too.
    foreach (var method in module.GetType("Storage").Methods.Where(method => method.Name.StartsWith("Copy")))
    {
        method.Body.Instructions.Clear();
        method.Body.Variables.Clear();
        var il = method.Body.GetILProcessor();
        il.Append(il.Create(OpCodes.Ldarg_0));
        il.Append(il.Create(OpCodes.Ldarg_1));
        il.Append(il.Create(OpCodes.Cpobj, method.ReturnType));
        il.Append(il.Create(OpCodes.Ldarg_0));
        il.Append(il.Create(OpCodes.Ldobj, method.ReturnType));
        il.Append(il.Create(OpCodes.Ret));
    }
    module.Write(assembly);
}
using var metadata = ModuleDefinition.ReadModule(assembly);
var selectors = metadata.GetType("Storage").Methods.ToDictionary(method => method.Name, method => method.FullName);
var runtime = Assembly.LoadFile(assembly).GetType("Storage")!;
var pending = new GeneratedQueue(verification, assembly, "Storage");
Run(["lake", "env", "lean", At("Tests/VectorStorage.lean")], cwd: FixturePackage());

object RuntimeVector(int bits, Type element)
{
    var factory = bits switch { 128 => typeof(Vector128), 256 => typeof(Vector256), _ => typeof(Vector512) };
    var create = factory.GetMethods().Single(method => method.Name == "Create" && method.IsGenericMethodDefinition &&
        method.GetParameters() is [{ ParameterType.IsGenericParameter: true }]);
    return create.MakeGenericMethod(element).Invoke(null, [Convert.ChangeType(7, element)])!;
}

void Prove(string name, int width, int offset = 0, bool copy = false)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    var size = width + offset;
    var definitions = $"def memory : CIL.Safety.Memory := {{ Examples.empty with\n" +
        $"  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨{size}, 1, []⟩, true, [{size}]⟩ else none\n" +
        $"  cells := fun _ _ => ⟨173, true⟩\n  views := [⟨0, 0, {size}, true, true⟩]\n  nextIdentity := 1 }}\n";
    var claims = new List<string>();
    var proofs = new List<string>();
    foreach (var mask in new[] { "full", "partial", "unknown" })
    {
        var cells = "[" + string.Join(", ", Enumerable.Range(0, width).Select(index =>
            $"({index * 7 % 256}, {(mask == "full" || mask == "partial" && index % 3 != 0 ? "true" : "false")})")) + "]";
        var value = $"CIL.Safety.snapshotValue .vector{width * 8} {cells}";
        var arguments = $"[Examples.reference, .scalar ({value})]";
        var initial = "memory";
        if (copy)
        {
            var inputMemory = "source" + mask;
            definitions += $"def {inputMemory} : CIL.Safety.Memory := {{ memory with\n" +
                $"  allocations := fun id => if id < 2 then some ⟨.callerStack, ⟨{width}, 1, []⟩, true, [{width}]⟩ else none\n" +
                $"  cells := fun id index => if id = 1 then let cell := {cells}[index]?.getD (0, false); ⟨cell.1, cell.2⟩ else ⟨173, true⟩\n" +
                $"  views := [⟨0, 0, {width}, true, true⟩, ⟨1, 0, {width}, true, true⟩]\n  nextIdentity := 2 }}\n";
            arguments = "[Examples.reference, .reference (.address ⟨1, 0⟩)]";
            initial = inputMemory;
        }
        var invocation = $"CIL.Safety.invoke Extracted.program 128 0 {arguments} {initial}";
        if (copy && mask != "full")
        {
            claims.Add($"({invocation}).map Prod.snd = " +
                $".error ⟨0, 2, .memory .uninitialized (.address ⟨1, 0⟩) {width}⟩");
            proofs.Add("by rfl");
            continue;
        }
        claims.Add($"({invocation}).map Prod.snd = .ok [.scalar ({value})]");
        claims.Add($"({invocation}).map (fun result => (CIL.Safety.readSnapshot result.1 ⟨0, 0⟩ {size} 1).toOption) = " +
            $".ok (some (List.replicate {offset} (173, true) ++ {cells}))");
        proofs.Add("by apply result_of_toOption; decide +kernel");
        proofs.Add("by apply result_of_toOption; decide +kernel");
    }
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + """
        private theorem result_of_toOption {error value : Type} {result : Except error value}
            {expected : value} (observed : result.toOption = some expected) : result = .ok expected := by
          cases result <;> simp_all [Except.toOption]
        #print axioms result_of_toOption

        """ + definitions +
        "theorem correctness :\n" + string.Join(" ∧\n", claims) + " := by exact ⟨" +
        string.Join(", ", proofs) + "⟩\n#print axioms correctness\nend ExampleProof\n");
    pending.Add(new(selectors[name], proof, output), () => Console.WriteLine("PASS vector storage masks: " + name));
}

foreach (var item in cases)
{
    var name = $"Roundtrip{item.Bits}{item.Element}";
    Prove(name, item.Bits / 8);
    var value = RuntimeVector(item.Bits, item.Type);
    object[] arguments = [Activator.CreateInstance(value.GetType())!, value];
    if (!runtime.GetMethod(name)!.Invoke(null, arguments)!.Equals(value) || !arguments[0].Equals(value))
        throw new InvalidOperationException("Runtime vector storage mismatch: " + name);
}
foreach (var bits in new[] { 128, 256, 512 })
{
    Prove($"Copy{bits}", bits / 8, copy: true);
    var value = RuntimeVector(bits, typeof(uint));
    object[] arguments = [Activator.CreateInstance(value.GetType())!, value];
    if (!runtime.GetMethod($"Copy{bits}")!.Invoke(null, arguments)!.Equals(value) || !arguments[0].Equals(value))
        throw new InvalidOperationException("Runtime vector cpobj mismatch");
    if (bits == 512) continue;
    Prove($"Field{bits}", bits / 8, offset: 3);
    arguments = [Activator.CreateInstance(runtime.GetNestedType($"Holder{bits}")!)!, value];
    if (!runtime.GetMethod($"Field{bits}")!.Invoke(null, arguments)!.Equals(value))
        throw new InvalidOperationException("Runtime vector field mismatch");
}
var sizes = cases.Sum(item => item.Bits / 8);
if ((int)runtime.GetMethod("Sizes")!.Invoke(null, null)! != sizes)
    throw new InvalidOperationException("Runtime vector sizeof mismatch");
var sizeOutput = Path.Combine(root, "Sizes");
Directory.CreateDirectory(sizeOutput);
var sizeProof = Path.Combine(sizeOutput, "Proof.lean");
File.WriteAllText(sizeProof, $$"""
import Extracted
import Examples.Support
namespace ExampleProof
theorem correctness : (CIL.Safety.invoke Extracted.program 64 0 [] Examples.empty).map Prod.snd =
    .ok [.scalar (.i32 {{sizes}})] := by rfl
#print axioms correctness
end ExampleProof
""");
pending.Add(new(selectors["Sizes"], sizeProof, sizeOutput), () => Console.WriteLine("PASS all vector sizeof tokens"));
pending.Flush();

var baseline = File.ReadAllText(Path.Combine(root, "Roundtrip128uint/Extracted.lean"));
const string obligation = "method0_vector_initializations_validated";
var controlPath = Path.Combine(root, "Roundtrip128uint/Control.lean");
File.WriteAllText(controlPath, baseline +
    CheckedEvidenceControl(baseline, NarrowEvidence(baseline, obligation), [obligation], 0));
Run(["lake", "env", "lean", controlPath], cwd: verification.CheckoutPackage());
var rejected = new RejectedEvidence(root);
foreach (var (name, changed) in new[]
{
    ("store-width", baseline.Replace(".memory .store128", ".memory .store256")),
    ("load-width", baseline.Replace(".memory .load128", ".memory .load256")),
    ("init-width", baseline.Replace(".initAggregate 16", ".initAggregate 32")),
    ("init-missing", baseline.Replace(".initAggregate 16", ".nop")),
    ("element-token", baseline.Replace("\"System.UInt32\"", "\"System.Int16\"")),
    ("vector-token", baseline.Replace("Vector128`1", "Vector256`1"))
})
{
    if (changed == baseline) throw new InvalidOperationException("Ineffective vector mutation: " + name);
    var path = Path.Combine(root, name + ".lean");
    File.WriteAllText(path, NarrowEvidence(changed, obligation));
    rejected.Add(path, "PASS independently rejected vector evidence: " + name,
        "Extraction.VectorInitializationsValid method0Closed", "is false");
}
rejected.Check();

foreach (var mutation in new[] { "element", "scope", "encoding", "field512" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var malformed = Path.Combine(output, "Storage.dll");
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var owner = module.GetType("Storage");
        var vector = mutation == "field512"
            ? (GenericInstanceType)owner.NestedTypes.Single(type => type.Name == "Holder128").Fields[0].FieldType
            : (GenericInstanceType)owner.Methods.Single(method => method.Name == "Roundtrip128uint").ReturnType;
        switch (mutation)
        {
            case "element": vector.GenericArguments[0] = module.TypeSystem.Int16; break;
            case "scope": vector.ElementType.Scope = module; break;
            case "encoding": vector.IsValueType = false; break;
            case "field512": vector.ElementType.Name = "Vector512`1"; break;
        }
        selector = owner.Methods.Single(method =>
            method.Name == (mutation == "field512" ? "Field128" : "Roundtrip128uint")).FullName;
        module.Write(malformed);
    }
    var result = Execute(Extract("extract", malformed, "Storage", selector, output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        result.Output.Contains("No method matches selector", StringComparison.Ordinal))
        throw new InvalidOperationException("Malformed vector metadata accepted: " + mutation);
    Console.WriteLine("PASS vector metadata rejection: " + mutation);
}
