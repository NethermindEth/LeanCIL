#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Numerics;
using System.Reflection;
using System.Runtime.Intrinsics;
using System.Text.RegularExpressions;
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
var portableCases = (from bits in new[] { 128, 256, 512 } from element in new[] { "byte", "long" }
    select (Bits: bits, Element: element)).ToArray();
var portable = portableCases.Select(item =>
{
    var intersection = item.Element == "byte" && item.Bits != 256
        ? $"PortableAnd{item.Bits}(left, right)" : "(left & right)";
    var primitiveChecks = item.Element == "byte" ? $$"""
        if (!Vector{{item.Bits}}.EqualsAll(Vector{{item.Bits}}<int>.Zero, ~Vector{{item.Bits}}<int>.AllBitsSet) ||
            !Vector{{item.Bits}}.EqualsAll(Vector{{item.Bits}}<uint>.Zero, ~Vector{{item.Bits}}<uint>.AllBitsSet))
            return Vector{{item.Bits}}<{{item.Element}}>.Zero;
        """ : "";
    return $$"""
    public static Vector{{item.Bits}}<{{item.Element}}> Portable{{item.Bits}}{{item.Element}}(
        Vector{{item.Bits}}<{{item.Element}}> left, Vector{{item.Bits}}<{{item.Element}}> right, bool equal)
    {
        if ((left == right) != equal || Vector{{item.Bits}}.EqualsAll(left, right) != equal)
            return Vector{{item.Bits}}<{{item.Element}}>.Zero;
        {{primitiveChecks}}
        return ({{intersection}} ^ (left | right)) |
            (~left & Vector{{item.Bits}}<{{item.Element}}>.AllBitsSet) ^ Vector{{item.Bits}}<{{item.Element}}>.Zero;
    }
    """;
});
File.WriteAllText(Path.Combine(source, "Storage.cs"),
    "using System.Runtime.Intrinsics; using System.Runtime.InteropServices;\n" +
    "public static unsafe class Storage {\n" +
    "static T Pass<T>(T value) where T : unmanaged => value;\n" +
    string.Join('\n', new[] { 128, 512 }.Select(bits =>
        $"static Vector{bits}<byte> PortableAnd{bits}(Vector{bits}<byte> left, " +
        $"Vector{bits}<byte> right) => left & right;")) +
    string.Join('\n', methods.Concat(copies).Concat(fields).Concat(portable)) +
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

void Prove(string name, int width, int offset = 0, bool copy = false, bool allMasks = true)
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
    foreach (var mask in allMasks ? new[] { "full", "partial", "unknown" } : ["full"])
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
    // Element tokens have independent certificates; mask propagation shares each width's operations.
    Prove(name, item.Bits / 8, allMasks: item.Element == "uint");
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
foreach (var item in portableCases)
{
    var name = $"Portable{item.Bits}{item.Element}";
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var claims = new List<string>();
    var left = Enumerable.Range(0, item.Bits / 8).Select(index => (byte)(index * 17 + 3)).ToArray();
    foreach (var variant in new[] { 0, 1, 2, 3 })
    {
        var right = left.ToArray();
        if (variant == 1) right[^1] ^= 128;
        if (variant == 2) right = left.Select(value => (byte)~value).ToArray();
        var equal = variant is 0 or 3;
        var suppliedEquality = variant != 3 && equal;
        var expected = variant == 3 ? new byte[left.Length] : left.Zip(right, (a, b) =>
            (byte)(((a & b) ^ (a | b)) | (~a & 255))).ToArray();
        object Box(byte[] bytes) => (item.Bits, item.Element) switch
        {
            (128, "byte") => Vector128.Create<byte>(bytes),
            (128, _) => Vector128.Create<byte>(bytes).AsInt64(),
            (256, "byte") => Vector256.Create<byte>(bytes),
            (256, _) => Vector256.Create<byte>(bytes).AsInt64(),
            (512, "byte") => Vector512.Create<byte>(bytes),
            _ => Vector512.Create<byte>(bytes).AsInt64()
        };
        var actual = runtime.GetMethod(name)!.Invoke(null, [Box(left), Box(right), suppliedEquality]);
        if (!Box(expected).Equals(actual)) throw new InvalidOperationException("Portable vector mismatch: " + name);
        string Value(byte[] bytes) => $".scalar (.v{item.Bits} {new BigInteger(bytes, isUnsigned: true)})";
        claims.Add($"((CIL.Safety.invoke Extracted.program 192 0 " +
            $"[{Value(left)}, {Value(right)}, .scalar (.i32 {(suppliedEquality ? 1 : 0)})] " +
            $"Examples.empty).map Prod.snd).toOption = some [{Value(expected)}]");
    }
    var proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
        "theorem correctness :\n" + string.Join(" ∧\n", claims) + " := by decide +kernel\n" +
        "#print axioms correctness\nend ExampleProof\n");
    if (item.Element == "byte" && item.Bits != 256)
    {
        Run(Extract("extract", assembly, "Storage", selectors[name], output));
        var evidence = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
        var callOutput = Path.Combine(root, $"PortableCall{item.Bits}");
        Run(Extract("extract", assembly, "Storage", selectors[$"PortableAnd{item.Bits}"], callOutput));
        // The helper's isolated declarations must match its certificate in the complete caller.
        var callEvidence = File.ReadAllText(Path.Combine(callOutput, "Extracted.lean"))
            .Replace("method0", "method1", StringComparison.Ordinal);
        const string portableObligation = "method1_division_validated";
        File.AppendAllText(proof, CheckedEvidenceControl(evidence,
            NarrowEvidence(callEvidence, portableObligation), [portableObligation], 1));
    }
    pending.Add(new(selectors[name], proof, output), () => Console.WriteLine("PASS portable vector operations: " + name));
}
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
    ("vector-token", baseline.Replace("Vector128\\u00601", "Vector256\\u00601"))
})
{
    if (changed == baseline) throw new InvalidOperationException("Ineffective vector mutation: " + name);
    var path = Path.Combine(root, name + ".lean");
    File.WriteAllText(path, NarrowEvidence(changed, obligation));
    rejected.Add(path, "PASS independently rejected vector evidence: " + name,
        "Extraction.VectorInitializationsValid method0Closed", "is false");
}
var portableBaseline = File.ReadAllText(Path.Combine(root, "PortableCall128/Extracted.lean"))
    .Replace("method0", "method1", StringComparison.Ordinal);
string RawOnly(string text, Func<string, string> change) => Regex.Replace(text,
    @"(?m)^def method1(?:Original|Closed) :[^\r\n]*", match => change(match.Value));
string UnrelatedPortable(string source, int bits)
{
    var unrelated = RawOnly(source, text => Regex.Replace(
        text.Replace($"System.Runtime.Intrinsics.Vector{bits}", $"Unrelated.Vector{bits}"),
        @"name := ""[^""]*""", "name := \"Unrelated\""));
    return Regex.Replace(unrelated,
        $@"\.intrinsic \(\.vector \(\.(?:band|bor|bxor|bnot|equalsAll|zero|ones) {bits}\)\) \d+", ".nop");
}
void RejectPortable(string original, string name, string changed)
{
    if (changed == original) throw new InvalidOperationException("Ineffective portable mutation: " + name);
    var path = Path.Combine(root, name + ".lean");
    File.WriteAllText(path, NarrowEvidence(changed, "method1_division_validated"));
    rejected.Add(path, "PASS independently rejected portable vector evidence: " + name,
        "Extraction.DivisionIntrinsicsValid method1Closed", "is false");
}
foreach (var (name, changed) in new[]
{
    ("portable-operation", portableBaseline.Replace(".vector (.band 128)", ".vector (.bor 128)")),
    ("portable-element", RawOnly(portableBaseline, text => text.Replace("System.Byte", "System.Int64"))),
    ("portable-scope", RawOnly(portableBaseline, text => text.Replace("Version=10.0.0.0", "Version=9.0.0.0"))),
    ("portable-width", portableBaseline.Replace(".vector (.band 128)", ".vector (.band 256)")),
    ("portable-arity", portableBaseline.Replace(".intrinsic (.vector (.band 128)) 2",
        ".intrinsic (.vector (.band 128)) 1")),
    ("portable-target-family", UnrelatedPortable(portableBaseline, 128))
})
    RejectPortable(portableBaseline, name, changed);
var wideBaseline = File.ReadAllText(Path.Combine(root, "PortableCall512/Extracted.lean"))
    .Replace("method0", "method1", StringComparison.Ordinal);
RejectPortable(wideBaseline, "portable512-width",
    wideBaseline.Replace(".vector (.band 512)", ".vector (.band 256)"));
RejectPortable(wideBaseline, "portable512-target-family", UnrelatedPortable(wideBaseline, 512));
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
