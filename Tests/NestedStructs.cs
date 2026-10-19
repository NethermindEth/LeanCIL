#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using System.Reflection.Emit;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/NestedStructs");
Directory.CreateDirectory(root);
var cases = 0;
var queue = new GeneratedQueue(verification, assembly);

void Prove(string dll, string selector, string name, IEnumerable<string> statements)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var claims = statements.ToArray();
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 8192\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) + " := by\n  exact " +
        (claims.Length == 1 ? "rfl" : "⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩") + "\nend ExampleProof\n");
    queue.Add(new(selector, proof, output, Assembly: dll), () =>
    {
        cases += claims.Length;
        Console.WriteLine($"PASS {name}: {claims.Length} layout/execution comparisons");
    });
}

// Probe managed storage, including nested padding, without interop marshalling.
int RuntimeSize(Type type)
{
    var method = new DynamicMethod("Size", typeof(int), [], typeof(Program).Module, true);
    var il = method.GetILGenerator();
    il.Emit(System.Reflection.Emit.OpCodes.Sizeof, type);
    il.Emit(System.Reflection.Emit.OpCodes.Ret);
    return ((Func<int>)method.CreateDelegate(typeof(Func<int>)))();
}

int RuntimeOffset(Type type, FieldInfo field)
{
    var method = new DynamicMethod("Offset", typeof(int), [], typeof(Program).Module, true);
    var il = method.GetILGenerator();
    var local = il.DeclareLocal(type);
    il.Emit(System.Reflection.Emit.OpCodes.Ldloca, local);
    il.Emit(System.Reflection.Emit.OpCodes.Ldflda, field);
    il.Emit(System.Reflection.Emit.OpCodes.Conv_U);
    il.Emit(System.Reflection.Emit.OpCodes.Ldloca, local);
    il.Emit(System.Reflection.Emit.OpCodes.Conv_U);
    il.Emit(System.Reflection.Emit.OpCodes.Sub);
    il.Emit(System.Reflection.Emit.OpCodes.Conv_I4);
    il.Emit(System.Reflection.Emit.OpCodes.Ret);
    return ((Func<int>)method.CreateDelegate(typeof(Func<int>)))();
}

var runtime = Assembly.Load(File.ReadAllBytes(assembly));
foreach (var name in new[] { "Snapshot", "Copy", "Alias", "Pass", "Packed", "Explicit", "Sized" })
{
    var method = runtime.GetType("Examples.Nested")!.GetMethod(name)!;
    var narrow = name == "Packed";
    var width = narrow ? 32 : 64;
    var claims = new List<string>();
    var layoutType = runtime.GetType("Examples." + (name switch
    {
        "Packed" => "PackedNestedRecord", "Explicit" => "ExplicitNestedRecord",
        "Sized" => "SizedNestedRecord", _ => "NestedRecord"
    }))!;
    var actualFields = layoutType.GetFields().OrderBy(f => f.MetadataToken).Select(f =>
        $"⟨{RuntimeOffset(layoutType, f)}, {RuntimeSize(f.FieldType)}, {(!f.FieldType.IsPrimitive && !f.FieldType.IsEnum).ToString().ToLowerInvariant()}⟩");
    claims.Add($"Extracted.layout0.size = {RuntimeSize(layoutType)}");
    claims.Add($"Extracted.layout0.fields = [{string.Join(", ", actualFields)}]");
    foreach (var bits in new ulong[] { 0, 1, 127, 128, 255, 65535, uint.MaxValue, 1UL << 32, long.MaxValue, 1UL << 63, ulong.MaxValue })
    {
        object value = narrow ? (object)unchecked((uint)bits) : bits;
        var expected = method.Invoke(null, [value])!;
        claims.Add($"(CIL.Safety.invoke Extracted.program 128 0 [.scalar (.i{width} {value})] Examples.empty).map Prod.snd = .ok [.scalar (.i{width} {expected})]");
    }
    Prove(assembly, $"Nested::{name}({(narrow ? "uint" : "ulong")})", name, claims);
}

// Compare every field offset and complete managed size across nested packing choices.
foreach (var innerPack in new[] { 1, 2, 4, 8 })
foreach (var outerPack in new[] { 1, 2, 4, 8 })
{
    var name = $"Packing-{innerPack}-{outerPack}";
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var inner = module.GetType("Examples.PackedLeaf");
        var outer = module.GetType("Examples.PackedNestedRecord");
        inner.PackingSize = (short)innerPack;
        inner.ClassSize = Math.Max(0, inner.ClassSize);
        outer.PackingSize = (short)outerPack;
        outer.ClassSize = Math.Max(0, outer.ClassSize);
        module.Write(dll);
    }
    var actual = Assembly.Load(File.ReadAllBytes(dll));
    var type = actual.GetType("Examples.PackedNestedRecord")!;
    var fields = type.GetFields().OrderBy(f => f.MetadataToken).Select(f =>
        $"⟨{RuntimeOffset(type, f)}, {RuntimeSize(f.FieldType)}, {(!f.FieldType.IsPrimitive && !f.FieldType.IsEnum).ToString().ToLowerInvariant()}⟩");
    Prove(dll, "Nested::Packed(uint)", name,
    [
        $"Extracted.layout0.size = {RuntimeSize(type)}",
        $"Extracted.layout0.fields = [{string.Join(", ", fields)}]"
    ]);
}

// Recursive and transitively unsupported layouts must fail before emission.
var contract = At("Examples/Proofs/NestedSnapshot.lean");
verification.Verify(assembly, "Examples", "Nested::Extract(Examples.NestedRecord)", contract, Path.Combine(root, "UniversalSnapshot"));
var wrongOutput = Path.Combine(root, "WrongSnapshot");
var failed = false;
try
{
    verification.Verify(assembly, "Examples", "Nested::WrongExtract(Examples.NestedRecord)", contract, wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    failed = true;
}
if (!failed || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Incorrect nested snapshot accepted");

// Recursive and transitively unsupported layouts must fail before emission.
var mutations = new[] { "self", "mutual", "reference", "float", "pack", "size", "auto" };
foreach (var mutation in mutations)
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var outer = module.GetType("Examples.NestedRecord");
        var leaf = module.GetType("Examples.Leaf");
        switch (mutation)
        {
            case "self": leaf.Fields[0].FieldType = leaf; break;
            case "mutual": leaf.Fields[0].FieldType = outer; break;
            case "reference": leaf.Fields[0].FieldType = module.TypeSystem.Object; break;
            case "float": leaf.Fields[0].FieldType = module.TypeSystem.Double; break;
            case "pack": leaf.PackingSize = 3; break;
            case "size": leaf.ClassSize = 65537; break;
            case "auto": leaf.IsAutoLayout = true; break;
        }
        module.Write(dll);
    }
    var result = Execute(Extract("extract", dll, "Examples", "Nested::Copy(ulong)", output));
    var marker = mutation is "self" or "mutual" ? "Recursive" : mutation == "pack" ? "Invalid aggregate packing" : "Unsupported";
    if (result.Code == 0 || !result.Output.Contains(marker) || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException($"Incorrect nested layout rejection: {mutation}\n{result.Output}");
}

queue.Flush();

Console.WriteLine($"PASS {cases} nested struct comparisons and {mutations.Length} malformed layouts");
