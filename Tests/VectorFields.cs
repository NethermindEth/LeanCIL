#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using System.Reflection.Emit;
using System.Runtime.Intrinsics;
using System.Text.RegularExpressions;
using Mono.Cecil;

using Program verification = new();
string assembly = At("Examples/Assembly/bin/Examples.dll");
string root = At("artifacts/VectorFields");
Assembly runtime = Assembly.LoadFile(assembly);
Type owner = runtime.GetType("Examples.VectorFields")!;
using ModuleDefinition metadata = ModuleDefinition.ReadModule(assembly);
Dictionary<string, string> selectors = metadata.GetType("Examples.VectorFields").Methods
    .ToDictionary(method => method.Name, method => method.FullName);
Run(["lake", "env", "lean", "Tests/VectorFields.lean"]);

int Size(Type type)
{
    DynamicMethod method = new("Size", typeof(int), [], typeof(Program).Module, true);
    ILGenerator il = method.GetILGenerator();
    il.Emit(System.Reflection.Emit.OpCodes.Sizeof, type);
    il.Emit(System.Reflection.Emit.OpCodes.Ret);
    return ((Func<int>)method.CreateDelegate(typeof(Func<int>)))();
}

int Offset(Type type)
{
    DynamicMethod method = new("Offset", typeof(int), [], typeof(Program).Module, true);
    ILGenerator il = method.GetILGenerator();
    LocalBuilder local = il.DeclareLocal(type);
    il.Emit(System.Reflection.Emit.OpCodes.Ldloca, local);
    il.Emit(System.Reflection.Emit.OpCodes.Ldflda, type.GetField("Value")!);
    il.Emit(System.Reflection.Emit.OpCodes.Conv_U);
    il.Emit(System.Reflection.Emit.OpCodes.Ldloca, local);
    il.Emit(System.Reflection.Emit.OpCodes.Conv_U);
    il.Emit(System.Reflection.Emit.OpCodes.Sub);
    il.Emit(System.Reflection.Emit.OpCodes.Conv_I4);
    il.Emit(System.Reflection.Emit.OpCodes.Ret);
    return ((Func<int>)method.CreateDelegate(typeof(Func<int>)))();
}

void Prove(string name, List<string> claims, string definitions = "")
{
    string output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    string proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + definitions +
        "\ntheorem correctness :\n" + string.Join(" ∧\n", claims) + " := by exact ⟨" +
        string.Join(", ", claims.Select(_ => "by rfl")) + "⟩\nend ExampleProof\n");
    verification.Verify(assembly, "Examples", selectors[name], proof, output);
    Console.WriteLine("PASS vector fields: " + name);
}

foreach ((string name, string holder, int width, bool write) in new[]
{
    ("Read128", "Holder128", 16, false), ("Read256", "Holder256", 32, false),
    ("Write128", "Holder128", 16, true), ("Write256", "Holder256", 32, true),
    ("WritePacked", "Packed256", 32, true), ("Reinterpret", "Words256", 32, true)
})
{
    Type type = owner.GetNestedType(holder)!;
    int size = Size(type);
    int offset = holder == "Words256" ? 0 : Offset(type);
    List<string> claims = [];
    string definitions = $"def memory : CIL.Safety.Memory := {{ Examples.empty with\n" +
        $"  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨{size}, 1, []⟩, true, [{size}]⟩ else none\n" +
        $"  cells := fun _ _ => ⟨173, true⟩\n  views := [⟨0, 0, {size}, true, true⟩]\n  nextIdentity := 1 }}\n";
    foreach (string mask in new[] { "full", "partial", "unknown" })
    {
        string cells = "[" + string.Join(", ", Enumerable.Range(0, width).Select(index =>
            $"({index * 7 % 256}, {(mask == "full" || mask == "partial" && index % 3 != 0 ? "true" : "false")})")) + "]";
        string value = $"CIL.Safety.snapshotValue .vector{width * 8} {cells}";
        string input = write ? $"[Examples.reference, .scalar ({value})]" :
            $"[.scalar (CIL.Safety.snapshotValue (.aggregate {size}) " +
            $"(List.replicate {offset} (173, true) ++ {cells} ++ List.replicate {size - offset - width} (173, true)))]";
        claims.Add($"(CIL.Safety.invoke Extracted.program 64 0 {input} memory).map Prod.snd = .ok [.scalar ({value})]");
        if (write)
            claims.Add($"(CIL.Safety.invoke Extracted.program 64 0 {input} memory).map " +
                $"(fun result => CIL.Safety.readSnapshot result.1 ⟨0, 0⟩ {size} 1) = " +
                $".ok (.ok (List.replicate {offset} (173, true) ++ {cells} ++ List.replicate {size - offset - width} (173, true)))");
    }
    if (holder != "Words256")
    {
        claims.Add($"Extracted.layout0.size = {size}");
        claims.Add($"Extracted.method0.code.contains (.fieldAt {offset} {width}) = true");
    }
    Prove(name, claims, definitions);

    object instance = Activator.CreateInstance(type)!;
    object vector = width == 16 ? (object)Vector128.Create(0x1122334455667788UL) : Vector256.Create(0x1122334455667788UL);
    if (write)
    {
        object[] arguments = [instance, vector];
        object actual = owner.GetMethod(name)!.Invoke(null, arguments)!;
        if (!actual.Equals(vector)) throw new InvalidOperationException("Runtime vector roundtrip failed: " + name);
    }
    else
    {
        type.GetField("Value")!.SetValue(instance, vector);
        object actual = owner.GetMethod(name)!.Invoke(null, [instance])!;
        if (!actual.Equals(vector)) throw new InvalidOperationException("Runtime vector field read failed: " + name);
    }
}

Type holder256 = owner.GetNestedType("Holder256")!;
int addressOffset = Offset(holder256);
int addressSize = Size(holder256);
Prove("Address256", [
    $"(CIL.Safety.invoke Extracted.program 16 0 [Examples.reference] memory).map Prod.snd = .ok [.reference (.address ⟨0, {addressOffset}⟩)]",
    $"Extracted.layout0.size = {addressSize}"],
    $"def memory : CIL.Safety.Memory := {{ Examples.empty with allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨{addressSize}, 1, []⟩, true, [{addressSize}]⟩ else none, nextIdentity := 1 }}\n");

foreach (string mutation in new[] { "element", "width", "scope", "version", "token", "arity", "encoding", "reference", "packing" })
{
    string output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    string dll = Path.Combine(output, "Examples.dll");
    using (ModuleDefinition module = ModuleDefinition.ReadModule(assembly))
    {
        TypeDefinition holder = module.GetType("Examples.VectorFields").NestedTypes.Single(type => type.Name == "Holder256");
        GenericInstanceType vector = (GenericInstanceType)holder.Fields.Single(field => field.Name == "Value").FieldType;
        switch (mutation)
        {
            case "element": vector.GenericArguments[0] = module.TypeSystem.SByte; break;
            case "width": vector.ElementType.Name = "Vector512`1"; break;
            case "scope": vector.ElementType.Scope = module; break;
            case "version": ((AssemblyNameReference)vector.ElementType.Scope).Version = new Version(9, 0, 0, 0); break;
            case "token": ((AssemblyNameReference)vector.ElementType.Scope).PublicKeyToken = new byte[8]; break;
            case "arity": vector.GenericArguments.Add(module.TypeSystem.UInt64); break;
            case "encoding": vector.IsValueType = false; break;
            case "reference": vector.GenericArguments[0] = module.TypeSystem.Object; break;
            case "packing": holder.PackingSize = 32; break;
        }
        module.Write(dll);
    }
    File.Delete(Path.Combine(output, "Extracted.lean"));
    (int Code, string Output, string Stdout, string Stderr) result = Execute(Extract("extract", dll, "Examples", selectors["Read256"], output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException("Unsupported vector field accepted: " + mutation);
    Console.WriteLine("PASS vector field rejection: " + mutation);
}

string baseline = File.ReadAllText(Path.Combine(root, "WritePacked", "Extracted.lean"));
foreach ((string name, string changed) in new[]
{
    ("field-offset", baseline.Replace(".fieldAt 3 32", ".fieldAt 2 32")),
    ("vector-storage", baseline.Replace("type := .vector256", "type := .unsigned64")),
    ("computed-width", baseline.Replace("⟨3, 32, false⟩", "⟨3, 16, false⟩")),
    ("omitted-uses", Regex.Replace(baseline,
        @"def method0LayoutUses : List Extraction.LayoutUse := [^\r\n]*",
        "def method0LayoutUses : List Extraction.LayoutUse := []"))
})
{
    if (changed == baseline) throw new InvalidOperationException("Vector evidence mutation did not change source: " + name);
    string path = Path.Combine(root, "Evidence-" + name + ".lean");
    File.WriteAllText(path, changed);
    (int Code, string Output, string Stdout, string Stderr) result = Execute(["lake", "env", "lean", path]);
    if (result.Code == 0 || !result.Output.Contains("decide"))
        throw new InvalidOperationException("Malformed vector field evidence accepted: " + name + "\n" + result.Output);
    Console.WriteLine("PASS vector field evidence rejection: " + name);
}
