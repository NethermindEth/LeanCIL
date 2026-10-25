#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Buffers.Binary;
using System.Reflection;
using System.Runtime.Intrinsics;
using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var runtime = Assembly.LoadFile(assembly).GetType("Examples.ValueBitCasts")!;
using var metadata = ModuleDefinition.ReadModule(assembly);
var selectors = metadata.GetType("Examples.ValueBitCasts").Methods.ToDictionary(method => method.Name, method => method.FullName);
var root = At("artifacts/ValueBitCasts");
var pending = new GeneratedQueue(verification, assembly);
void Prove(string name, int width, string source, string target)
{
    var bytes = Enumerable.Range(0, width).Select(i => (byte)(i * 17 + 3)).ToArray();
    var claims = new List<string>();
    foreach (var mask in new[] { "full", "partial", "unknown" })
    {
        var cells = "[" + string.Join(", ", bytes.Select((b, i) => $"({b}, {(mask == "full" || mask == "partial" && i % 3 != 0 ? "true" : "false")})")) + "]";
        claims.Add($"(CIL.Safety.invoke Extracted.program 64 0 [.scalar (CIL.Safety.snapshotValue {source} {cells})] Examples.empty).map Prod.snd = " +
            $".ok [.scalar (CIL.Safety.snapshotValue {target} {cells})]");
    }
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by exact ⟨by rfl, by rfl, by rfl⟩\nend ExampleProof\n");
    pending.Add(new GeneratedVerification(selectors[name], proof, output),
        () => Console.WriteLine("PASS compiled BitCast full/partial/unknown masks: " + name));
}
foreach (var width in new[] { 16, 32 })
foreach (var element in new[] { "UInt32", "UInt64" })
foreach (var toVector in new[] { true, false })
{
    var name = $"{(toVector ? "To" : "From")}{width * 8}{element}";
    var aggregate = $"(.aggregate {width})";
    var vector = $".vector{width * 8}";
    var source = toVector ? aggregate : vector;
    var target = toVector ? vector : aggregate;
    var bytes = Enumerable.Range(0, width).Select(i => (byte)(i * 17 + 3)).ToArray();
    var method = runtime.GetMethod(name)!;
    object input;
    if (toVector)
    {
        input = Activator.CreateInstance(method.GetParameters()[0].ParameterType)!;
        var fields = input.GetType().GetFields();
        for (var i = 0; i < fields.Length; i++)
            fields[i].SetValue(input, BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan(i * 8)));
    }
    else if (width == 16)
    {
        var value = Vector128.Create(BinaryPrimitives.ReadUInt64LittleEndian(bytes), BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan(8)));
        input = element == "UInt64" ? (object)value : value.AsUInt32();
    }
    else
    {
        var value = Vector256.Create(BinaryPrimitives.ReadUInt64LittleEndian(bytes), BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan(8)),
            BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan(16)), BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan(24)));
        input = element == "UInt64" ? (object)value : value.AsUInt32();
    }
    var result = method.Invoke(null, [input])!;
    var actual = new byte[width];
    if (!toVector)
    {
        var fields = result.GetType().GetFields();
        for (var i = 0; i < fields.Length; i++)
            BinaryPrimitives.WriteUInt64LittleEndian(actual.AsSpan(i * 8), (ulong)fields[i].GetValue(result)!);
    }
    else if (width == 16)
        (element == "UInt64" ? ((Vector128<ulong>)result).AsByte() : ((Vector128<uint>)result).AsByte()).CopyTo(actual);
    else
        (element == "UInt64" ? ((Vector256<ulong>)result).AsByte() : ((Vector256<uint>)result).AsByte()).CopyTo(actual);
    if (!bytes.SequenceEqual(actual)) throw new InvalidOperationException("Runtime byte reinterpretation mismatch: " + name);

    Prove(name, width, source, target);
    Console.WriteLine("PASS BitCast runtime byte comparison: " + name);
}
Prove("RoundTrip", 32, "(.aggregate 32)", "(.aggregate 32)");
Prove("CopyLocal", 32, "(.aggregate 32)", ".vector256");
Prove("ParameterCopy", 32, "(.aggregate 32)", "(.aggregate 32)");
pending.Flush();

foreach (var name in new[] { "WrongSize", "ReferenceLayout" })
{
    var output = Path.Combine(root, "Reject-" + name);
    Directory.CreateDirectory(output);
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var result = Execute(Extract("extract", assembly, "Examples", selectors[name], output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException("Unsupported BitCast accepted: " + name);
    Console.WriteLine("PASS BitCast layout rejection: " + name);
}

foreach (var mutation in new[] { "arity", "parameter", "return", "instance", "scope", "version", "token" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.ValueBitCasts").Methods.Single(m => m.Name == "To256UInt64");
        var call = (GenericInstanceMethod)method.Body.Instructions.Single(i => i.Operand is MethodReference).Operand;
        switch (mutation)
        {
            case "arity": call.GenericArguments.Add(module.TypeSystem.UInt64); break;
            case "parameter": call.Parameters[0].ParameterType = module.TypeSystem.UInt64; break;
            case "return": call.ReturnType = call.ElementMethod.GenericParameters[0]; break;
            case "instance": call.ElementMethod.HasThis = true; break;
            case "scope": call.DeclaringType.Scope = module; break;
            case "version": ((AssemblyNameReference)call.DeclaringType.Scope).Version = new Version(9, 0, 0, 0); break;
            case "token": ((AssemblyNameReference)call.DeclaringType.Scope).PublicKeyToken = new byte[8]; break;
        }
        module.Write(dll);
    }
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var result = Execute(Extract("extract", dll, "Examples", selectors["To256UInt64"], output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException("Malformed BitCast accepted: " + mutation);
    Console.WriteLine("PASS BitCast signature rejection: " + mutation);
}
