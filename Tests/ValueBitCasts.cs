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
        if (mask != "full" && name is "To128Byte" or "To256Int32" or "To256Int64")
            claims.Add($"CIL.Safety.checkedIntrinsic (.vector (.equalsAll {width * 8})) " +
                $"[CIL.Safety.snapshotValue {target} {cells}, CIL.Safety.snapshotValue {target} {cells}] = " +
                ".error .invalidState");
    }
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by exact ⟨" +
        string.Join(", ", claims.Select(_ => "by rfl")) + "⟩\n" +
        "#print axioms correctness\nend ExampleProof\n");
    pending.Add(new GeneratedVerification(selectors[name], proof, output),
        () => Console.WriteLine("PASS compiled BitCast full/partial/unknown masks: " + name));
}
foreach (var (width, element) in new[]
{
    (16, "UInt32"), (16, "UInt64"), (32, "UInt32"), (32, "UInt64"),
    (16, "Byte"), (32, "Int32"), (32, "Int64")
})
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
        input = element switch
        {
            "UInt64" => (object)value, "Byte" => value.AsByte(), _ => value.AsUInt32()
        };
    }
    else
    {
        var value = Vector256.Create(BinaryPrimitives.ReadUInt64LittleEndian(bytes), BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan(8)),
            BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan(16)), BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan(24)));
        input = element switch
        {
            "UInt64" => (object)value, "Int32" => value.AsInt32(), "Int64" => value.AsInt64(),
            _ => value.AsUInt32()
        };
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
        (result switch
        {
            Vector128<ulong> value => value.AsByte(), Vector128<byte> value => value,
            _ => ((Vector128<uint>)result).AsByte()
        }).CopyTo(actual);
    else
        (result switch
        {
            Vector256<ulong> value => value.AsByte(), Vector256<int> value => value.AsByte(),
            Vector256<long> value => value.AsByte(), _ => ((Vector256<uint>)result).AsByte()
        }).CopyTo(actual);
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

foreach (var mutation in new[] { "arity", "parameter", "return", "instance", "scope", "version", "token",
    "vector-scope", "vector-element" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.ValueBitCasts").Methods.Single(m => m.Name == "To256Int32");
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
            case "vector-scope": ((GenericInstanceType)call.GenericArguments[1]).ElementType.Scope = module; break;
            case "vector-element":
                ((GenericInstanceType)call.GenericArguments[1]).GenericArguments[0] = module.TypeSystem.Single;
                break;
        }
        module.Write(dll);
    }
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var result = Execute(Extract("extract", dll, "Examples", selectors["To256Int32"], output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException("Malformed BitCast accepted: " + mutation);
    var diagnostic = mutation switch
    {
        "vector-scope" => "Unresolved aggregate",
        "vector-element" => "Unsupported Unsafe.BitCast value layouts",
        _ => null
    };
    if (diagnostic is not null && !result.Output.Contains(diagnostic, StringComparison.Ordinal))
        throw new InvalidOperationException("BitCast vector rejection failed for the wrong reason: " + mutation);
    Console.WriteLine("PASS BitCast signature rejection: " + mutation);
}
