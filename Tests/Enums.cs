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
var root = At("artifacts/Enums");
Directory.CreateDirectory(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Enums")!;
var cases = 0;
var queue = new GeneratedQueue(verification, assembly);

string LeanValue(object value)
{
    if (value.GetType().IsEnum) value = Convert.ChangeType(value, Enum.GetUnderlyingType(value.GetType()));
    return value switch
    {
        sbyte x => $".scalar (.i32 {unchecked((uint)x)})",
        byte x => $".scalar (.i32 {x})",
        short x => $".scalar (.i32 {unchecked((uint)x)})",
        ushort x => $".scalar (.i32 {x})",
        int x => $".scalar (.i32 {unchecked((uint)x)})",
        uint x => $".scalar (.i32 {x})",
        long x => $".scalar (.i64 {unchecked((ulong)x)})",
        ulong x => $".scalar (.i64 {x})",
        _ => throw new InvalidOperationException("Unexpected value: " + value)
    };
}

// Emit typed memory instructions explicitly: C# normally chooses ldind/stind for enums.
var storageAssembly = Path.Combine(root, "EnumStorage.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var owner = module.GetType("Examples.Enums");
    foreach (var type in module.Types.Where(t => t.IsEnum))
    {
        var method = new MethodDefinition("Storage" + type.Name,
            Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, type);
        method.Parameters.Add(new ParameterDefinition(type));
        method.Body.InitLocals = true;
        method.Body.Variables.Add(new VariableDefinition(type));
        method.Body.Variables.Add(new VariableDefinition(type));
        var il = method.Body.GetILProcessor();
        il.Emit(OpCodes.Ldloca_S, method.Body.Variables[0]);
        il.Emit(OpCodes.Initobj, type);
        il.Emit(OpCodes.Ldloca_S, method.Body.Variables[0]);
        il.Emit(OpCodes.Ldarg_0);
        il.Emit(OpCodes.Stobj, type);
        il.Emit(OpCodes.Ldloca_S, method.Body.Variables[1]);
        il.Emit(OpCodes.Ldloca_S, method.Body.Variables[0]);
        il.Emit(OpCodes.Cpobj, type);
        il.Emit(OpCodes.Ldloca_S, method.Body.Variables[1]);
        il.Emit(OpCodes.Ldobj, type);
        il.Emit(OpCodes.Starg_S, method.Parameters[0]);
        il.Emit(OpCodes.Ldarga_S, method.Parameters[0]);
        il.Emit(OpCodes.Ldobj, type);
        il.Emit(OpCodes.Sizeof, type);
        if (type.Fields.Single(f => !f.IsStatic).FieldType.MetadataType is MetadataType.Int64 or MetadataType.UInt64)
            il.Emit(OpCodes.Conv_I8);
        il.Emit(OpCodes.Add);
        il.Emit(OpCodes.Ret);
        owner.Methods.Add(method);
    }
    module.Write(storageAssembly);
}
var storageRuntime = Assembly.Load(File.ReadAllBytes(storageAssembly)).GetType("Examples.Enums")!;

// Include unnamed values, each sign boundary and all eight integer representations.
foreach (var method in runtime.GetMethods(BindingFlags.Public | BindingFlags.Static)
    .Concat(storageRuntime.GetMethods(BindingFlags.Public | BindingFlags.Static).Where(m => m.Name.StartsWith("Storage", StringComparison.Ordinal)))
    .Where(m => m.GetParameters().Length == 1 && m.GetParameters()[0].ParameterType.IsEnum && !m.Name.StartsWith("Wrong", StringComparison.Ordinal)))
{
    var output = Path.Combine(root, method.Name);
    Directory.CreateDirectory(output);
    var type = method.GetParameters()[0].ParameterType;
    var values = new ulong[] { 0, 1, 2, 127, 128, 255, 256, 32767, 32768, 65535, 65536,
        int.MaxValue, 1UL << 31, uint.MaxValue, 1UL << 32, long.MaxValue, 1UL << 63, ulong.MaxValue };
    var claims = new List<string>();
    foreach (var bits in values)
    {
        var value = Enum.ToObject(type, bits);
        var expected = method.Invoke(null, [value])!;
        claims.Add($"(CIL.Safety.invoke Extracted.program 64 0 [{LeanValue(value)}] Examples.empty).map Prod.snd = .ok [{LeanValue(expected)}]");
    }
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 8192\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    var dll = method.Name.StartsWith("Storage", StringComparison.Ordinal) ? storageAssembly : assembly;
    queue.Add(new($"Enums::{method.Name}({type.FullName})", proof, output, Assembly: dll), () =>
    {
        cases += claims.Count;
        Console.WriteLine($"PASS {method.Name}: {claims.Count} runtime comparisons");
    });
}

// The same universally quantified contract rejects an incorrect implementation.
var contract = At("Examples/Proofs/EnumFlags.lean");
verification.Verify(assembly, "Examples", "Enums::SetFlag(Examples.Unsigned64)", contract, Path.Combine(root, "UniversalFlags"));
var wrongOutput = Path.Combine(root, "WrongFlags");
var failed = false;
try
{
    verification.Verify(assembly, "Examples", "Enums::WrongSetFlag(Examples.Unsigned64)", contract, wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    failed = true;
}
if (!failed || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Incorrect enum flag implementation accepted");

// Bad metadata must fail before it can produce a proof artifact.
var mutations = new[] { "base", "underlying", "scope", "extra-field", "field-name", "special-name", "generic", "constant", "sealed", "layout", "boolean" };
foreach (var mutation in mutations)
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var type = module.GetType("Examples.Signed8");
        var storage = type.Fields.Single(f => !f.IsStatic);
        switch (mutation)
        {
            case "base": type.BaseType.Scope = module; break;
            case "underlying": storage.FieldType = module.TypeSystem.Single; break;
            case "scope":
                foreach (var field in type.Fields.Where(f => f.IsStatic).ToArray()) type.Fields.Remove(field);
                storage.FieldType = new TypeReference("System", "SByte", module, module, true);
                break;
            case "extra-field": type.Fields.Add(new FieldDefinition("extra", Mono.Cecil.FieldAttributes.Public, module.TypeSystem.Int32)); break;
            case "field-name": storage.Name = "other"; break;
            case "special-name": storage.IsRuntimeSpecialName = false; break;
            case "generic": type.GenericParameters.Add(new GenericParameter("T", type)); break;
            case "constant": type.Fields.Single(f => f.Name == "One").IsLiteral = false; break;
            case "sealed": type.IsSealed = false; break;
            case "layout": type.IsSequentialLayout = true; break;
            case "boolean": storage.FieldType = module.TypeSystem.Boolean; break;
        }
        module.Write(dll);
    }
    var result = Execute(Extract("extract", dll, "Examples", "Enums::IdentityS8(Examples.Signed8)", output));
    if (result.Code == 0 || !result.Output.Contains("Unsupported", StringComparison.Ordinal) ||
        File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException($"Enum metadata mutation accepted: {mutation}\n{result.Output}");
}

queue.Flush();

Console.WriteLine($"PASS {cases} enum runtime comparisons and {mutations.Length} malformed metadata rejections");
Run(["dotnet", "run", "--file", "Tests/EnumBuffers.cs"], streamOutput: true, progress: "Enum buffer checks");
