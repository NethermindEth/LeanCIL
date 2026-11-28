#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include ../scripts/Checking/BatchVerification.cs
#:include ContractVariants.cs

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
        claims.Add($"(CIL.Safety.invoke Extracted.program 64 0 [{LeanValue(value)}] CIL.Safety.Memory.empty).map Prod.snd = .ok [{LeanValue(expected)}]");
    }
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport CIL.Safety.Execution\nset_option maxRecDepth 8192\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    var dll = method.Name.StartsWith("Storage", StringComparison.Ordinal) ? storageAssembly : assembly;
    queue.Add(new($"Enums::{method.Name}({type.FullName})", proof, output, Assembly: dll), () =>
    {
        cases += claims.Count;
        Console.WriteLine($"PASS {method.Name}: {claims.Count} runtime comparisons");
    });
}

// An unnamed high bit distinguishes preserving the flags from masking them all away.
var setFlag = runtime.GetMethod("SetFlag")!;
const ulong high = 1UL << 63;
var witness = Enum.ToObject(setFlag.GetParameters()[0].ParameterType, high);
if (Convert.ToUInt64(setFlag.Invoke(null, [witness])) != (high | 1) ||
    Convert.ToUInt64(runtime.GetMethod("WrongSetFlag")!.Invoke(null, [witness])) != 0)
    throw new InvalidOperationException("The compiled flag methods disagree with the high-bit witness.");

verification.VerifyContractVariant(assembly, "Examples", "Enums::SetFlag(Examples.Unsigned64)",
    Path.Combine(root, "UniversalFlags"), assembly, "Enums::WrongSetFlag(Examples.Unsigned64)",
    Path.Combine(root, "WrongFlags"), """
    /-- Setting the low flag preserves every other enum bit and the caller's memory. -/
    def flags : MethodContract W64 W64 where
      args value := [.scalar (.i64 value)]
      results value := [.scalar (.i64 value)]
      pre _ _ := True
      footprint _ := []
      post input before after value := after = before ∧ value = input ||| 1
    """, """
    theorem correctness : flags.Holds Extracted.program 0 := by
      intro input memory _
      apply MethodContract.Holds.intro (c := flags) (input := input) memory
        (input ||| 1) ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
      exact ⟨8, rfl⟩
    """, """
    /-- Masking the high bit returns zero on a successful invocation. -/
    theorem correctness : flags.Refuted Extracted.program 0 := by
      apply MethodContract.Refuted.of_return (c := flags) (input := 1 <<< 63)
        (initial := Memory.empty) (fuel := 8) (values := [.scalar (.i64 0)]) trivial rfl
      rintro ⟨_, value, encoded, _, rfl⟩
      exact (by decide : [Value.scalar (.i64 0)] ≠ [.scalar (.i64 ((1 <<< 63) ||| 1))]) encoded
    """, example: At("Examples/Proofs/EnumFlags.lean"));
Console.WriteLine("PASS setting the low flag preserves all other bits and refutes the masking variant");

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
VerifyEnumParameters(verification, assembly, root);

Console.WriteLine($"PASS {cases} enum runtime comparisons and {mutations.Length} malformed metadata rejections");
Run(["dotnet", "run", "--file", "Tests/EnumBuffers.cs"], streamOutput: true, progress: "Enum buffer checks");
Run(["dotnet", "run", "--file", "Tests/EnumMetadata.cs"], streamOutput: true, progress: "Enum metadata checks");

static void VerifyEnumParameters(Program verification, string assembly, string root)
{
    var image = Path.Combine(root, "EnumParameters.dll");
    using var module = ModuleDefinition.ReadModule(assembly);
    var owner = module.GetType("Examples.Enums");
    var enumBase = module.Types.First(type => type.IsEnum).BaseType;
    var flags = Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static;
    var caller = new MethodDefinition("ReadBothEnums", flags, module.TypeSystem.Int32);
    owner.Methods.Add(caller);
    var il = caller.Body.GetILProcessor();
    il.Emit(OpCodes.Ldc_I4_0);
    foreach (var digit in new[] { 1, 2 })
    {
        var type = new TypeDefinition(digit == 1 ? "Rows" : "", digit == 1 ? "Choice" : "Rows.Choice",
            Mono.Cecil.TypeAttributes.Public | Mono.Cecil.TypeAttributes.Sealed, enumBase);
        module.Types.Add(type);
        type.Fields.Add(new FieldDefinition("value__", Mono.Cecil.FieldAttributes.Public | Mono.Cecil.FieldAttributes.SpecialName |
            Mono.Cecil.FieldAttributes.RTSpecialName, module.TypeSystem.Int32));
        var member = new MethodDefinition("EnumDigit", flags, module.TypeSystem.Int32);
        member.Parameters.Add(new ParameterDefinition(type));
        owner.Methods.Add(member);
        var body = member.Body.GetILProcessor();
        body.Emit(OpCodes.Ldc_I4, digit);
        body.Emit(OpCodes.Ret);
        il.Emit(OpCodes.Ldc_I4_S, (sbyte)10);
        il.Emit(OpCodes.Mul);
        il.Emit(OpCodes.Ldc_I4_0);
        il.Emit(OpCodes.Call, member);
        il.Emit(OpCodes.Add);
    }
    il.Emit(OpCodes.Ret);
    module.Write(image);
    var runtime = Assembly.Load(File.ReadAllBytes(image)).GetType("Examples.Enums", true)!;
    var parameters = runtime.GetMethods().Where(method => method.Name == "EnumDigit")
        .Select(method => method.GetParameters()[0].ParameterType).ToArray();
    if (parameters.Length != 2 || parameters[0] == parameters[1] || parameters.Any(type => !type.IsEnum) ||
        !Equals(runtime.GetMethod("ReadBothEnums")!.Invoke(null, null), 12))
        throw new InvalidOperationException("CLR enum overloads must select different declarations and return 12.");
    verification.Verify(image, "Examples", "Enums::ReadBothEnums()", At("Tests/Enums/Parameters.lean"),
        Path.Combine(root, "EnumParameters"));
    Console.WriteLine("PASS CLR and checked overloads for two enum declarations named Rows.Choice");
}
