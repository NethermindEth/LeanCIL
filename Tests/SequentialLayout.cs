#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using System.Reflection.Emit;
using Mono.Cecil;
using Mono.Cecil.Cil;
using OpCodes = Mono.Cecil.Cil.OpCodes;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/SequentialLayout");
Directory.CreateDirectory(root);
var queue = new GeneratedQueue(verification, assembly);
if (IntPtr.Size != 8) throw new InvalidOperationException("Layout comparisons require a 64-bit runtime");
var cases = 0;

void Prove(string dll, string selector, string name, IEnumerable<string> statements)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var claims = statements.ToArray();
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 4096\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) + " := by\n  exact " +
        (claims.Length == 1 ? "rfl" : "⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩") + "\nend ExampleProof\n");
    queue.Add(new(selector, proof, output, Assembly: dll), () =>
    {
        cases += claims.Length;
        Console.WriteLine($"PASS {name}: {claims.Length} layout and execution cases");
    });
}

// Measure managed layout directly; interop Marshal.SizeOf/OffsetOf would give
// different answers for some fields, particularly Boolean and Char.
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

verification.Verify(assembly, "Examples", "Sequential::ReadWrite(Examples.Record&,uint)",
    At("Examples/Proofs/SequentialReadWrite.lean"), Path.Combine(root, "UniversalField"));
Prove(assembly, "Sequential::Packed(ulong)", "Packed",
    new ulong[] { 0, 1, uint.MaxValue, long.MaxValue, ulong.MaxValue }.Select(value =>
        $"(CIL.Safety.invoke Extracted.program 64 0 [.scalar (.i64 {value})] Examples.empty).map Prod.snd = .ok [.scalar (.i64 {value})]"));

var variants = new List<(int Pack, int Size, bool Empty)>();
variants.AddRange(new[] { 0, 1, 2, 4, 8, 16, 32, 64, 128 }.Select(pack => (pack, 0, false)));
variants.AddRange([(0, 1, false), (0, 65, false), (1, 65, false), (0, 0, true), (4, 9, true)]);
foreach (var (pack, size, empty) in variants)
{
    var name = $"Pack{pack}-Size{size}-Empty{empty}";
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var type = new TypeDefinition("Examples", "LayoutFixture", Mono.Cecil.TypeAttributes.Public |
            Mono.Cecil.TypeAttributes.Sealed | Mono.Cecil.TypeAttributes.SequentialLayout,
            module.GetType("Examples.Record").BaseType) { PackingSize = (short)pack, ClassSize = size };
        module.Types.Add(type);
        if (!empty)
        {
            var fields = new[] { module.TypeSystem.Byte, module.TypeSystem.UInt64, module.TypeSystem.Boolean,
                module.TypeSystem.Char, module.TypeSystem.Int16, module.TypeSystem.UInt32, module.TypeSystem.IntPtr,
                module.TypeSystem.UIntPtr, module.TypeSystem.SByte };
            for (var index = 0; index < fields.Length; index++)
                type.Fields.Add(new FieldDefinition("Field" + index, Mono.Cecil.FieldAttributes.Public, fields[index]));
        }
        var method = new MethodDefinition("LayoutFixture", Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static,
            module.TypeSystem.UInt64);
        method.Parameters.Add(new ParameterDefinition(module.TypeSystem.UInt64));
        module.GetType("Examples.Sequential").Methods.Add(method);
        method.Body.InitLocals = true;
        method.Body.Variables.Add(new VariableDefinition(type));
        var il = method.Body.GetILProcessor();
        il.Emit(OpCodes.Ldloca_S, method.Body.Variables[0]);
        il.Emit(OpCodes.Initobj, type);
        foreach (var field in type.Fields)
        {
            il.Emit(OpCodes.Ldloca_S, method.Body.Variables[0]);
            il.Emit(OpCodes.Ldarg_0);
            if (field.FieldType.MetadataType is not (MetadataType.UInt64 or MetadataType.IntPtr or MetadataType.UIntPtr))
                il.Emit(OpCodes.Conv_U4);
            il.Emit(OpCodes.Stfld, field);
        }
        il.Emit(OpCodes.Sizeof, type);
        il.Emit(OpCodes.Conv_U8);
        foreach (var field in type.Fields)
        {
            il.Emit(OpCodes.Ldloca_S, method.Body.Variables[0]);
            il.Emit(OpCodes.Ldfld, field);
            il.Emit(OpCodes.Conv_U8);
            il.Emit(OpCodes.Add);
        }
        il.Emit(OpCodes.Ret);
        selector = method.FullName;
        module.Write(dll);
    }
    var runtime = Assembly.Load(File.ReadAllBytes(dll));
    var runtimeType = runtime.GetType("Examples.LayoutFixture")!;
    var actualSize = RuntimeSize(runtimeType);
    var runtimeFields = runtimeType.GetFields().OrderBy(f => f.MetadataToken).ToArray();
    var actualFields = runtimeFields.Select(f => $"⟨{RuntimeOffset(runtimeType, f)}, {RuntimeSize(f.FieldType)}, false⟩");
    var claims = new List<string>
    {
        $"Extracted.layout0.size = {actualSize}",
        $"Extracted.layout0.fields = [{string.Join(", ", actualFields)}]"
    };
    var methodInfo = runtime.GetType("Examples.Sequential")!.GetMethod("LayoutFixture")!;
    foreach (var value in new ulong[] { 0, 1, 127, 128, 255, 256, 32767, 32768, uint.MaxValue, long.MaxValue, ulong.MaxValue })
    {
        var result = (ulong)methodInfo.Invoke(null, [value])!;
        claims.Add($"(CIL.Safety.invoke Extracted.program 128 0 [.scalar (.i64 {value})] Examples.empty).map Prod.snd = .ok [.scalar (.i64 {result})]");
    }
    Prove(dll, selector, name, claims);
}

queue.Flush();

// Reject layout metadata that the admitted model cannot faithfully interpret.
foreach (var mutation in new[] { "pack", "size", "auto", "reference", "float", "inline", "generic", "offset", "nested", "recursive" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var type = module.GetType("Examples.Record");
        switch (mutation)
        {
            case "pack": type.PackingSize = 3; break;
            case "size": type.ClassSize = 65537; break;
            case "auto": type.IsAutoLayout = true; break;
            case "reference": type.Fields[0].FieldType = module.TypeSystem.Object; break;
            case "float": type.Fields[0].FieldType = module.TypeSystem.Double; break;
            case "generic": type.GenericParameters.Add(new GenericParameter("T", type)); break;
            case "offset": type.Fields[0].Offset = 0; break;
            case "nested":
                type.Fields[0].FieldType = module.GetType("Examples.Packet");
                module.GetType("Examples.Packet").Fields[0].FieldType = module.TypeSystem.Object;
                break;
            case "recursive": type.Fields[0].FieldType = type; break;
            case "inline":
                var attributeType = new TypeReference("System.Runtime.CompilerServices", "InlineArrayAttribute", module, module.TypeSystem.CoreLibrary);
                var constructor = new MethodReference(".ctor", module.TypeSystem.Void, attributeType) { HasThis = true };
                constructor.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
                var attribute = new CustomAttribute(constructor);
                attribute.ConstructorArguments.Add(new CustomAttributeArgument(module.TypeSystem.Int32, 2));
                type.CustomAttributes.Add(attribute);
                break;
        }
        module.Write(dll);
    }
    var rejected = Execute(Extract("extract", dll, "Examples", "Sequential::ReadWrite(Examples.Record&,uint)", output));
    var marker = mutation switch
    {
        "pack" => "Invalid aggregate packing", "offset" => "Invalid field layout",
        "reference" or "float" or "nested" => "Unsupported field type",
        "recursive" => "Recursive or excessively nested aggregate layout",
        _ => "Unsupported aggregate layout"
    };
    if (rejected.Code == 0 || !rejected.Output.Contains(marker) || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException("Incorrect layout rejection: " + mutation + "\n" + rejected.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}

Console.WriteLine($"Sequential layout passed: {cases} managed layout and execution cases; ten metadata rejections.");
