#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using System.Reflection.Emit;
using Mono.Cecil;
using OpCodes = Mono.Cecil.Cil.OpCodes;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/TypedCopy");
Directory.CreateDirectory(root);
var cases = 0;
var queue = new GeneratedQueue(verification, assembly);

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
        Console.WriteLine($"PASS {name}: {claims.Length} copy cases");
    });
}

// Read a zero-initialized typed value's managed bytes directly. Interop marshalling
// is intentionally not used, because bool/char marshalling has different widths.
byte[] ManagedBytes(object value, int size)
{
    var type = value.GetType();
    var method = new DynamicMethod("Bytes", typeof(byte[]), [typeof(object)], typeof(Program).Module, true);
    var il = method.GetILGenerator();
    var local = il.DeclareLocal(type);
    var bytes = il.DeclareLocal(typeof(byte[]));
    il.Emit(System.Reflection.Emit.OpCodes.Ldarg_0);
    il.Emit(System.Reflection.Emit.OpCodes.Unbox_Any, type);
    il.Emit(System.Reflection.Emit.OpCodes.Stloc, local);
    il.Emit(System.Reflection.Emit.OpCodes.Ldc_I4, size);
    il.Emit(System.Reflection.Emit.OpCodes.Newarr, typeof(byte));
    il.Emit(System.Reflection.Emit.OpCodes.Stloc, bytes);
    for (var index = 0; index < size; index++)
    {
        il.Emit(System.Reflection.Emit.OpCodes.Ldloc, bytes);
        il.Emit(System.Reflection.Emit.OpCodes.Ldc_I4, index);
        il.Emit(System.Reflection.Emit.OpCodes.Ldloca, local);
        il.Emit(System.Reflection.Emit.OpCodes.Conv_U);
        il.Emit(System.Reflection.Emit.OpCodes.Ldc_I4, index);
        il.Emit(System.Reflection.Emit.OpCodes.Add);
        il.Emit(System.Reflection.Emit.OpCodes.Ldind_U1);
        il.Emit(System.Reflection.Emit.OpCodes.Stelem_I1);
    }
    il.Emit(System.Reflection.Emit.OpCodes.Ldloc, bytes);
    il.Emit(System.Reflection.Emit.OpCodes.Ret);
    return ((Func<object, byte[]>)method.CreateDelegate(typeof(Func<object, byte[]>)))(value);
}

object Value(Type type, ulong bits)
{
    if (type == typeof(System.Runtime.Intrinsics.Vector128<ulong>))
        return System.Runtime.Intrinsics.Vector128.Create(bits, unchecked(bits + 1));
    if (type == typeof(System.Runtime.Intrinsics.Vector256<ulong>))
        return System.Runtime.Intrinsics.Vector256.Create(bits, unchecked(bits + 1), unchecked(bits + 2), unchecked(bits + 3));
    if (type == typeof(byte)) return unchecked((byte)bits);
    if (type == typeof(sbyte)) return unchecked((sbyte)bits);
    if (type == typeof(bool)) return bits != 0;
    if (type == typeof(char)) return unchecked((char)bits);
    if (type == typeof(short)) return unchecked((short)bits);
    if (type == typeof(ushort)) return unchecked((ushort)bits);
    if (type == typeof(int)) return unchecked((int)bits);
    if (type == typeof(uint)) return unchecked((uint)bits);
    if (type == typeof(long)) return unchecked((long)bits);
    if (type == typeof(ulong)) return bits;
    if (type == typeof(nint)) return unchecked((nint)bits);
    if (type == typeof(nuint)) return unchecked((nuint)bits);
    var result = Activator.CreateInstance(type)!;
    foreach (var field in type.GetFields()) field.SetValue(result, Value(field.FieldType, bits));
    return result;
}

string Memory(byte[] bytes) => "{ Examples.empty with allocations := fun id => if id < 2 then " +
    $"some ⟨.callerStack, ⟨{bytes.Length}, 1, []⟩, true, [{bytes.Length}]⟩ else none, " +
    $"cells := fun id offset => if id = 0 then ⟨([{string.Join(", ", bytes)}] : List (BitVec 8))[offset]?.getD 0, true⟩ else ⟨0, false⟩, " +
    $"views := [⟨0, 0, {bytes.Length}, true, true⟩, ⟨1, 0, {bytes.Length}, true, true⟩], nextIdentity := 2 }}";

var types = new (string Name, int Size)[]
{
    ("SByte", 1), ("Byte", 1), ("Boolean", 1), ("Char", 2), ("Int16", 2), ("UInt16", 2),
    ("Int32", 4), ("UInt32", 4), ("Int64", 8), ("UInt64", 8), ("IntPtr", 8), ("UIntPtr", 8),
    ("Packet", 12), ("LargePacket", 40), ("Record", 8), ("PackedRecord", 11), ("Vector128", 16), ("Vector256", 32)
};
foreach (var (name, size) in types)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var vector = name.StartsWith("Vector", StringComparison.Ordinal);
        var type = vector ? ((ByReferenceType)module.GetType("Examples.TypedCopy").Methods.Single(m => m.Name == name).Parameters[0].ParameterType).ElementType :
            module.GetType("Examples." + name) ?? (TypeReference)typeof(TypeSystem).GetProperty(name)!.GetValue(module.TypeSystem)!;
        var method = new MethodDefinition("CopyFixture", Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static,
            module.TypeSystem.UInt64);
        method.Parameters.Add(new ParameterDefinition(new ByReferenceType(type)));
        method.Parameters.Add(new ParameterDefinition(new ByReferenceType(type)));
        var owner = module.GetType("Examples.Sequential");
        owner.Methods.Add(method);
        var il = method.Body.GetILProcessor();
        il.Emit(OpCodes.Ldarg_0);
        il.Emit(OpCodes.Ldarg_1);
        il.Emit(OpCodes.Cpobj, type);
        if (type is TypeDefinition aggregate)
        {
            il.Emit(OpCodes.Ldc_I8, 0L);
            foreach (var field in aggregate.Fields.Where(f => !f.IsStatic))
            {
                il.Emit(OpCodes.Ldarg_0);
                il.Emit(OpCodes.Ldfld, field);
                il.Emit(OpCodes.Conv_U8);
                il.Emit(OpCodes.Add);
            }
        }
        else if (vector)
            il.Emit(OpCodes.Ldc_I8, 0L);
        else
        {
            il.Emit(OpCodes.Ldarg_0);
            il.Emit(OpCodes.Ldobj, type);
            il.Emit(OpCodes.Conv_U8);
        }
        il.Emit(OpCodes.Ret);
        selector = method.FullName;
        var self = new MethodDefinition("SelfFixture", Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, module.TypeSystem.UInt64);
        self.Parameters.Add(new ParameterDefinition(new ByReferenceType(type)));
        owner.Methods.Add(self);
        var selfIl = self.Body.GetILProcessor();
        selfIl.Emit(OpCodes.Ldarg_0);
        selfIl.Emit(OpCodes.Ldarg_0);
        selfIl.Emit(OpCodes.Call, method);
        selfIl.Emit(OpCodes.Ret);
        module.Write(dll);
    }
    var runtime = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Sequential")!;
    var copied = runtime.GetMethod("CopyFixture")!;
    var selfCopy = runtime.GetMethod("SelfFixture")!;
    var runtimeType = copied.GetParameters()[0].ParameterType.GetElementType()!;
    var claims = new List<string>();
    var selfClaims = new List<string>();
    foreach (var bits in new ulong[] { 0, 1, 127, 128, 255, 32768, uint.MaxValue, long.MaxValue, ulong.MaxValue })
    {
        var source = Value(runtimeType, bits);
        var sourceBytes = ManagedBytes(source, size);
        object[] arguments = [Activator.CreateInstance(runtimeType)!, source];
        var result = (ulong)copied.Invoke(null, arguments)!;
        var destinationBytes = ManagedBytes(arguments[0], size);
        var memory = Memory(sourceBytes);
        var invocation = $"CIL.Safety.invoke Extracted.program 64 0 [.reference (.address ⟨1, 0⟩), .reference (.address ⟨0, 0⟩)] ({memory})";
        claims.Add($"({invocation}).map Prod.snd = .ok [.scalar (.i64 {result})]");
        claims.Add($"({invocation}).map (fun result => (List.range {size}).map (fun offset => (result.1.cells 1 offset).bits)) = .ok [{string.Join(", ", destinationBytes)}]");
        var selfResult = (ulong)selfCopy.Invoke(null, [source])!;
        selfClaims.Add($"(CIL.Safety.invoke Extracted.program 64 0 [.reference (.address ⟨0, 0⟩)] ({memory})).map Prod.snd = .ok [.scalar (.i64 {selfResult})]");
        selfClaims.Add($"(CIL.Safety.invoke Extracted.program 64 0 [.reference (.address ⟨0, 0⟩)] ({memory})).map " +
            $"(fun result => (List.range {size}).map (fun offset => (result.1.cells 0 offset).bits)) = .ok [{string.Join(", ", sourceBytes)}]");
    }
    Prove(dll, selector, name, claims);
    using var read = ModuleDefinition.ReadModule(dll);
    var selfSelector = read.GetType("Examples.Sequential").Methods.Single(m => m.Name == "SelfFixture").FullName;
    Prove(dll, selfSelector, name + "-Self", selfClaims);
    if (name == "UInt64")
    {
        verification.Verify(dll, "Examples", selector, At("Examples/Proofs/TypedCopy.lean"), Path.Combine(root, "UniversalCopy"));

        // Keep the same contract while reversing source and destination.
        var wrongOutput = Path.Combine(root, "WrongCopy");
        Directory.CreateDirectory(wrongOutput);
        var wrongDll = Path.Combine(wrongOutput, "Examples.dll");
        using (var wrong = ModuleDefinition.ReadModule(dll))
        {
            var method = wrong.GetType("Examples.Sequential").Methods.Single(m => m.Name == "CopyFixture");
            method.Body.Instructions[0].OpCode = OpCodes.Ldarg_1;
            method.Body.Instructions[1].OpCode = OpCodes.Ldarg_0;
            wrong.Write(wrongDll);
        }
        var failed = false;
        try
        {
            verification.Verify(wrongDll, "Examples", selector, At("Examples/Proofs/TypedCopy.lean"), wrongOutput);
        }
        catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
        {
            failed = true;
        }
        if (!failed || File.Exists(Path.Combine(wrongOutput, "verified.json")))
            throw new InvalidOperationException("Incorrect copy direction accepted");

        // Invalid tokens must be rejected before any Lean artifact is emitted.
        foreach (var mutation in new[] { "float", "object", "array", "scope" })
        {
            var rejectedOutput = Path.Combine(root, "Reject-" + mutation);
            Directory.CreateDirectory(rejectedOutput);
            var rejectedDll = Path.Combine(rejectedOutput, "Examples.dll");
            using (var invalid = ModuleDefinition.ReadModule(dll))
            {
                var method = invalid.GetType("Examples.Sequential").Methods.Single(m => m.Name == "CopyFixture");
                method.Body.Instructions[2].Operand = mutation switch
                {
                    "float" => invalid.TypeSystem.Double,
                    "object" => invalid.TypeSystem.Object,
                    "array" => new ArrayType(invalid.TypeSystem.UInt64),
                    _ => new TypeReference("System", "UInt64", invalid, invalid)
                };
                invalid.Write(rejectedDll);
            }
            var rejected = Execute(Extract("extract", rejectedDll, "Examples", selector, rejectedOutput));
            if (rejected.Code == 0 || !rejected.Output.Contains("Unsupported") ||
                File.Exists(Path.Combine(rejectedOutput, "Extracted.lean")))
                throw new InvalidOperationException("Incorrect copy token rejection: " + mutation + "\n" + rejected.Output);
            Console.WriteLine("PASS rejection: " + mutation);
        }
    }
}

queue.Flush();

Console.WriteLine($"Typed copy passed: {cases} runtime and byte-copy cases.");
