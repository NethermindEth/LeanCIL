#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Buffers.Binary;
using System.Numerics;
using System.Reflection.PortableExecutable;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/PrimitiveOperations");
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
        "namespace ExampleProof\ntheorem correctness :\n  " + string.Join(" ∧\n  ", claims) +
        " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    queue.Add(new(selector, proof, output, Assembly: dll), () =>
    {
        cases += claims.Length;
        Console.WriteLine($"PASS {name}: {claims.Length} cases");
    });
}

string Executes(string arguments, string memory = "Examples.caller") =>
    $"CIL.Safety.invoke Extracted.program 32 0 [{arguments}] ({memory})";

string Returns(string arguments, BigInteger value, int width = 32, string memory = "Examples.caller") =>
    $"({Executes(arguments, memory)}).map Prod.snd = .ok [.scalar (.i{width} {value})]";

BigInteger[] Boundaries(int width) => [0, 1, 127, 128, 255, 256, 32767, 32768, 65535, 65536,
    (BigInteger.One << (width - 1)), (BigInteger.One << width) - 1];

BigInteger Extended(BigInteger value, int bytes, bool signed, int stackWidth)
{
    var modulus = BigInteger.One << (8 * bytes);
    var result = value % modulus;
    if (signed && result >= modulus / 2) result -= modulus;
    return (result + (BigInteger.One << stackWidth)) % (BigInteger.One << stackWidth);
}

// Check compiler output as well as exact encodings emitted below.
verification.Verify(assembly, "Examples", "PrimitiveOperations::ReadWrite(int&,int)",
    At("Examples/Proofs/PrimitiveReadWrite.lean"), Path.Combine(root, "ReadWrite"));
Prove(assembly, "PrimitiveOperations::Alias(short&,short&,int)", "Alias",
    Boundaries(32).Select(value => Returns($"Examples.reference, Examples.reference, .scalar (.i32 {value})",
        Extended(value, 2, true, 32))));
Prove(assembly, "PrimitiveOperations::Choose(int)", "CSharpSwitch",
    new BigInteger[] { 0, 1, 2, 3, 4, 5, 2147483648, 4294967295 }.Select(value =>
        Returns($".scalar (.i32 {value})", value < 5 ? new[] { 13, 29, 7, 41, 19 }[(int)value] : 4294967295)));
Prove(assembly, "PrimitiveOperations::PacketSize()", "CSharpSizeof",
    [Returns("", 12), Returns("", 12, memory: "Examples.empty")]);

// Each fixture uses actual CIL, without a source-level arithmetic summary.
string Fixture(string name, Action<ModuleDefinition, MethodDefinition> emit)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using var module = ModuleDefinition.ReadModule(assembly);
    var method = new MethodDefinition("Fixture", MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Int32);
    module.GetType("Examples.PrimitiveOperations").Methods.Add(method);
    emit(module, method);
    module.Write(dll);
    return dll;
}

string FixtureSelector(string dll)
{
    using var module = ModuleDefinition.ReadModule(dll);
    return module.GetType("Examples.PrimitiveOperations").Methods.Single(m => m.Name == "Fixture").FullName;
}

TypeReference Primitive(ModuleDefinition module, string name) => name switch
{
    "SByte" => module.TypeSystem.SByte, "Byte" => module.TypeSystem.Byte,
    "Int16" => module.TypeSystem.Int16, "UInt16" => module.TypeSystem.UInt16,
    "Char" => module.TypeSystem.Char, "Boolean" => module.TypeSystem.Boolean,
    "Int32" => module.TypeSystem.Int32, "UInt32" => module.TypeSystem.UInt32,
    "Int64" => module.TypeSystem.Int64, "UInt64" => module.TypeSystem.UInt64,
    "IntPtr" => module.TypeSystem.IntPtr, "UIntPtr" => module.TypeSystem.UIntPtr,
    _ => throw new ArgumentException("Unknown primitive: " + name)
};

var types = new (string Name, int Width, bool Signed)[]
{
    ("SByte", 1, true), ("Byte", 1, false), ("Int16", 2, true),
    ("UInt16", 2, false), ("Char", 2, false), ("Boolean", 1, false),
    ("Int32", 4, false), ("UInt32", 4, false), ("Int64", 8, false), ("UInt64", 8, false),
    ("IntPtr", 8, true), ("UIntPtr", 8, false)
};

// Typed stores/loads and zero initialization cover all admitted integer tokens.
foreach (var (typeName, width, signed) in types)
foreach (var initialize in new[] { false, true })
{
    var name = (initialize ? "Init-" : "Typed-") + typeName;
    var stackWidth = width == 8 ? 64 : 32;
    var dll = Fixture(name, (module, method) =>
    {
        var type = Primitive(module, typeName);
        method.ReturnType = stackWidth == 64 ? module.TypeSystem.Int64 : module.TypeSystem.Int32;
        method.Parameters.Add(new ParameterDefinition(new ByReferenceType(type)));
        method.Parameters.Add(new ParameterDefinition(method.ReturnType));
        var code = method.Body.Instructions;
        code.Add(Instruction.Create(OpCodes.Ldarg_0));
        if (!initialize) code.Add(Instruction.Create(OpCodes.Ldarg_1));
        code.Add(Instruction.Create(initialize ? OpCodes.Initobj : OpCodes.Stobj, type));
        code.Add(Instruction.Create(OpCodes.Ldarg_0));
        code.Add(Instruction.Create(OpCodes.Ldobj, type));
        code.Add(Instruction.Create(OpCodes.Ret));
    });
    var claims = Boundaries(stackWidth).Select(value => Returns($"Examples.reference, .scalar (.i{stackWidth} {value})",
        initialize ? 0 : Extended(value, width, signed, stackWidth), stackWidth)).ToList();
    var arguments = $"Examples.reference, .scalar (.i{stackWidth} 17)";
    var pc = initialize ? 1 : 2;
    claims.Add($"({Executes(arguments, "{ Examples.caller with views := [⟨0, 0, 8, true, false⟩] }")}) = " +
        $".error ⟨0, {pc}, .memory .unwritable (.address ⟨0, 0⟩) {width}⟩");
    // Starting with unknown bytes is valid for stores and initialization.
    claims.Add(Returns(arguments, initialize ? 0 : 17, stackWidth,
        "{ Examples.caller with cells := fun _ _ => ⟨255, false⟩ }"));
    if (width < 8)
        claims.Add($"({Executes(arguments, "{ Examples.caller with cells := fun _ _ => ⟨255, true⟩ }")}).map " +
            $"(fun result => result.1.cells 0 {width}) = .ok ⟨255, true⟩");
    Prove(dll, FixtureSelector(dll), name, claims);
}

// Exact indirect encodings, including signed/unsigned loads and truncating stores.
foreach (var (load, store, width, signed) in new[]
{
    (OpCodes.Ldind_I1, OpCodes.Stind_I1, 1, true), (OpCodes.Ldind_U1, OpCodes.Stind_I1, 1, false),
    (OpCodes.Ldind_I2, OpCodes.Stind_I2, 2, true), (OpCodes.Ldind_U2, OpCodes.Stind_I2, 2, false),
    (OpCodes.Ldind_I4, OpCodes.Stind_I4, 4, false), (OpCodes.Ldind_U4, OpCodes.Stind_I4, 4, false),
    (OpCodes.Ldind_I8, OpCodes.Stind_I8, 8, false), (OpCodes.Ldind_I, OpCodes.Stind_I, 8, false)
})
{
    var name = load.Name.Replace('.', '_');
    var stackWidth = width == 8 ? 64 : 32;
    var dll = Fixture(name, (module, method) =>
    {
        method.ReturnType = stackWidth == 64 ? module.TypeSystem.Int64 : module.TypeSystem.Int32;
        method.Parameters.Add(new ParameterDefinition(new ByReferenceType(method.ReturnType)));
        method.Parameters.Add(new ParameterDefinition(method.ReturnType));
        foreach (var op in new[] { OpCodes.Ldarg_0, OpCodes.Ldarg_1, store, OpCodes.Ldarg_0, load, OpCodes.Ret })
            method.Body.Instructions.Add(Instruction.Create(op));
    });
    Prove(dll, FixtureSelector(dll), name, Boundaries(stackWidth).Select(value =>
        Returns($"Examples.reference, .scalar (.i{stackWidth} {value})", Extended(value, width, signed, stackWidth), stackWidth)));

    var readName = name + "-faults";
    var readDll = Fixture(readName, (module, method) =>
    {
        method.ReturnType = stackWidth == 64 ? module.TypeSystem.Int64 : module.TypeSystem.Int32;
        method.Parameters.Add(new ParameterDefinition(new ByReferenceType(method.ReturnType)));
        method.Body.Instructions.Add(Instruction.Create(OpCodes.Ldarg_0));
        method.Body.Instructions.Add(Instruction.Create(load));
        method.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
    });
    Prove(readDll, FixtureSelector(readDll), readName,
    [
        $"({Executes("Examples.reference", "{ Examples.caller with cells := fun _ _ => ⟨0, false⟩ }")}) = .error ⟨0, 1, .memory .uninitialized (.address ⟨0, 0⟩) {width}⟩",
        $"({Executes(".reference (.address ⟨0, 8⟩)")}) = .error ⟨0, 1, .memory .outsideAllocation (.address ⟨0, 8⟩) {width}⟩",
        $"({Executes(".reference .null")}) = .error ⟨0, 1, .memory .nullDereference .null {width}⟩",
        $"({Executes("Examples.reference", "CIL.Safety.expire Examples.caller 0")}) = .error ⟨0, 0, .memory .expiredLifetime (.address ⟨0, 0⟩) 0⟩",
        $"({Executes("Examples.reference", "{ Examples.caller with views := [⟨0, 0, 8, false, true⟩] }")}) = .error ⟨0, 1, .memory .unreadable (.address ⟨0, 0⟩) {width}⟩"
    ]);
}

// sizeof uses the validated managed storage width, including non-32-byte structs.
var sizeDll = Fixture("Sizes", (module, method) =>
{
    method.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
    var tokens = types.Select(t => Primitive(module, t.Name)).Append(module.GetType("Examples.Packet")).ToArray();
    var targets = tokens.Select(t => Instruction.Create(OpCodes.Sizeof, t)).ToArray();
    var code = method.Body.Instructions;
    code.Add(Instruction.Create(OpCodes.Ldarg_0));
    code.Add(Instruction.Create(OpCodes.Switch, targets));
    code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
    code.Add(Instruction.Create(OpCodes.Ret));
    foreach (var target in targets) { code.Add(target); code.Add(Instruction.Create(OpCodes.Ret)); }
});
Prove(sizeDll, FixtureSelector(sizeDll), "Sizes", types.Select(t => t.Width).Append(12).Append(0)
    .Select((width, index) => Returns($".scalar (.i32 {index})", width)));

// Unsupported type tokens and layouts must fail, never become guessed constants.
foreach (var operand in new[] { "pointer", "byref", "object", "string", "array", "double",
    "sequential", "auto", "reference-field", "generic", "generic-instance" })
{
    var name = "Reject-sizeof-" + operand;
    var layout = operand is "sequential" or "auto" or "reference-field" or "generic" or "generic-instance";
    var dll = Fixture(name, (module, method) =>
    {
        var packet = module.GetType("Examples.Packet");
        if (operand is "sequential" or "auto")
            packet.Attributes = (packet.Attributes & ~TypeAttributes.LayoutMask) |
                (operand == "sequential" ? TypeAttributes.SequentialLayout : TypeAttributes.AutoLayout);
        if (operand == "reference-field")
            packet.Fields.First(f => !f.IsStatic).FieldType = module.TypeSystem.Object;
        if (operand is "generic" or "generic-instance")
            packet.GenericParameters.Add(new GenericParameter("T", packet));

        TypeReference type = operand switch
        {
            "pointer" => new PointerType(module.TypeSystem.Int32),
            "byref" => new ByReferenceType(module.TypeSystem.Int32),
            "object" => module.TypeSystem.Object,
            "string" => module.TypeSystem.String,
            "array" => new ArrayType(module.TypeSystem.Int32),
            "double" => module.TypeSystem.Double,
            "generic-instance" => new GenericInstanceType(packet),
            _ => packet
        };
        if (type is GenericInstanceType generic)
            generic.GenericArguments.Add(module.TypeSystem.Int32);
        method.Body.Instructions.Add(Instruction.Create(OpCodes.Sizeof, type));
        method.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
    });

    var output = Path.Combine(root, name, "extraction");
    var rejected = Execute(Extract("extract", dll, "Examples", FixtureSelector(dll), output));
    var marker = operand == "sequential" ? "Invalid field layout" :
        operand == "generic-instance" ? "Unsupported closed generic struct layout" :
        layout && operand != "reference-field" ? "Unsupported aggregate layout" : "Unsupported field type";
    if (rejected.Code == 0 || !rejected.Output.Contains(marker) || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException($"Wrong sizeof rejection ({operand}): {rejected.Output}");
    Console.WriteLine("PASS sizeof rejection: " + operand);
}

// Empty/duplicate tables and dependencies reachable only from a switch target.
foreach (var empty in new[] { false, true })
{
    var name = empty ? "EmptySwitch" : "SwitchCall";
    var dll = Fixture(name, (module, method) =>
    {
        method.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
        var callee = new MethodDefinition("SwitchCallee", MethodAttributes.Static, module.TypeSystem.Int32);
        method.DeclaringType.Methods.Add(callee);
        callee.Body.Instructions.Add(Instruction.Create(OpCodes.Ldc_I4, 17));
        callee.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
        var target = Instruction.Create(OpCodes.Call, callee);
        var code = method.Body.Instructions;
        code.Add(Instruction.Create(OpCodes.Ldarg_0));
        code.Add(Instruction.Create(OpCodes.Switch, empty ? [] : new[] { target, target }));
        code.Add(Instruction.Create(OpCodes.Ldc_I4, 99));
        code.Add(Instruction.Create(OpCodes.Ret));
        code.Add(target);
        code.Add(Instruction.Create(OpCodes.Ret));
    });
    Prove(dll, FixtureSelector(dll), name, new BigInteger[] { 0, 1, 2, 2147483648, 4294967295 }
        .Select(value => Returns($".scalar (.i32 {value})", !empty && value < 2 ? 17 : 99)));
}

// Unsupported targets and forged type tokens cannot hide behind a switch arm.
foreach (var mutation in new[] { "bad-target", "unsupported-arm", "scope-load", "scope-store", "scope-init", "scope-size", "float-size" })
{
    var name = "Reject-" + mutation;
    var dll = Fixture(name, (module, method) =>
    {
        var code = method.Body.Instructions;
        if (mutation.StartsWith("scope-", StringComparison.Ordinal) || mutation == "float-size")
        {
            var fake = new AssemblyNameReference("Fake.Runtime", new Version(10, 0, 0, 0));
            module.AssemblyReferences.Add(fake);
            var type = mutation == "float-size" ? module.TypeSystem.Single : new TypeReference("System", "Int16", module, fake, true);
            var op = mutation switch { "scope-load" => OpCodes.Ldobj, "scope-store" => OpCodes.Stobj, "scope-init" => OpCodes.Initobj, _ => OpCodes.Sizeof };
            if (op != OpCodes.Sizeof)
            {
                method.Parameters.Add(new ParameterDefinition(new ByReferenceType(module.TypeSystem.Int16)));
                code.Add(Instruction.Create(OpCodes.Ldarg_0));
                if (op == OpCodes.Stobj) code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
            }
            code.Add(Instruction.Create(op, type));
            if (op == OpCodes.Stobj || op == OpCodes.Initobj) code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
        }
        else
        {
            method.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
            var start = Instruction.Create(OpCodes.Ldarg_0);
            var target = Instruction.Create(OpCodes.Ldc_I4_1);
            code.Add(start);
            code.Add(Instruction.Create(OpCodes.Switch, new[] { target }));
            code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
            code.Add(Instruction.Create(OpCodes.Ret));
            code.Add(target);
            if (mutation == "unsupported-arm")
            {
                code.Add(Instruction.Create(OpCodes.Ldc_I4_1));
                code.Add(Instruction.Create(OpCodes.Newarr, module.TypeSystem.Int32));
            }
        }
        code.Add(Instruction.Create(OpCodes.Ret));
    });

    if (mutation == "bad-target")
    {
        // Corrupt the encoded switch displacement to point outside the method.
        var bytes = File.ReadAllBytes(dll);
        using var module = ModuleDefinition.ReadModule(new MemoryStream(bytes));
        var method = module.GetType("Examples.PrimitiveOperations").Methods.Single(m => m.Name == "Fixture");
        using var pe = new PEReader(new MemoryStream(bytes));
        var section = pe.PEHeaders.SectionHeaders.Single(s => method.RVA >= s.VirtualAddress && method.RVA < s.VirtualAddress + s.SizeOfRawData);
        var body = section.PointerToRawData + method.RVA - section.VirtualAddress;
        var header = (bytes[body] & 3) == 2 ? 1 : (BinaryPrimitives.ReadUInt16LittleEndian(bytes.AsSpan(body)) >> 12) * 4;
        var offset = method.Body.Instructions.Single(i => i.OpCode == OpCodes.Switch).Offset;
        BinaryPrimitives.WriteInt32LittleEndian(bytes.AsSpan(body + header + offset + 5), int.MaxValue);
        File.WriteAllBytes(dll, bytes);
    }

    var rejected = Execute(Extract("extract", dll, "Examples", FixtureSelector(dll), Path.Combine(root, name)));
    var marker = mutation switch
    {
        "bad-target" => "Malformed switch targets",
        "unsupported-arm" => "Unsupported instruction", "float-size" => "Unsupported field type",
        _ => "Unsupported type identity"
    };
    if (rejected.Code == 0 || !rejected.Output.Contains(marker))
        throw new InvalidOperationException("Wrong rejection: " + rejected.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}

// Changing the actual write must fail the same universal roundtrip contract.
var wrongDll = Fixture("WrongWrite", (module, method) =>
{
    var original = module.GetType("Examples.PrimitiveOperations").Methods.Single(m => m.Name == "ReadWrite");
    original.Body.Instructions.Single(i => i.OpCode == OpCodes.Ldarg_1).OpCode = OpCodes.Ldc_I4_0;
    method.Body.Instructions.Add(Instruction.Create(OpCodes.Ldc_I4_0));
    method.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
});
var wrongOutput = Path.Combine(root, "WrongWrite");
var failed = false;
try
{
    verification.Verify(wrongDll, "Examples", "PrimitiveOperations::ReadWrite(int&,int)",
        At("Examples/Proofs/PrimitiveReadWrite.lean"), wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    failed = true;
}
if (!failed || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Incorrect write accepted");

queue.Flush();

Console.WriteLine($"Primitive operation proofs passed: {cases} cases; incorrect write rejected.");
