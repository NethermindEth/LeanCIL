#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs

using System.Globalization;
using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/StaticScalarValues");
Directory.CreateDirectory(root);
var rejected = new RejectedEvidence(root);
var evidence = new GeneratedEvidence(root, args.Contains("--measure", StringComparer.Ordinal));
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.StaticScalars")!;
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution");

string[] ExtractScalar(string dll, string method, string output, bool assume = true) =>
    ["dotnet", ExtractorPath, "extract", dll, "StaticScalars::" + method + "()", output,
        .. assume ? new[] { "--assume-initialized", "Examples.StaticScalars" } : []];

string Expected(object value)
{
    if (value is Enum) value = Convert.ChangeType(value, Enum.GetUnderlyingType(value.GetType()),
        CultureInfo.InvariantCulture);
    return value switch
    {
        ulong word => ".i64 " + word,
        long word => ".i64 " + unchecked((ulong)word),
        nuint word => ".i64 " + (ulong)word,
        nint word => ".i64 " + unchecked((ulong)word),
        uint word => ".i32 " + word,
        bool flag => flag ? ".i32 1" : ".i32 0",
        _ => ".i32 " + unchecked((uint)Convert.ToInt32(value, CultureInfo.InvariantCulture))
    };
}

foreach (var method in runtime.GetMethods().Where(method => method.Name.StartsWith("Read", StringComparison.Ordinal)))
{
    var output = Path.Combine(root, method.Name);
    Run(ExtractScalar(assembly, method.Name, output));
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, method.Name + ".lean");
    File.WriteAllText(proof, source + $$"""

        theorem scalar_value :
            (CIL.Safety.invoke Extracted.program 32 0 [] CIL.Extraction.initializerMemory).map Prod.snd =
              .ok [.scalar ({{Expected(method.Invoke(null, null)!)}})] := rfl
        #print axioms scalar_value
        """);
    evidence.Add(proof, "PASS runtime and certified scalar value: " + method.Name);
}

evidence.Check();
void Reject(string name, string dll, string method, string marker, bool assume = true)
{
    var output = Path.Combine(root, "Reject-" + name);
    var result = Execute(ExtractScalar(dll, method, output, assume));
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal))
        throw new Exception("Incorrect scalar rejection: " + name + "\n" + result.Output);
    Console.WriteLine("PASS scalar rejection: " + name);
}

Reject("unassumed", assembly, "ReadByte", "Unsupported static initialisation", assume: false);
foreach (var name in new[] { "mutable", "twice", "branch", "address" })
{
    var dll = Path.Combine(root, name + ".dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var type = module.GetType("Examples.StaticScalars");
        var field = type.Fields.Single(field => field.Name == "Byte");
        var code = type.Methods.Single(method => method.IsConstructor).Body;
        var store = code.Instructions.Single(instruction => instruction.OpCode.Code == Code.Stsfld &&
            ((FieldReference)instruction.Operand).Name == "Byte");
        var il = code.GetILProcessor();
        if (name == "mutable") field.IsInitOnly = false;
        else if (name == "twice")
        {
            il.InsertBefore(store, Instruction.Create(OpCodes.Dup));
            il.InsertAfter(store, Instruction.Create(OpCodes.Stsfld, field));
        }
        else if (name == "branch") il.InsertBefore(code.Instructions[0],
            Instruction.Create(OpCodes.Br, code.Instructions[0]));
        else
        {
            il.InsertBefore(store, Instruction.Create(OpCodes.Ldsflda, field));
            il.InsertBefore(store, Instruction.Create(OpCodes.Pop));
        }
        module.Write(dll);
    }
    Reject(name, dll, "ReadByte", name switch
    {
        "mutable" => "Unsupported static field load",
        "twice" => "stores it 2 times",
        "branch" => "Control flow precedes its store",
        _ => "Its address is taken during initialization"
    });
}

var original = File.ReadAllText(Path.Combine(root, "ReadSignedByte", "Extracted.lean"));
foreach (var (name, before, after, marker) in new[]
{
    ("signedness", "scalar := some true", "scalar := some false", "MethodShapeValid"),
    ("width", "[(BitVec.ofNat 8 128)]", "[(BitVec.ofNat 8 128), (BitVec.ofNat 8 255)]", "MethodShapeValid"),
    ("literal", "literal := some (.i32 4294967168)", "literal := some (.i32 127)", "StaticValuesValid")
})
{
    if (!original.Contains(before, StringComparison.Ordinal)) throw new Exception("Missing tamper target: " + name);
    var proof = Path.Combine(root, "Forged-" + name + ".lean");
    File.WriteAllText(proof, original.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(proof, "PASS Lean scalar evidence rejects " + name, marker);
}

// Seeds from a source extraction cannot run load from the caller's binding: proofs cover every seed.
const string seededType = "Examples.SeededHash";
string[] seedFields = [$"System.UInt64 {seededType}::Seed0", $"System.UInt64 {seededType}::Seed1"];
string[] ExtractSeeded(string dll, string method, string output, bool assume = true) =>
    ["dotnet", ExtractorPath, "extract", dll, "SeededHash::" + method, output,
        .. assume ? new[] { "--assume-initialized", seededType } : []];
var mix = Path.Combine(root, "Opaque-Mix");
Run(ExtractSeeded(assembly, "Hash(ulong)", mix));
var verified = Run(["dotnet", ExtractorPath, "verify", mix, "--proof", At("Examples/Proofs/OpaqueSeeds.lean")]);
if (seedFields.Any(field =>
        !verified.Contains($"Unknown static value: {field} is not computed", StringComparison.Ordinal)) ||
    !verified.Contains("ExampleProof.correctness (seed0 seed1 value : CIL.W64) :", StringComparison.Ordinal))
    throw new Exception("Verification omitted the unknown seeds or their quantifier:\n" + verified);
var seededReport = System.Text.Json.JsonDocument.Parse(File.ReadAllText(Path.Combine(mix, "verified.json")))
    .RootElement.GetProperty("opaqueStaticValues").EnumerateArray().Select(item => item.GetString());
if (!seededReport.SequenceEqual(seedFields))
    throw new Exception("verified.json omitted the unknown seeds");
Console.WriteLine("PASS hash proved for every seed; a fixed seed is refuted and unbound seeds fault");

var mixSource = File.ReadAllText(Path.Combine(mix, "Extracted.lean"));
const string seedBytes = "SeededHash::Seed0\", bytes := [(BitVec.ofNat 8 0)";
if (!mixSource.Contains(seedBytes, StringComparison.Ordinal)) throw new Exception("Missing unknown seed descriptor");
var guessedProof = Path.Combine(root, "Opaque-guessed.lean");
// The zero placeholder is not a value: without a caller binding the load faults instead of reading it.
File.WriteAllText(guessedProof, mixSource + """

    theorem guessed_seed : (CIL.Safety.invoke Extracted.program 16 0 [.scalar (.i64 0)]
        CIL.Safety.Memory.empty).map Prod.snd = .ok [.scalar (.i64 0)] := by rfl
    """);
rejected.Add(guessedProof, "PASS unknown seed is never read as its zero placeholder",
    "CIL.Safety.Memory.empty", "is not definitionally equal");
var forgedSeed = Path.Combine(root, "Opaque-forged.lean");
File.WriteAllText(forgedSeed, mixSource.Replace(seedBytes, seedBytes[..^2] + "5)", StringComparison.Ordinal));
rejected.Add(forgedSeed, "PASS Lean evidence rejects a value written into an unknown seed",
    "StaticValuesValid");

void RejectSeeded(string name, string dll, string method, string marker, bool assume = true)
{
    var result = Execute(ExtractSeeded(dll, method, Path.Combine(root, "Reject-seeded-" + name), assume));
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal))
        throw new Exception("Incorrect unknown seed rejection: " + name + "\n" + result.Output);
    Console.WriteLine("PASS unknown seed rejection: " + name);
}
RejectSeeded("address", assembly, "ByReference()", $"Unsupported static field address: {seedFields[0]}");
RejectSeeded("unassumed", assembly, "Hash(ulong)", "Unsupported static initialisation", assume: false);
foreach (var name in new[] { "mutable", "twice", "outside" })
{
    var dll = Path.Combine(root, "seeded-" + name + ".dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var type = module.GetType(seededType);
        var field = type.Fields.Single(field => field.Name == "Seed0");
        var code = type.Methods.Single(method => method.IsConstructor && method.IsStatic).Body;
        var store = code.Instructions.Single(instruction => instruction.OpCode.Code == Code.Stsfld &&
            ((FieldReference)instruction.Operand).Name == field.Name);
        if (name == "mutable") field.IsInitOnly = false;
        else if (name == "twice")
        {
            code.GetILProcessor().InsertBefore(store, Instruction.Create(OpCodes.Dup));
            code.GetILProcessor().InsertAfter(store, Instruction.Create(OpCodes.Stsfld, field));
        }
        else
        {
            var writer = new MethodDefinition("Overwrite", Mono.Cecil.MethodAttributes.Public |
                Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Void);
            writer.Body.Instructions.Add(Instruction.Create(OpCodes.Ldc_I8, 0L));
            writer.Body.Instructions.Add(Instruction.Create(OpCodes.Stsfld, field));
            writer.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
            type.Methods.Add(writer);
        }
        module.Write(dll);
    }
    RejectSeeded(name, dll, "Hash(ulong)", name switch
    {
        "mutable" => "Unsupported static field load",
        "twice" => "stores it 2 times",
        _ => "It is also stored outside its static constructor"
    });
}

rejected.Check();
