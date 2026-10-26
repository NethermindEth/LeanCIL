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

Reject("unassumed", assembly, "ReadByte", "Unsupported method metadata or static initialisation", assume: false);
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

rejected.Check();
