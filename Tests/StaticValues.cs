#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include PreparedLeanFixtures.cs

using System.Reflection;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/StaticValues");
var pending = new GeneratedQueue(verification, assembly);
Directory.CreateDirectory(root);
const string word = "Examples.Word256";
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType(word)!;
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.Safety.Execution");

string[] Extract(string dll, string selector, string output, bool assume = true) =>
    ["dotnet", ExtractorPath, "extract", dll, selector, output, .. assume ? new[] { "--assume-initialized", word } : []];
ulong[] Limbs(string field)
{
    var value = runtime.GetField(field)!.GetValue(null)!;
    return new[] { "U0", "U1", "U2", "U3" }.Select(name => (ulong)runtime.GetField(name)!.GetValue(value)!).ToArray();
}
// The theorem names each limb, so a wrong byte order or value cannot satisfy it.
string Claim(string method, ulong[] limbs) =>
    $"∃ bytes, (CIL.Safety.invoke Extracted.program 64 0 [] Examples.empty).map Prod.snd = .ok [.scalar (.aggregate bytes)] ∧\n" +
    $"  (List.range {limbs.Length}).map (fun i => CIL.Safety.byteNumber ((bytes.drop (8 * i)).take 8)) = [{string.Join(", ", limbs)}]";
void Prove(string dll, string selector, string folder, string claim, Action<JsonElement> passed)
{
    var output = Path.Combine(root, folder);
    var proof = Path.Combine(root, folder + ".lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness :\n" +
        claim + " :=\n  ⟨_, rfl, by decide⟩\n#print axioms correctness\nend ExampleProof\n");
    void Report()
    {
        var report = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")));
        if (!report.GetProperty("initializedTypes").EnumerateArray().Select(item => item.GetString())
            .SequenceEqual(new[] { word }))
            throw new InvalidOperationException("Verification omitted the initialization assumption");
        passed(report);
    }
    if (folder == "One")
    {
        Run(Extract(dll, selector, output));
        var verified = Run(["dotnet", ExtractorPath, "verify", output, "--proof", proof]);
        if (!verified.Contains($"Caller assumption: {word} initialization completed successfully before invocation."))
            throw new InvalidOperationException("Verification omitted the initialization assumption:\n" + verified);
        Report();
    }
    else pending.Add(new(selector, proof, output, Assembly: dll, InitializedTypes: [word]), Report);
}

// Limbs agree with the values .NET's static constructor stored.
foreach (var (method, field) in new[] { ("One", "One"), ("Zero", "Zero"), ("Min", "MinValue"), ("Max", "MaxValue") })
{
    Prove(assembly, $"StaticValues::{method}()", method, Claim(method, Limbs(field)), report =>
    {
        if (report.GetProperty("staticValues").EnumerateArray().Single().GetString() != $"{word} {word}::{field}")
            throw new InvalidOperationException("Verification report omitted the static value assumption for " + field);
        Console.WriteLine($"PASS {field}: limbs {string.Join(", ", Limbs(field))} from the static constructor");
    });
}

foreach (var (method, limbs) in new[] { ("Pair32", new ulong[] { 7, 9 }), ("Pair64", new ulong[] { 11, 13 }) })
    Prove(assembly, $"StaticValues::{method}()", method, Claim(method, limbs), _ =>
        Console.WriteLine($"PASS closed generic static constructor {method}, including zero-filled padding"));

// ExpMod's shape: a loaded value stored through an out parameter.
var select = Path.Combine(root, "Select");
var selectProof = Path.Combine(root, "Select.lean");
File.WriteAllText(selectProof, """
    import Extracted
    import Examples.Support
    namespace ExampleProof
    open CIL.Safety
    def out : Memory := {
      allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨32, 1, []⟩, true, [32]⟩ else none
      cells := fun _ _ => ⟨0, false⟩
      views := [⟨0, 0, 32, true, true⟩]
      nextIdentity := 1 }
    def stored (flag : Nat) : Option (List (BitVec 8)) :=
      match invoke Extracted.program 64 0 [.scalar (.i32 (BitVec.ofNat 32 flag)), .reference (.address ⟨0, 0⟩)] out with
      | .ok (memory, []) => some ((List.range 32).map fun offset => (memory.cells 0 offset).1)
      | _ => none
    theorem correctness : stored 1 = some (1 :: List.replicate 31 0) ∧ stored 0 = some (List.replicate 32 0) := by
      decide +kernel
    end ExampleProof
    """);
pending.Add(new("StaticValues::Select(bool,Examples.Word256&)", selectProof, select, InitializedTypes: [word]),
    () => Console.WriteLine("PASS loaded One and Zero stored through an out parameter"));

// The proved value comes from the static constructor's IL: changing its argument changes the theorem.
var changed = Path.Combine(root, "Changed", "Examples.dll");
Directory.CreateDirectory(Path.GetDirectoryName(changed)!);
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var code = module.GetType(word).Methods.Single(m => m.Name == ".cctor").Body.Instructions;
    var store = code.Single(i => i.OpCode.Code == Code.Stsfld && ((FieldReference)i.Operand).Name == "One");
    var constant = code[code.IndexOf(store) - 3];
    if (constant.OpCode.Code != Code.Ldc_I4_1) throw new InvalidOperationException("Unexpected One initializer: " + constant);
    constant.OpCode = OpCodes.Ldc_I4_7;
    module.Write(changed);
}
Prove(changed, "StaticValues::One()", "Changed", Claim("One", [7, 0, 0, 0]),
    _ => Console.WriteLine("PASS changed static constructor argument changes the proved limbs"));

foreach (var (method, result) in new[]
    { ("ReadAddress", ".ok [.scalar (.i64 1)]"), ("SameAddress", ".ok [.scalar (.i32 1)]"),
      ("DifferentAddresses", ".ok [.scalar (.i32 0)]") })
{
    var proof = Path.Combine(root, method + ".lean");
    File.WriteAllText(proof, $$"""
        import Extracted
        import Examples.Support
        namespace ExampleProof
        theorem correctness :
            (CIL.Safety.invoke Extracted.program 64 0 [] Examples.empty).map Prod.snd = {{result}} := by
          rfl
        #print axioms correctness
        end ExampleProof
        """);
    pending.Add(new($"StaticValues::{method}()", proof, Path.Combine(root, method), InitializedTypes: [word]),
        () => Console.WriteLine("PASS readonly static address " + method));
}
var writeProof = Path.Combine(root, "Overwrite.lean");
File.WriteAllText(writeProof, """
    import Extracted
    import Examples.Support
    namespace ExampleProof
    def denied : Bool := match CIL.Safety.invoke Extracted.program 64 0 [] Examples.empty with
      | .error ⟨_, _, .memory .unwritable _ _⟩ => true
      | _ => false
    theorem correctness : denied = true := by decide +kernel
    #print axioms correctness
    end ExampleProof
    """);
pending.Add(new("StaticValues::Overwrite()", writeProof, Path.Combine(root, "Overwrite"), InitializedTypes: [word]),
    () => Console.WriteLine("PASS readonly static address cannot be written through Unsafe.AsRef"));
pending.Flush();

// The certificate recomputes the initializer: forged bytes in the extracted program fail translation_valid.
var source = File.ReadAllText(Path.Combine(root, "One", "Extracted.lean"));
var one = "bytes := [(BitVec.ofNat 8 1), ";
if (!source.Contains(one) || !source.Contains(".staticValue [(BitVec.ofNat 8 1), "))
    throw new InvalidOperationException("Missing One descriptor in the extraction");
var forged = Path.Combine(root, "One-forged.lean");
File.WriteAllText(forged, source.Replace("[(BitVec.ofNat 8 1), ", "[(BitVec.ofNat 8 2), "));
var forgedResult = Execute(["lake", "env", "lean", forged], cwd: verification.CheckoutPackage());
if (forgedResult.Code == 0 || !forgedResult.Output.Contains("Extraction.StaticValuesValid program"))
    throw new InvalidOperationException("Forged static value was accepted\n" + forgedResult.Output);
Console.WriteLine("PASS forged static value rejected by the extraction certificate");

void Reject(string dll, string selector, string name, string marker, bool assume = true)
{
    var output = Path.Combine(root, "Reject-" + name);
    Directory.CreateDirectory(output);
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var result = Execute(Extract(dll, selector, output, assume));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) || !result.Output.Contains(marker))
        throw new InvalidOperationException($"Incorrect rejection: {name}\n{result.Output}");
    Console.WriteLine("PASS rejection: " + name);
}

Reject(assembly, "StaticValues::One()", "unassumed", $"requires --assume-initialized {word}", assume: false);
Reject(assembly, "StaticValues::ReadAddress()", "address-unassumed",
    $"requires --assume-initialized {word}", assume: false);

// A store outside the static constructor is rejected, and the field is no longer fixed elsewhere.
var mutations = new Dictionary<string, Action<ModuleDefinition>>
{
    ["store"] = module =>
    {
        var one = module.GetType(word).Fields.Single(f => f.Name == "One");
        var body = module.GetType("Examples.StaticValues").Methods.Single(m => m.Name == "Zero").Body;
        var il = body.GetILProcessor();
        il.InsertAfter(body.Instructions[0], il.Create(OpCodes.Dup));
        il.InsertAfter(body.Instructions[1], il.Create(OpCodes.Stsfld, one));
    },
    ["twice"] = module =>
    {
        var code = module.GetType(word).Methods.Single(m => m.Name == ".cctor").Body;
        var store = code.Instructions.Single(i => i.OpCode.Code == Code.Stsfld && ((FieldReference)i.Operand).Name == "One");
        var il = code.GetILProcessor();
        il.InsertBefore(code.Instructions[^1], il.Create(OpCodes.Ldsfld, (FieldReference)store.Operand));
        il.InsertBefore(code.Instructions[^1], il.Create(OpCodes.Stsfld, (FieldReference)store.Operand));
    },
    // `jmp` leaves the static constructor, so its stores never run.
    ["jump"] = module =>
    {
        var code = module.GetType(word).Methods.Single(m => m.Name == ".cctor").Body;
        var target = module.GetType("Examples.StaticValues").Methods.Single(m => m.Name == "Overwrite");
        code.GetILProcessor().InsertBefore(code.Instructions[0], Instruction.Create(OpCodes.Jmp, target));
    },
    ["constructor-static"] = module =>
    {
        var constructor = module.GetType(word).Methods.Single(method => method.Name == ".cctor");
        var store = constructor.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Stsfld &&
            ((FieldReference)instruction.Operand).Name == "MaxValue");
        constructor.Body.Instructions[constructor.Body.Instructions.IndexOf(store) - 1].Operand = constructor;
    },
    ["constructor-return"] = module =>
    {
        var constructor = module.GetType(word).Methods.Single(method => method.Name == ".ctor");
        constructor.ReturnType = module.TypeSystem.Int32;
    }
};
foreach (var (name, mutate) in mutations)
{
    var dll = Path.Combine(root, "Mutation-" + name, "Examples.dll");
    Directory.CreateDirectory(Path.GetDirectoryName(dll)!);
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        mutate(module);
        module.Write(dll);
    }
    if (name == "store")
    {
        Reject(dll, "StaticValues::Zero()", "store-outside-constructor", $"Unsupported static field store: IL_0006: stsfld {word} {word}::One");
        Reject(dll, "StaticValues::One()", "stored-outside-constructor", "It is also stored outside its static constructor, in Examples.Word256 Examples.StaticValues::Zero()");
    }
    else if (name == "twice") Reject(dll, "StaticValues::One()", "stored-twice", "stores it 2 times");
    else if (name.StartsWith("constructor-", StringComparison.Ordinal))
        Reject(dll, "StaticValues::Max()", name, "Its value is not a same-assembly static call or struct construction");
    else Reject(dll, "StaticValues::One()", "jump-before-store", "Control flow precedes its store");
}
Console.WriteLine("PASS static readonly values, runtime limbs, changed initializers, forged certificates and write rejection");
