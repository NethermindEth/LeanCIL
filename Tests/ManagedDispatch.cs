#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Text.RegularExpressions;
using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/ManagedDispatch");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root);
var rejected = new RejectedEvidence(root);
var dll = Path.Combine(root, "ManagedDispatch.dll");
string selector;
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var methods = module.GetType("Examples.ManagedDispatch").Methods;
    foreach (var method in methods.Where(method =>
        method.Name is "Repeat" or "Raise" or "Dispatch" or "Address" or "LocalEscape"))
    {
        var call = method.Body.Instructions.Single(instruction =>
            instruction.OpCode.Code is Code.Call or Code.Calli);
        if (call.Next?.OpCode.Code != Code.Ret) throw new Exception("Missing adjacent dispatch return");
        var processor = method.Body.GetILProcessor();
        if (method.Name == "Repeat")
        {
            // The handler dispatches itself indirectly, exercising a genuine cyclic catalog.
            processor.InsertBefore(call, Instruction.Create(OpCodes.Ldftn, (MethodReference)call.Operand));
            var signature = new CallSite(module.TypeSystem.Int32);
            signature.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
            call.OpCode = OpCodes.Calli;
            call.Operand = signature;
        }
        processor.InsertBefore(call, Instruction.Create(OpCodes.Tail));
    }
    selector = methods.Single(method => method.Name == "Dispatch").FullName;
    module.Write(dll);
}
var normalDll = Path.Combine(root, "ManagedDispatchNormal.dll");
using (var module = ModuleDefinition.ReadModule(dll))
{
    var dispatch = module.GetType("Examples.ManagedDispatch").Methods.Single(method => method.Name == "Dispatch");
    var prefix = dispatch.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Tail);
    dispatch.Body.GetILProcessor().Remove(prefix);
    module.Write(normalDll);
}
var runtimeAddress = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.ManagedDispatch")!
    .GetMethod("Address")!.CreateDelegate<Func<int, int>>();
if (runtimeAddress(3) != 17) throw new Exception("Runtime indirect tail cycle differs");
foreach (var name in new[] { "Address", "LocalEscape", "Dispatch", "DispatchNormal" })
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", name == "DispatchNormal" ? normalDll : dll,
        name.StartsWith("Dispatch", StringComparison.Ordinal) ? selector : $"ManagedDispatch::{name}(int)", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    var claims = new List<string>();
    const string memory = "{ allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, " +
        "views := [], nextIdentity := 0 }";
    string RunCase(string args, int fuel = 128) =>
        $"CIL.Safety.invoke Extracted.program {fuel} 0 [{args}] dispatchMemory";
    if (name == "Address")
    {
        claims.Add($"({RunCase(".scalar (.i32 3)")}).map Prod.snd = .ok [.scalar (.i32 17)]");
    }
    else if (name == "LocalEscape")
    {
        claims.Add($"(match {RunCase(".scalar (.i32 42)")} with | .error fault => some fault.fault | " +
            ".ok _ => none) = some (.memory .expiredLifetime (.address ⟨0, 0⟩) 0)");
    }
    else
    {
        // Stable identities come from the actual compiled metadata, not program positions.
        using var module = ModuleDefinition.ReadModule(dll);
        var methods = module.GetType("Examples.ManagedDispatch").Methods;
        var repeat = methods.Single(method => method.Name == "Repeat").MetadataToken.ToUInt32();
        var raise = methods.Single(method => method.Name == "Raise").MetadataToken.ToUInt32();
        var owner = module.Assembly.Name.FullName + "::Examples.ManagedDispatch";
        string Identity(uint token) => $"⟨{System.Text.Json.JsonSerializer.Serialize(owner)}, {token}, []⟩";
        string Table(string targets) => $".methodTable ⟨dispatchSignature, some [{targets}]⟩";
        var table = Table(Identity(repeat) + ", " + Identity(raise));
        string Args(string view, int index, int value) => $"{view}, .scalar (.i32 {index}), .scalar (.i32 {value})";
        claims.Add($"({RunCase(Args(table, 0, 3))}).map Prod.snd = .ok [.scalar (.i32 17)]");
        string Fault(string args, int fuel = 128) =>
            $"(match {RunCase(args, fuel)} with | .error fault => some fault.fault | .ok _ => none)";
        claims.Add($"{Fault(Args(table, 1, 2))} = some (.thrown \"System.ArgumentException\")");
        claims.Add($"{Fault(Args(table, 2, 0))} = some (.thrown \"System.IndexOutOfRangeException\")");
        claims.Add($"{Fault(Args(".methodTable ⟨dispatchSignature, none⟩", 0, 0))} = " +
            "some (.thrown \"System.NullReferenceException\")");
        claims.Add($"{Fault(Args(Table(Identity(uint.MaxValue)), 0, 0))} = some .invalidState");
        claims.Add($"({RunCase(Args(table, 0, 3), 1)}).isOk = false");
    }
    File.WriteAllText(proof, source + "\nprivate def dispatchMemory : CIL.Safety.Memory := " + memory + "\n" + """
        private def dispatchSignature : CIL.ManagedSignature :=
          ⟨.atom CIL.Extraction.runtimeScope "System.Int32",
            [.atom CIL.Extraction.runtimeScope "System.Int32"]⟩
        """ + "\ntheorem managed_dispatch_result :\n" + string.Join(" ∧\n", claims) +
        " := " + (claims.Count == 1 ? "by rfl" :
            "by exact ⟨" + string.Join(", ", claims.Select(_ => "by rfl")) + "⟩") +
        "\n#print axioms managed_dispatch_result\n");
    evidence.Add(proof, "PASS compiled typed indirect dispatch: " + name);
    if (name != "Address") continue;
    var call = source.Split('\n').First(line => line.TrimStart().StartsWith(".managed (.call ",
        StringComparison.Ordinal));
    var address = source.Split('\n').First(line => line.TrimStart().StartsWith(".managed (.address ",
        StringComparison.Ordinal));
    var changedTarget = Regex.Replace(call, @"method := \d+", "method := 999999");
    foreach (var (mutation, theorem, before, after, marker) in new[]
    {
        ("target", "method0_calls_validated", call, changedTarget, "ManagedCallsValid"),
        ("identity", "method0_calls_validated", call,
            call.Replace("Examples.ManagedDispatch", "Examples.ForgedDispatch", StringComparison.Ordinal),
            "ManagedCallsValid"),
        ("signature", "method0_calls_validated", call,
            call.Replace("System.Int32", "System.UInt32", StringComparison.Ordinal), "ManagedCallsValid"),
        ("numeric-pointer", "method0_calls_validated", address, "  .const64 0,", "ManagedCallsValid"),
        ("convention", "method0_calls_validated", "] false false 0 },", "] false false 1 },",
            "ManagedCallsValid"),
        ("tail", "method0_features_validated", call,
            call.Replace("] true)", "] false)", StringComparison.Ordinal), "FeatureFlowValid")
    })
    {
        var narrowed = NarrowEvidence(source, theorem);
        if (before == after || !narrowed.Contains(before, StringComparison.Ordinal))
            throw new Exception("Missing managed mutation: " + mutation);
        var path = Path.Combine(root, "Rejected-" + mutation + ".lean");
        File.WriteAllText(path, narrowed.Replace(before, after, StringComparison.Ordinal));
        rejected.Add(path, "PASS exact managed dispatch evidence rejection: " + mutation, marker);
    }
}
foreach (var mutation in new[] { "convention", "prefix-entry" })
{
    var malformed = Path.Combine(root, "Malformed-" + mutation + ".dll");
    using (var module = ModuleDefinition.ReadModule(dll))
    {
        var dispatch = module.GetType("Examples.ManagedDispatch").Methods.Single(method => method.Name == "Dispatch");
        var call = dispatch.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Calli);
        if (mutation == "convention") ((CallSite)call.Operand).CallingConvention = MethodCallingConvention.C;
        else dispatch.Body.GetILProcessor().InsertBefore(call.Previous, Instruction.Create(OpCodes.Br, call));
        module.Write(malformed);
    }
    var result = Execute(["dotnet", ExtractorPath, "extract", malformed, selector,
        Path.Combine(root, "Malformed-" + mutation)]);
    var marker = mutation == "convention" ? "calling convention" : "tail";
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.OrdinalIgnoreCase))
        throw new Exception("Incorrect managed metadata rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS managed metadata rejection: " + mutation);
}
evidence.Check();
rejected.Check();
