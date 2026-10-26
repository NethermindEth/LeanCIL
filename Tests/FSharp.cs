#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using System.Runtime.Loader;

using var verification = new Program();
var assembly = At("Examples/FSharp/bin/Examples.FSharp.dll");
var root = At("artifacts/FSharp");
Directory.CreateDirectory(root);
var queue = new GeneratedQueue(verification, assembly, "Examples.FSharp");

// Resolve the example's pinned F# runtime when invoking compiled functions.
AssemblyLoadContext.Default.Resolving += (_, name) => name.Name == "FSharp.Core"
    ? AssemblyLoadContext.Default.LoadFromAssemblyPath(At("Examples/FSharp/bin/FSharp.Core.dll")) : null;
var runtime = Assembly.Load(File.ReadAllBytes(assembly));
var arithmetic = runtime.GetType("Examples.FSharp.Arithmetic")!;
ulong[] boundaries = [0, 1, 2, 127, 128, 255, 65535, uint.MaxValue, 1UL << 32, long.MaxValue, 1UL << 63, ulong.MaxValue];
var cases = 0;

// Compare the same compiled assembly against the checked CIL interpreter.
foreach (var name in new[] { "Add", "Minimum", "Calls", "Mutate", "Store" })
{
    var method = arithmetic.GetMethod(name)!;
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var claims = new List<string>();
    foreach (var x in boundaries)
    foreach (var y in name is "Add" or "Minimum" ? boundaries : new ulong[] { 0 })
    {
        object[] inputs = name switch
        {
            "Add" or "Minimum" => [x, y],
            "Store" => [0UL, x],
            _ => [x]
        };
        var expected = (ulong)method.Invoke(null, inputs)!;
        if (name == "Store" && (ulong)inputs[0] != expected)
            throw new InvalidOperationException("F# store did not update its caller");
        var values = name switch
        {
            "Add" or "Minimum" => $".scalar (.i64 {x}), .scalar (.i64 {y})",
            "Store" => $"Examples.reference, .scalar (.i64 {x})",
            _ => $".scalar (.i64 {x})"
        };
        claims.Add($"(CIL.Safety.invoke Extracted.program 64 0 [{values}] Examples.{(name == "Store" ? "caller" : "empty")}).map Prod.snd = .ok [.scalar (.i64 {expected})]");
    }
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 8192\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) + " := by\n  exact ⟨" +
        string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    var parameters = name switch
    {
        "Add" or "Minimum" => "ulong,ulong", "Store" => "ulong&,ulong", _ => "ulong"
    };
    queue.Add(new($"Arithmetic::{name}({parameters})", proof, output), () =>
    {
        var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
        if (name is "Calls" or "Mutate" && !extracted.Contains(".call "))
            throw new InvalidOperationException($"{name} no longer exercises compiled method calls");
        if (name == "Mutate" && !extracted.Contains(".newAggregate "))
            throw new InvalidOperationException("Mutate no longer exercises struct construction");
        cases += claims.Count;
        Console.WriteLine($"PASS F# {name}: {claims.Count} runtime comparisons");
    });
}

// The same language-independent contracts apply to C# and F# assemblies.
foreach (var (selector, contract, name) in new[]
{
    ("Arithmetic::Add(ulong,ulong)", "Add", "UniversalAddition"),
    ("Arithmetic::Store(ulong&,ulong)", "InstanceWriteRead", "UniversalStore"),
    ("Arithmetic::Construct(ulong)", "ConstructorValue", "UniversalConstructor")
})
    queue.Add(new(selector, At($"Examples/Proofs/{contract}.lean"), Path.Combine(root, name)),
        () => Console.WriteLine($"PASS F# {name}: unchanged contract"));

queue.Flush();

var wrongOutput = Path.Combine(root, "WrongAddition");
var failed = false;
try
{
    verification.Verify(assembly, "Examples.FSharp", "Arithmetic::WrongAdd(ulong,ulong)",
        At("Examples/Proofs/Add.lean"), wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    failed = true;
}
if (!failed || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Incorrect F# addition accepted");

var rejectedOutput = Path.Combine(root, "UnsupportedList");
var rejected = Execute(Extract("extract", assembly, "Examples.FSharp", "Arithmetic::UnsupportedList(ulong)", rejectedOutput));
if (rejected.Code == 0 || !rejected.Output.Contains("Unsupported type") ||
    File.Exists(Path.Combine(rejectedOutput, "Extracted.lean")))
    throw new InvalidOperationException("Incorrect F# list rejection: " + rejected.Output);

Console.WriteLine($"PASS {cases} F# runtime comparisons, three universal contracts, incorrect addition and unsupported list rejection");
