#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/SpanTables");
Directory.CreateDirectory(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.SpanTables")!;
Run(["lake", "build", "CIL.Extraction.Translation", "CIL.Safety.Execution"]);

string Scalar(object value) => value switch
{
    int v => $".scalar (.i32 {unchecked((uint)v)})", uint v => $".scalar (.i32 {v})", ulong v => $".scalar (.i64 {v})",
    _ => throw new InvalidOperationException("Unexpected result type")
};
string Claim(string dll, string name, int[] input, string outcome) =>
    $"(CIL.Safety.invoke Extracted.program 64 0 [{string.Join(", ", input.Select(v => Scalar(v)))}] Examples.empty).map Prod.snd = {outcome}";
void Prove(string dll, string name, string selector, string folder, IReadOnlyList<string> claims)
{
    var proof = Path.Combine(root, folder + ".lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by\n  and_intros <;> rfl\nend ExampleProof\n");
    verification.Verify(dll, "Examples", selector, proof, Path.Combine(root, folder));
}

// Reads agree with .NET, and an out-of-range index faults at get_Item with the type .NET raises.
foreach (var (name, selector, inputs) in new (string, string, int[][])[]
{
    ("Word", "SpanTables::Word(int)", [[0], [7], [8], [-1], [int.MinValue]]),
    ("Power", "SpanTables::Power(int)", [[0], [3], [4], [-1]]),
    ("Count", "SpanTables::Count()", [[]]),
    ("First", "SpanTables::First()", [[]])
})
{
    var folder = Path.Combine(root, name);
    Run(Extract("extract", assembly, "Examples", selector, folder));
    var source = File.ReadAllText(Path.Combine(folder, "Extracted.lean"));
    var site = Regex.Match(source, @"(?m)^@\[cil_code ↓\] theorem method(\d+)_instruction(\d+) : method\d+\.code\[\d+\]\? = some \(\.memory \(\.spanItem \d\) : Op\) := rfl\r?$");
    var claims = inputs.Select(input =>
    {
        try { return Claim(assembly, name, input, $".ok [{Scalar(runtime.GetMethod(name)!.Invoke(null, [.. input.Cast<object>()])!)}]"); }
        catch (TargetInvocationException error) when (site.Success)
        {
            return Claim(assembly, name, input, $".error ⟨{site.Groups[1].Value}, {site.Groups[2].Value}, .thrown \"{error.InnerException!.GetType().FullName}\"⟩");
        }
    }).ToList();
    Prove(assembly, name, selector, name + "-Verified", claims);
    Console.WriteLine($"PASS {name}: {claims.Count} runtime comparisons");

    // The receiver fold is bound by the feature certificate, independently of the instruction lemmas.
    if (!source.Contains("(.nop : Op)")) continue;
    var forged = Path.Combine(root, name + "-forged.lean");
    File.WriteAllText(forged, source.Replace(".nop", ".localAddr 0"));
    var result = Execute(["lake", "env", "lean", forged]);
    if (result.Code == 0 || !Regex.IsMatch(result.Output, @"Extraction\.FeatureFlowValid method\d+Closed") || !result.Output.Contains("is false"))
        throw new InvalidOperationException($"Forged span receiver was accepted for {name}\n{result.Output}");
    Console.WriteLine($"PASS {name}: forged span receiver rejected by the feature certificate");
}

// The proved value comes from the assembly's RVA blob through ldtoken.
var tampered = Path.Combine(root, "Tampered", "Examples.dll");
Directory.CreateDirectory(Path.GetDirectoryName(tampered)!);
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var getter = module.GetType("Examples.SpanTables").Methods.Single(m => m.Name == "get_Words");
    var blob = ((FieldReference)getter.Body.Instructions[0].Operand).Resolve();
    var bytes = blob.InitialValue.ToArray();
    bytes[0] = 0x63;
    blob.InitialValue = bytes;
    module.Write(tampered);
}
Prove(tampered, "Word", "SpanTables::Word(int)", "Tampered", [Claim(tampered, "Word", [0], ".ok [.scalar (.i32 1891)]")]);
Console.WriteLine("PASS tampered RVA blob changes the proved word");

// Any other use of the span local, or entry into the fold, stays unsupported.
foreach (var (mutation, marker) in new[]
{
    ("second-read", "Unsupported span local use"),
    ("computed-index", "Unsupported span local use"),
    ("interior-branch", "Branch into a folded span receiver")
})
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var body = module.GetType("Examples.SpanTables").Methods.Single(m => m.Name == "Word").Body;
        var code = body.Instructions;
        var il = body.GetILProcessor();
        if (code.Count != 7 || code[1].OpCode.Code != Code.Stloc_0 || code[2].OpCode.Code != Code.Ldloca_S || code[6].OpCode.Code != Code.Ret)
            throw new InvalidOperationException("Unexpected compiled span read");
        switch (mutation)
        {
            case "second-read":
                il.InsertBefore(code[6], il.Create(OpCodes.Ldloc_0));
                il.InsertBefore(code[7], il.Create(OpCodes.Pop));
                break;
            case "computed-index":
                il.InsertAfter(code[3], il.Create(OpCodes.Ldc_I4_0));
                il.InsertAfter(code[4], il.Create(OpCodes.Add));
                break;
            case "interior-branch":
                il.InsertBefore(code[1], il.Create(OpCodes.Br, code[2]));
                break;
        }
        module.Write(dll);
    }
    var result = Execute(Extract("extract", dll, "Examples", "SpanTables::Word(int)", output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) || !result.Output.Contains(marker))
        throw new InvalidOperationException("Incorrect span rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}
Console.WriteLine("PASS typed static spans, bounds faults, runtime comparisons, forged receivers and exact-pattern rejection");
