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
var root = At("artifacts/Throws");
Directory.CreateDirectory(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Throws")!;
Run(["lake", "build", "CIL.Extraction.Translation", "CIL.Safety.Execution"]);

// Every fault is located at the folded `throw` and names the type .NET raises.
foreach (var (name, selector, inputs) in new (string, string, uint[][])[]
{
    ("Quotient", "Throws::Quotient(uint,uint)", [[7, 2], [7, 0], [0, 0], [uint.MaxValue, 1]]),
    ("Percent", "Throws::Percent(uint)", [[0], [100], [101], [uint.MaxValue]])
})
{
    var folder = Path.Combine(root, name);
    Run(Extract("extract", assembly, "Examples", selector, folder));
    var extracted = Path.Combine(folder, "Extracted.lean");
    var source = File.ReadAllText(extracted);
    var site = Regex.Match(source,
        @"(?m)^@\[cil_code ↓\] theorem method(\d+)_instruction(\d+) : method\d+\.code\[\d+\]\? = some \(\.throw ""([\w.]+)"" : Op\) := rfl\r?$");
    if (!site.Success) throw new InvalidOperationException($"No folded throw in {name}");
    var (method, pc, label) = (site.Groups[1].Value, site.Groups[2].Value, site.Groups[3].Value);

    var claims = inputs.Select(input =>
    {
        string outcome;
        try { outcome = $".ok [.scalar (.i32 {(uint)runtime.GetMethod(name)!.Invoke(null, [.. input.Cast<object>()])!})]"; }
        catch (TargetInvocationException error) { outcome = $".error ⟨{method}, {pc}, .thrown \"{error.InnerException!.GetType().FullName}\"⟩"; }
        return $"(CIL.Safety.invoke Extracted.program 64 0 [{string.Join(", ", input.Select(v => $".scalar (.i32 {v})"))}] Examples.empty).map Prod.snd = {outcome}";
    }).ToList();
    var proof = Path.Combine(folder, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    verification.Verify(assembly, "Examples", selector, proof, Path.Combine(root, name + "-Verified"));
    Console.WriteLine($"PASS {name}: {claims.Count} runtime comparisons, {label} located at method {method} pc {pc}");

    // A forged type must fail the feature certificate, independently of the instruction lemma.
    var forged = source.Replace($".throw \"{label}\"", ".throw \"System.InvalidOperationException\"");
    var mutated = Path.Combine(root, name + "-forged.lean");
    File.WriteAllText(mutated, forged);
    var result = Execute(["lake", "env", "lean", mutated]);
    if (result.Code == 0 || !result.Output.Contains($"Extraction.FeatureFlowValid method{method}Closed") || !result.Output.Contains("is false"))
        throw new InvalidOperationException($"Forged raised type was accepted for {name}\n{result.Output}");
    Console.WriteLine($"PASS {name}: forged raised type rejected by the feature certificate");
}

// Anything other than the exact encoding without handlers stays unsupported.
foreach (var (mutation, marker) in new[]
{
    ("handler", "Unsupported method metadata"),
    ("no-throw", "Contract imports support call only, not callvirt, newobj or ldftn."),
    ("thrown-null", "Unsupported instruction"),
    ("interior-branch", "Branch into a folded throw")
})
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var helper = module.GetType("Examples.Throws").Methods.Single(m => m.Name == "ThrowDivideByZero").Body;
        var code = helper.Instructions;
        var il = helper.GetILProcessor();
        if (code.Count != 2 || code[0].OpCode.Code != Code.Newobj || code[1].OpCode.Code != Code.Throw)
            throw new InvalidOperationException("Unexpected compiled throw helper");
        switch (mutation)
        {
            case "handler":
                var leave = il.Create(OpCodes.Ret);
                il.Append(il.Create(OpCodes.Pop));
                il.Append(il.Create(OpCodes.Leave, leave));
                il.Append(leave);
                helper.ExceptionHandlers.Add(new ExceptionHandler(ExceptionHandlerType.Catch)
                {
                    TryStart = code[0], TryEnd = code[2], HandlerStart = code[2], HandlerEnd = leave,
                    CatchType = module.ImportReference(typeof(Exception))
                });
                break;
            case "no-throw":
                il.Replace(code[1], il.Create(OpCodes.Pop));
                il.Append(il.Create(OpCodes.Ret));
                break;
            case "thrown-null": il.Replace(code[0], il.Create(OpCodes.Ldnull)); break;
            case "interior-branch":
                il.InsertBefore(code[0], il.Create(OpCodes.Br, code[1]));
                il.InsertBefore(code[0], il.Create(OpCodes.Ldnull));
                break;
        }
        module.Write(dll);
    }
    var result = Execute(Extract("extract", dll, "Examples", "Throws::Quotient(uint,uint)", output));
    if (result.Code != 1 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        File.Exists(Path.Combine(output, "verified.json")) || !result.Output.Contains(marker))
        throw new InvalidOperationException("Incorrect throw rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}
Console.WriteLine("PASS folded throws, located faults, runtime comparisons, forged types and exact-pattern rejection");
