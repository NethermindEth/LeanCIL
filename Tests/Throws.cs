#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Throws");
Directory.CreateDirectory(root);
var rejected = new RejectedEvidence(root);
var queue = new GeneratedQueue(verification, assembly);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Throws")!;
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.Safety.Execution");

// Every fault is located at the folded `throw` and names the type .NET raises.
foreach (var (name, selector, inputs) in new (string, string, uint[][])[]
{
    ("Quotient", "Throws::Quotient(uint,uint)", [[7, 2], [7, 0], [0, 0], [uint.MaxValue, 1]]),
    ("Percent", "Throws::Percent(uint)", [[0], [100], [101], [uint.MaxValue]]),
    ("Inner", "Throws::Inner(uint)", [[0], [1]]),
    ("ArgumentInner", "Throws::ArgumentInner(uint)", [[0], [1]]),
    ("ActualValue", "Throws::ActualValue(uint)", [[0], [1]])
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
        string.Join(" ∧\n", claims) + " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) +
        "⟩\n#print axioms correctness\nend ExampleProof\n");
    queue.Add(new(selector, proof, Path.Combine(root, name + "-Verified")), () =>
        Console.WriteLine($"PASS {name}: {claims.Count} runtime comparisons, {label} located at method {method} pc {pc}"));

    // A forged type must fail the feature certificate, independently of the instruction lemma.
    var forgedLabel = label == "System.InvalidOperationException"
        ? "System.DivideByZeroException" : "System.InvalidOperationException";
    var forged = source.Replace($".throw \"{label}\"", $".throw \"{forgedLabel}\"");
    var mutated = Path.Combine(root, name + "-forged.lean");
    File.WriteAllText(mutated, forged);
    rejected.Add(mutated, $"PASS {name}: forged raised type rejected by the feature certificate",
        $"Extraction.FeatureFlowValid rawLayouts.toArray method{method}Closed", "is false");
    if (name is "Inner" or "ArgumentInner" or "ActualValue")
    {
        var nonNull = Path.Combine(root, name + "-non-null.lean");
        const string nullLoad = "opcode := 20, operand := .none";
        if (!source.Contains(nullLoad, StringComparison.Ordinal))
            throw new InvalidOperationException("Missing null constructor argument");
        File.WriteAllText(nonNull, source.Replace(nullLoad,
            "opcode := 114, operand := .text \"not null\"", StringComparison.Ordinal));
        rejected.Add(nonNull, $"PASS {name}: non-null constructor operand rejected",
            $"Extraction.FeatureFlowValid rawLayouts.toArray method{method}Closed", "is false");
    }
}

queue.Flush();
rejected.Check();

// Anything other than the exact encoding without handlers stays unsupported.
foreach (var (mutation, marker) in new[]
{
    ("handler", "Unsupported method metadata"),
    ("no-throw", "Contract imports support call only, not callvirt, newobj or ldftn."),
    ("thrown-null", "Unsupported instruction"),
    ("interior-branch", "Branch into a folded throw"),
    ("non-exception", "Unsupported exception constructor"),
    ("dead-non-exception", ""),
    ("missing-constructor", "Unsupported exception constructor"),
    ("wrong-parameter", "Unsupported exception constructor"),
    ("explicit-this", "Unsupported exception constructor"),
    ("vararg", "Unsupported exception constructor")
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
            case "non-exception":
            case "dead-non-exception":
            case "missing-constructor":
            case "wrong-parameter":
            {
                var original = (MethodReference)code[0].Operand;
                var type = new TypeReference("System", mutation.EndsWith("non-exception", StringComparison.Ordinal) ? "Object" : "DivideByZeroException",
                    module, original.DeclaringType.Scope);
                var constructor = new MethodReference(".ctor", module.TypeSystem.Void, type) { HasThis = true };
                code[0].Operand = constructor;
                if (mutation is "missing-constructor" or "wrong-parameter")
                {
                    var creation = code[0];
                    for (int n = 0; n < (mutation == "missing-constructor" ? 2 : 1); n++)
                    {
                        constructor.Parameters.Add(new ParameterDefinition(mutation == "missing-constructor" ? module.TypeSystem.String : module.TypeSystem.Int32));
                        il.InsertBefore(creation, il.Create(OpCodes.Ldstr, "message"));
                    }
                }
                if (mutation == "dead-non-exception")
                {
                    var returned = il.Create(OpCodes.Ret);
                    il.InsertBefore(code[0], il.Create(OpCodes.Br, returned));
                    il.Append(returned);
                }
                break;
            }
            case "explicit-this": ((MethodReference)code[0].Operand).ExplicitThis = true; break;
            case "vararg": ((MethodReference)code[0].Operand).CallingConvention = MethodCallingConvention.VarArg; break;
            case "interior-branch":
                il.InsertBefore(code[0], il.Create(OpCodes.Br, code[1]));
                il.InsertBefore(code[0], il.Create(OpCodes.Ldnull));
                break;
        }
        module.Write(dll);
    }
    if (mutation is "non-exception" or "missing-constructor")
    {
        var expected = mutation == "non-exception" ? "System.Runtime.CompilerServices.RuntimeWrappedException" : "System.MissingMethodException";
        try
        {
            Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Throws")!.GetMethod("Quotient")!.Invoke(null, [1u, 0u]);
            throw new InvalidOperationException("The runtime fixture unexpectedly returned: " + mutation);
        }
        catch (TargetInvocationException error) when (error.InnerException?.GetType().FullName == expected) { }
        Console.WriteLine($"PASS runtime throws {expected} for {mutation}; it must not be folded as the constructed type");
    }
    var result = Execute(Extract("extract", dll, "Examples", "Throws::Quotient(uint,uint)", output));
    if (mutation == "dead-non-exception")
    {
        if (result.Code != 0) throw new InvalidOperationException("Unreachable unsupported throw blocked extraction: " + result.Output);
        Run(["lake", "env", "lean", Path.Combine(output, "Extracted.lean")], cwd: verification.CheckoutPackage());
        Console.WriteLine("PASS unreachable unsupported throw stays excluded and its certificate checks");
        continue;
    }
    if (result.Code != 1 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        File.Exists(Path.Combine(output, "verified.json")) || !result.Output.Contains(marker))
        throw new InvalidOperationException("Incorrect throw rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}
Console.WriteLine("PASS folded throws, located faults, runtime comparisons, forged types and exact-pattern rejection");
