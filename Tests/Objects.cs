#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using Mono.Cecil;
using Mono.Cecil.Cil;

// Class instances on the checked heap: proofs about identity and presence, and the named
// rejection of every class shape or access the model does not represent.
using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Objects");
Directory.CreateDirectory(root);

foreach (var (proof, entry) in new[]
{
    ("SameObject", "Objects::Same(Examples.Account,Examples.Account)"),
    ("NullObject", "Objects::IsNull(Examples.Account)"),
    ("PresentObject", "Objects::IsPresent(Examples.Account)"),
    ("FirstPresentObject", "Objects::FirstPresent(Examples.Account,Examples.Account)")
})
{
    verification.Verify(assembly, "Examples", entry, At($"Examples/Proofs/{proof}.lean"), Path.Combine(root, proof));
    Console.WriteLine($"PASS {proof}: {entry}");
}

foreach (var mutation in new[] { "abstract", "base", "explicit", "finalizer", "interface", "byref", "field" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string expected;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var account = module.GetType("Examples.Account");
        var method = module.GetType("Examples.Objects").Methods.Single(candidate => candidate.Name == "IsNull");
        var runtime = module.TypeSystem.Object.Scope;
        switch (mutation)
        {
            case "abstract": account.IsAbstract = true; break;
            case "base": account.BaseType = new TypeReference("System", "Exception", module, runtime); break;
            case "explicit":
                account.IsAutoLayout = false;
                account.IsExplicitLayout = true;
                foreach (var field in account.Fields) field.Offset = 0;
                break;
            case "finalizer":
                var finalizer = new MethodDefinition("Finalize", MethodAttributes.Family | MethodAttributes.Virtual |
                    MethodAttributes.HideBySig, module.TypeSystem.Void);
                finalizer.Body.GetILProcessor().Emit(OpCodes.Ret);
                account.Methods.Add(finalizer);
                break;
            case "interface":
                method.Parameters[0].ParameterType = module.GetType("Examples.ICounterValue");
                break;
            case "byref":
                method.Parameters[0].ParameterType = new ByReferenceType(account);
                break;
            case "field":
                var load = method.Body.Instructions[1];
                var processor = method.Body.GetILProcessor();
                processor.InsertBefore(load, processor.Create(OpCodes.Ldfld,
                    account.Fields.Single(field => field.Name == "Limit")));
                processor.Replace(load, processor.Create(OpCodes.Ldc_I4_0));
                break;
        }
        expected = mutation switch
        {
            "abstract" => "Unsupported class instance type: Examples.Account\n  An abstract class",
            "base" => "Unsupported class instance type: Examples.Account\n  Only classes deriving directly",
            "explicit" => "Unsupported class instance type: Examples.Account\n  Explicit class layout",
            "finalizer" => "Unsupported class instance type: Examples.Account\n  A finalizer",
            "interface" => "Unsupported class instance type: Examples.ICounterValue\n  Interface-typed values",
            "byref" => "Unsupported by-reference class instance: Examples.Account&",
            "field" => "Unsupported class instance field access: System.UInt32 Examples.Account::Limit",
            _ => throw new InvalidOperationException("Unknown class rejection fixture: " + mutation)
        };
        module.Write(dll);
    }
    var parameter = mutation switch
    {
        "interface" => "Examples.ICounterValue", "byref" => "Examples.Account&", _ => "Examples.Account"
    };
    var result = Execute(["dotnet", ExtractorPath, "extract", dll, $"Objects::IsNull({parameter})", output]);
    if (result.Code != 1 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !result.Output.Replace("\r\n", "\n").Contains(expected, StringComparison.Ordinal))
        throw new InvalidOperationException($"Incorrect class rejection: {mutation}\n{result.Output}");
    Console.WriteLine($"PASS class rejection: {mutation}");
}
Console.WriteLine("PASS objects: identity and presence proofs, and named rejection of unmodelled class shapes");
