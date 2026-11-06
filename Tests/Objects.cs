#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using Mono.Cecil;
using Mono.Cecil.Cil;

// Class instances on the checked heap: proofs about identity, presence and scalar fields, and the
// named rejection of every class shape or access the model does not represent.
using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Objects");
Directory.CreateDirectory(root);

foreach (var (proof, entry) in new[]
{
    ("SameObject", "Objects::Same(Examples.Account,Examples.Account)"),
    ("NullObject", "Objects::IsNull(Examples.Account)"),
    ("PresentObject", "Objects::IsPresent(Examples.Account)"),
    ("FirstPresentObject", "Objects::FirstPresent(Examples.Account,Examples.Account)"),
    ("BalanceField", "Objects::BalanceOf(Examples.Account)"),
    ("ReplaceField", "Objects::Replace(Examples.Account,System.UInt64)"),
    ("LimitField", "Objects::SetLimit(Examples.Account,System.UInt32)")
})
{
    verification.Verify(assembly, "Examples", entry, At($"Examples/Proofs/{proof}.lean"), Path.Combine(root, proof));
    Console.WriteLine($"PASS {proof}: {entry}");
}

foreach (var mutation in new[]
{
    "abstract", "base", "explicit", "finalizer", "interface", "byref", "address", "reference", "fieldType"
})
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
            case "address":
                var receiver = method.Body.Instructions[0];
                var processor = method.Body.GetILProcessor();
                processor.InsertAfter(receiver, processor.Create(OpCodes.Ldind_U4));
                processor.InsertAfter(receiver, processor.Create(OpCodes.Ldflda,
                    account.Fields.Single(field => field.Name == "Limit")));
                processor.Replace(method.Body.Instructions[3], processor.Create(OpCodes.Ldc_I4_0));
                break;
            case "reference":
                var owner = new FieldDefinition("Owner", FieldAttributes.Public, account);
                account.Fields.Add(owner);
                method.Body.GetILProcessor().InsertAfter(method.Body.Instructions[0],
                    Instruction.Create(OpCodes.Ldfld, owner));
                break;
            case "fieldType":
                var rate = new FieldDefinition("Rate", FieldAttributes.Public, module.TypeSystem.Double);
                account.Fields.Add(rate);
                var first = method.Body.Instructions[0];
                var editor = method.Body.GetILProcessor();
                editor.InsertAfter(first, editor.Create(OpCodes.Ldarg_0));
                editor.InsertAfter(first, editor.Create(OpCodes.Pop));
                editor.InsertAfter(first, editor.Create(OpCodes.Ldfld, rate));
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
            "address" => "Unsupported field address on a class instance: System.UInt32 Examples.Account::Limit",
            "reference" => "Unsupported reference-typed field: Examples.Account Examples.Account::Owner",
            "fieldType" => "Unsupported class instance field type: System.Double Examples.Account::Rate",
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
Console.WriteLine("PASS objects: identity, presence and scalar field proofs, and named rejection of unmodelled " +
    "class shapes and field accesses");
