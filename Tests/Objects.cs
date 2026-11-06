#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using Mono.Cecil;
using Mono.Cecil.Cil;

// Class instances on the checked heap: proofs about identity, presence, scalar and class-typed fields,
// instance receivers, calls framed across objects and construction against the heap budget, and the named
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
    ("FirstPresentObject", "Objects::FirstPresent(Examples.Account,Examples.Account)"),
    ("BalanceField", "Objects::BalanceOf(Examples.Account)"),
    ("ReplaceField", "Objects::Replace(Examples.Account,System.UInt64)"),
    ("LimitField", "Objects::SetLimit(Examples.Account,System.UInt32)"),
    ("HeadroomReceiver", "Account::get_Headroom()"),
    ("BumpBoth", "Objects::BumpBoth(Examples.Account,Examples.Account,System.UInt64)"),
    ("FreshObject", "Objects::Fresh(System.UInt32)"),
    ("DepositBoth", "Objects::DepositBoth(Examples.Account,Examples.Account,System.UInt64)"),
    ("DepositTimes", "Objects::DepositTimes(Examples.Account,System.UInt64,System.UInt32)"),
    ("TwoMarkers", "Objects::TwoMarkers()"),
    ("LinkedNodes", "Objects::LinkedValue(Examples.Node,Examples.Node)")
})
{
    verification.Verify(assembly, "Examples", entry, At($"Examples/Proofs/{proof}.lean"), Path.Combine(root, proof));
    Console.WriteLine($"PASS {proof}: {entry}");
}

// The entry's call proof simplifies with the constructor's closed body; without it the proof
// falls back to a whole-method kernel decision.
var constructed = File.ReadAllLines(Path.Combine(root, "FreshObject", "Extracted.lean"));
var construction = constructed.Single(line => line.StartsWith("  .newObject ", StringComparison.Ordinal));
var constructor = construction.Split(' ', StringSplitOptions.RemoveEmptyEntries)[1];
var entryCalls = constructed.Single(line =>
    line.StartsWith("theorem method0_calls_validated ", StringComparison.Ordinal));
if (!entryCalls.Contains("by cil_managed_calls [", StringComparison.Ordinal) ||
    !entryCalls.Contains($"method{constructor}Closed", StringComparison.Ordinal))
    throw new InvalidOperationException("The constructing method's call proof omits the constructor:\n" + entryCalls);
Console.WriteLine("PASS construction call proof names the constructor");

foreach (var mutation in new[]
{
    "abstract", "base", "explicit", "finalizer", "interface", "byref", "address", "reference", "fieldType",
    "virtual", "virtualCall", "receiverAddress"
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
        var getter = account.Methods.Single(candidate => candidate.Name == "get_Headroom");
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
                var owner = new FieldDefinition("Owner", FieldAttributes.Public, module.TypeSystem.String);
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
            case "virtual":
                getter.IsVirtual = true;
                getter.IsNewSlot = true;
                break;
            case "virtualCall":
                getter.IsVirtual = true;
                getter.IsNewSlot = true;
                var start = method.Body.Instructions[0];
                var calls = method.Body.GetILProcessor();
                calls.InsertAfter(start, calls.Create(OpCodes.Ldarg_0));
                calls.InsertAfter(start, calls.Create(OpCodes.Pop));
                calls.InsertAfter(start, calls.Create(OpCodes.Callvirt, getter));
                break;
            case "receiverAddress":
                var body = getter.Body.GetILProcessor();
                body.InsertBefore(getter.Body.Instructions[0], body.Create(OpCodes.Pop));
                body.InsertBefore(getter.Body.Instructions[0],
                    body.Create(OpCodes.Ldarga_S, getter.Body.ThisParameter));
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
            "reference" => "Unsupported reference-typed field: System.String Examples.Account::Owner\n" +
                "  Only fields holding instances of admitted classes are modelled; System.String is not one.",
            "fieldType" => "Unsupported class instance field type: System.Double Examples.Account::Rate",
            "virtual" => "Unsupported virtual instance method\n  Dispatch on class instances",
            "virtualCall" => "Unsupported virtual call: System.UInt64 Examples.Account::get_Headroom()",
            "receiverAddress" =>
                "Unsupported address of a class instance receiver: System.UInt64 Examples.Account::get_Headroom()",
            _ => throw new InvalidOperationException("Unknown class rejection fixture: " + mutation)
        };
        module.Write(dll);
    }
    var selector = mutation switch
    {
        "interface" => "Objects::IsNull(Examples.ICounterValue)",
        "byref" => "Objects::IsNull(Examples.Account&)",
        "virtual" or "receiverAddress" => "Account::get_Headroom()",
        _ => "Objects::IsNull(Examples.Account)"
    };
    var result = Execute(["dotnet", ExtractorPath, "extract", dll, selector, output]);
    if (result.Code != 1 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !result.Output.Replace("\r\n", "\n").Contains(expected, StringComparison.Ordinal))
        throw new InvalidOperationException($"Incorrect class rejection: {mutation}\n{result.Output}");
    Console.WriteLine($"PASS class rejection: {mutation}");
}
Console.WriteLine("PASS objects: identity, presence, scalar and reference field, receiver, framed call " +
    "and construction proofs, " +
    "and named rejection of unmodelled class shapes, field accesses and calls");
