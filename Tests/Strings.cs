#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using Mono.Cecil;
using Mono.Cecil.Cil;

// Strings as opaque object references: proofs that they are passed, returned, stored and loaded as literals, and the
// named rejection of every operation that would read through one, address its root or load an unencodable literal.
using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Strings");
Directory.CreateDirectory(root);

foreach (var (proof, entry) in new[]
{
    ("StringValues", "Strings::Pick(System.Boolean,System.String,System.String)"),
    ("StringLabel", "Strings::Relabel(Examples.Labelled,System.String)"),
    ("StringLiterals", "Strings::SameText()"),
    ("StringDefault", "Strings::OrNone(System.String)")
})
{
    verification.Verify(assembly, "Examples", entry, At($"Examples/Proofs/{proof}.lean"), Path.Combine(root, proof));
    Console.WriteLine($"PASS {proof}: {entry}");
}

foreach (var mutation in new[] { "read", "surrogate", "argumentAddress", "localAddress", "byref", "modified" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string expected, selector = "Strings::Pick(System.Boolean,System.String,System.String)";
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Strings").Methods.Single(candidate => candidate.Name == "Pick");
        var il = method.Body.GetILProcessor();
        var start = method.Body.Instructions[0];
        var text = module.TypeSystem.String;
        switch (mutation)
        {
            case "read":
                var empty = new MethodReference("IsNullOrEmpty", module.TypeSystem.Boolean, text);
                empty.Parameters.Add(new ParameterDefinition(text));
                il.InsertBefore(start, il.Create(OpCodes.Ldarg_1));
                il.InsertBefore(start, il.Create(OpCodes.Call, empty));
                il.InsertBefore(start, il.Create(OpCodes.Pop));
                expected = "Rejected external call: System.Boolean System.String::IsNullOrEmpty(System.String)";
                break;
            case "surrogate":
                il.InsertBefore(start, il.Create(OpCodes.Ldstr, "\uD800"));
                il.InsertBefore(start, il.Create(OpCodes.Pop));
                expected = "Unsupported string literal: a surrogate, backspace or form feed";
                break;
            case "argumentAddress":
                il.InsertBefore(start, il.Create(OpCodes.Ldarga_S, method.Parameters[1]));
                il.InsertBefore(start, il.Create(OpCodes.Pop));
                expected = "Unsupported address of a class instance argument: " + method.FullName;
                break;
            case "localAddress":
                il.InsertBefore(start, il.Create(OpCodes.Ldloca_S, method.Body.Variables[0]));
                il.InsertBefore(start, il.Create(OpCodes.Pop));
                expected = "Unsupported address of a class instance local: " + method.FullName;
                break;
            case "byref":
                method.Parameters[1].ParameterType = new ByReferenceType(text);
                selector = "Strings::Pick(System.Boolean,System.String&,System.String)";
                expected = "Unsupported by-reference class instance: System.String&";
                break;
            case "modified":
                method.Parameters[1].ParameterType = new OptionalModifierType(module.TypeSystem.Object, text);
                selector = "Strings::Pick(System.Boolean,System.String modopt(System.Object),System.String)";
                expected = "Custom modifiers are unsupported in method signatures";
                break;
            default: throw new InvalidOperationException("Unknown string rejection fixture: " + mutation);
        }
        module.Write(dll);
    }
    var result = Execute(["dotnet", ExtractorPath, "extract", dll, selector, output]);
    if (result.Code != 1 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !result.Output.Replace("\r\n", "\n").Contains(expected, StringComparison.Ordinal))
        throw new InvalidOperationException($"Incorrect string rejection: {mutation}\n{result.Output}");
    Console.WriteLine($"PASS string rejection: {mutation}");
}
Console.WriteLine("PASS strings: passed, returned, stored and loaded as literals; reads and addresses rejected by name");
