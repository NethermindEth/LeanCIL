#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using Mono.Cecil;
using Mono.Cecil.Cil;
using MethodAttributes = Mono.Cecil.MethodAttributes;

// Each case edits a method of the examples so that its outline must stop, and checks the stop names the
// instruction it stopped at instead of failing the generator or outlining a value it does not model.
var source = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/OutlineStops");
Directory.CreateDirectory(root);

(int Code, string Output, string Proof) Outline(string name, string selector, Action<ModuleDefinition> edit)
{
    var directory = Path.Combine(root, name);
    Directory.CreateDirectory(directory);
    var dll = Path.Combine(directory, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(source))
    {
        edit(module);
        module.Write(dll);
    }
    var extraction = Path.Combine(directory, "Extraction");
    Run(["dotnet", ExtractorPath, "extract", dll, selector, extraction]);
    var proof = Path.Combine(directory, "Proof.lean");
    File.Delete(proof);
    var outline = Execute(["dotnet", ExtractorPath, "new-proof", extraction, proof]);
    return (outline.Code, outline.Output, File.Exists(proof) ? File.ReadAllText(proof) : "");
}

MethodDefinition Added(ModuleDefinition module, string name, TypeReference result, params TypeReference[] parameters)
{
    var method = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, result);
    foreach (var parameter in parameters) method.Parameters.Add(new ParameterDefinition(parameter));
    module.GetType("Examples.NativeIntegers").Methods.Add(method);
    return method;
}

// A conditional branch the native-width analysis wraps, in a method over a class instance, is a hole that names
// the wrapped branch.
var wrapped = Outline("WrappedObject",
    "System.UInt64 Examples.NativeIntegers::Wrapped(Examples.Account,System.Int32[])", module =>
    {
        var account = module.GetType("Examples.Account");
        var method = Added(module, "Wrapped", module.TypeSystem.UInt64, account,
            new ArrayType(module.TypeSystem.Int32));
        var code = method.Body.Instructions;
        var zero = Instruction.Create(OpCodes.Ldc_I4_0);
        code.Add(Instruction.Create(OpCodes.Ldarg_1));
        code.Add(Instruction.Create(OpCodes.Ldlen));
        code.Add(Instruction.Create(OpCodes.Ldc_I4_5));
        code.Add(Instruction.Create(OpCodes.Blt, zero));
        code.Add(Instruction.Create(OpCodes.Ldarg_0));
        code.Add(Instruction.Create(OpCodes.Ldfld, account.Fields.Single(field => field.Name == "Balance")));
        code.Add(Instruction.Create(OpCodes.Ret));
        code.Add(zero);
        code.Add(Instruction.Create(OpCodes.Conv_U8));
        code.Add(Instruction.Create(OpCodes.Ret));
    });
if (wrapped.Code != 0 || !wrapped.Proof.Contains("not outlined: ", StringComparison.Ordinal) ||
    !wrapped.Proof.Contains(".nativeBinary (.blt", StringComparison.Ordinal))
    throw new Exception("A wrapped native branch did not leave a hole naming it in the object outline:\n" +
        wrapped.Output + wrapped.Proof);
Console.WriteLine("PASS a wrapped native and int32 branch is a hole that names it in the object outline");

// A loop whose back edge the analysis wraps is refused with a message that names the back edge.
var latch = Outline("WrappedLatch", "System.UInt32 Examples.NativeIntegers::WrappedLatch(System.UInt32)",
    module =>
{
    var method = Added(module, "WrappedLatch", module.TypeSystem.UInt32, module.TypeSystem.UInt32);
    method.Body.Variables.Add(new VariableDefinition(module.TypeSystem.Int32));
    var code = method.Body.Instructions;
    var head = Instruction.Create(OpCodes.Ldloc_0);
    code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
    code.Add(Instruction.Create(OpCodes.Stloc_0));
    code.Add(head);
    code.Add(Instruction.Create(OpCodes.Ldc_I4_1));
    code.Add(Instruction.Create(OpCodes.Add));
    code.Add(Instruction.Create(OpCodes.Stloc_0));
    code.Add(Instruction.Create(OpCodes.Ldloc_0));
    code.Add(Instruction.Create(OpCodes.Conv_U));
    code.Add(Instruction.Create(OpCodes.Ldarg_0));
    code.Add(Instruction.Create(OpCodes.Blt, head));
    code.Add(Instruction.Create(OpCodes.Ldloc_0));
    code.Add(Instruction.Create(OpCodes.Ret));
});
if (latch.Code == 0 || !latch.Output.Contains("its loop at IL_0009 tests a native and an int32 value at its back edge",
        StringComparison.Ordinal))
    throw new Exception("A wrapped back edge was not refused by name in the loop outline:\n" + latch.Output);
Console.WriteLine("PASS a wrapped back edge is refused by name in the loop outline");

// The element a span read loads must be as wide as the span's elements.
var read = Outline("WrongWidth",
    "System.Boolean Examples.Loops::AllZero(System.ReadOnlySpan`1<System.UInt32>)", module =>
{
    var method = module.GetType("Examples.Loops").Methods.Single(candidate => candidate.Name == "AllZero");
    var load = method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Ldind_U4);
    load.OpCode = OpCodes.Ldind_I8;
});
if (read.Code != 0 || !read.Proof.Contains("not outlined: `.load64`", StringComparison.Ordinal))
    throw new Exception("A read wider than the span's elements was outlined as a read of its element:\n" +
        read.Output + read.Proof);
Console.WriteLine("PASS a span read of another width than its elements is a hole");

// A local of a narrow integer type stays the author's in every outline family, which reads it from the local's
// type: the straight-line outline does not step its store, the loop outline refuses its kind and the object
// outline refuses a numeric frame that holds it.
MethodDefinition NarrowLocal(ModuleDefinition module, string name, TypeReference parameter)
{
    var method = Added(module, name, module.TypeSystem.Int32, parameter);
    method.Body.Variables.Add(new VariableDefinition(module.TypeSystem.Byte));
    method.Body.InitLocals = true;
    return method;
}

var straight = Outline("NarrowStraight", "System.Int32 Examples.NativeIntegers::NarrowStraight(System.Int32)",
    module =>
{
    var code = NarrowLocal(module, "NarrowStraight", module.TypeSystem.Int32).Body.Instructions;
    code.Add(Instruction.Create(OpCodes.Ldarg_0));
    code.Add(Instruction.Create(OpCodes.Stloc_0));
    code.Add(Instruction.Create(OpCodes.Ldloc_0));
    code.Add(Instruction.Create(OpCodes.Ret));
});
if (straight.Code != 0 || !straight.Proof.Contains("not outlined: `.setLocal 0` at IL_0001", StringComparison.Ordinal))
    throw new Exception("A store to a byte local was stepped by the straight-line outline:\n" +
        straight.Output + straight.Proof);
Console.WriteLine("PASS a store to a byte local is a hole in the straight-line outline");

var looped = Outline("NarrowLoop", "System.Int32 Examples.NativeIntegers::NarrowLoop(System.Int32)", module =>
{
    var code = NarrowLocal(module, "NarrowLoop", module.TypeSystem.Int32).Body.Instructions;
    var head = Instruction.Create(OpCodes.Ldloc_0);
    code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
    code.Add(Instruction.Create(OpCodes.Stloc_0));
    code.Add(head);
    code.Add(Instruction.Create(OpCodes.Ldc_I4_1));
    code.Add(Instruction.Create(OpCodes.Add));
    code.Add(Instruction.Create(OpCodes.Stloc_0));
    code.Add(Instruction.Create(OpCodes.Ldloc_0));
    code.Add(Instruction.Create(OpCodes.Ldarg_0));
    code.Add(Instruction.Create(OpCodes.Blt, head));
    code.Add(Instruction.Create(OpCodes.Ldloc_0));
    code.Add(Instruction.Create(OpCodes.Ret));
});
if (looped.Code == 0 ||
    !looped.Output.Contains("local `local0` has kind .narrow .unsigned8", StringComparison.Ordinal))
    throw new Exception("A loop over a byte local was not refused by its kind:\n" + looped.Output);
Console.WriteLine("PASS a loop over a byte local is refused by its kind in the loop outline");

var framed = Outline("NarrowObject", "System.Int32 Examples.NativeIntegers::NarrowObject(Examples.Account)", module =>
{
    var account = module.GetType("Examples.Account");
    var code = NarrowLocal(module, "NarrowObject", account).Body.Instructions;
    code.Add(Instruction.Create(OpCodes.Ldarg_0));
    code.Add(Instruction.Create(OpCodes.Ldfld, account.Fields.Single(field => field.Name == "Balance")));
    code.Add(Instruction.Create(OpCodes.Conv_U1));
    code.Add(Instruction.Create(OpCodes.Stloc_0));
    code.Add(Instruction.Create(OpCodes.Ldloc_0));
    code.Add(Instruction.Create(OpCodes.Ret));
});
if (framed.Code != 0 ||
    !framed.Proof.Contains("a class frame with mixed numeric homes and unsupported local", StringComparison.Ordinal))
    throw new Exception("A byte local beside an object argument was stepped by the object outline:\n" +
        framed.Output + framed.Proof);
Console.WriteLine("PASS a byte local in a method over an object is a hole in the object outline");
