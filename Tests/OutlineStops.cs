#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

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

// Loop callee selection excludes narrow result types even when the helper always throws.
var throwOnly = Outline("NarrowThrowOnly", "Loops::CountUntil(uint,uint)", module =>
{
    var helper = module.GetType("Examples.Loops").Methods.Single(method => method.Name == "Bump");
    var constructor = (MethodReference)helper.Body.Instructions.Single(instruction =>
        instruction.OpCode == OpCodes.Newobj).Operand;
    helper.ReturnType = module.TypeSystem.Byte;
    helper.Body.Instructions.Clear();
    helper.Body.Variables.Clear();
    helper.Body.Instructions.Add(Instruction.Create(OpCodes.Newobj, constructor));
    helper.Body.Instructions.Add(Instruction.Create(OpCodes.Throw));
});
if (throwOnly.Code == 0 || !throwOnly.Output.Contains("callee Bump returns System.Byte", StringComparison.Ordinal))
    throw new InvalidOperationException("A narrow throw-only helper bypassed callee result selection:\n" +
        throwOnly.Output + throwOnly.Proof);
Console.WriteLine("PASS narrow throw-only helper retains its callee selection diagnostic");
foreach (var (owner, methodName, selector) in new[]
{
    ("Arithmetic", "Larger", "Arithmetic::Larger(int,int)"),
    ("PrimitiveArrays", "ReadInt32", "PrimitiveArrays::ReadInt32(int[],int)"),
    ("Loops", "Put", "Loops::Put(System.Span`1<System.UInt32>,uint)"),
    ("Counter", "Read", "Counter::Read()"),
    ("OutlineCountdown", "Drain", "OutlineCountdown::Drain()")
})
{
    var positive = Outline("WideReturn" + owner, selector, _ => { });
    if (positive.Code != 0 || positive.Proof.Contains("-- not outlined:", StringComparison.Ordinal))
        throw new InvalidOperationException("Wide return control failed: " + selector + "\n" + positive.Output);
    var narrow = Outline("NarrowReturn" + owner, selector, module =>
    {
        var method = module.GetType("Examples." + owner).Methods.Single(method => method.Name == methodName);
        if (method.ReturnType.MetadataType == MetadataType.Void)
        {
            var processor = method.Body.GetILProcessor();
            foreach (var returned in method.Body.Instructions.Where(instruction =>
                instruction.OpCode == OpCodes.Ret).ToArray())
            {
                returned.OpCode = OpCodes.Ldc_I4_0;
                processor.InsertAfter(returned, Instruction.Create(OpCodes.Ret));
            }
        }
        method.ReturnType = module.TypeSystem.Byte;
    });
    if (narrow.Code == 0 && !narrow.Proof.Contains("-- not outlined:", StringComparison.Ordinal))
        throw new InvalidOperationException("Narrow return was outlined: " + selector + "\n" + narrow.Proof);
    Console.WriteLine("PASS declared narrow return outline rejection and wide control: " + owner);
}
if (args is ["--return-only"]) return;

// A parameter of a narrow declared type is loaded narrowed by its step, which no outline reader models, so each
// reader refuses it and names it; the method before the retyping is the wide control.
var unnamed = new List<string>();
foreach (var (owner, methodName, parameter, selector, narrowSelector, prepare) in
    new (string, string, int, string, string, Action<MethodDefinition>?)[]
{
    ("Arithmetic", "Larger", 0, "Arithmetic::Larger(int,int)", "Arithmetic::Larger(ushort,int)", null),
    ("PrimitiveArrays", "ReadInt32", 1, "PrimitiveArrays::ReadInt32(int[],int)",
        "PrimitiveArrays::ReadInt32(int[],ushort)", null),
    ("Loops", "Put", 1, "Loops::Put(System.Span`1<System.UInt32>,uint)",
        "Loops::Put(System.Span`1<System.UInt32>,ushort)", null),
    ("Loops", "CountUntil", 1, "Loops::CountUntil(uint,uint)", "Loops::CountUntil(uint,ushort)", null),
    ("Objects", "SetLimit", 1, "Objects::SetLimit(Examples.Account,uint)",
        "Objects::SetLimit(Examples.Account,ushort)", null),
    ("NarrowTotals", "WriteRead", 0, "NarrowTotals::WriteRead(uint)", "NarrowTotals::WriteRead(ushort)", null),
    ("OutlineCountdown", "Drain", 0, "OutlineCountdown::Drain(ulong)", "OutlineCountdown::Drain(ushort)",
        CountBy)
})
{
    MethodDefinition Target(ModuleDefinition module)
    {
        var method = module.GetType("Examples." + owner).Methods.Single(method => method.Name == methodName);
        prepare?.Invoke(method);
        return method;
    }
    var wide = Outline("WideArgument" + owner + methodName, selector, module => Target(module));
    if (wide.Code != 0 || wide.Proof.Contains("-- not outlined:", StringComparison.Ordinal))
        throw new InvalidOperationException("Wide argument control failed: " + selector + "\n" + wide.Output);
    var name = "";
    var narrow = Outline("NarrowArgument" + owner + methodName, narrowSelector, module =>
    {
        var retyped = Target(module).Parameters[parameter];
        retyped.ParameterType = module.TypeSystem.UInt16;
        name = retyped.Name;
    });
    var refused = narrow.Code != 0 || narrow.Proof.Contains("-- not outlined:", StringComparison.Ordinal);
    if (!refused || !(narrow.Output + narrow.Proof).Contains($"`{name}`", StringComparison.Ordinal))
        unnamed.Add(
            $"Narrow argument `{name}` was outlined or not named: {narrowSelector}\n{narrow.Output}{narrow.Proof}");
    else Console.WriteLine($"PASS declared narrow argument outline rejection and wide control: {owner}::{methodName}");
}
if (unnamed.Count > 0) throw new InvalidOperationException(string.Join("\n", unnamed));

// The receiver loop adds its one word argument to the count instead of one, so the loop body reads an argument.
static void CountBy(MethodDefinition drain)
{
    drain.Parameters.Add(new ParameterDefinition("step", Mono.Cecil.ParameterAttributes.None,
        drain.Module.TypeSystem.UInt64));
    var one = drain.Body.Instructions.Where(instruction => instruction.OpCode == OpCodes.Ldc_I4_1).ElementAt(1);
    one.OpCode = OpCodes.Ldarg_1;
    one.Next.OpCode = OpCodes.Conv_U8;
}

// A conditional branch with mixed native/int32 operands, in a method over a class instance, is a hole that names
// the mixed-width branch.
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
    !wrapped.Proof.Contains(".blt", StringComparison.Ordinal))
    throw new Exception("A mixed native branch did not leave a hole naming it in the object outline:\n" +
        wrapped.Output + wrapped.Proof);
Console.WriteLine("PASS a mixed native and int32 branch is a hole that names it in the object outline");

// Mixed tests retain explicit diagnostics at both a loop latch and an internal branch.
foreach (var atLatch in new[] { true, false })
{
    var mixed = Outline(atLatch ? "MixedLatch" : "MixedInternal",
        "System.Int32 Examples.NativeIntegers::MixedLoop(System.Int32)", module =>
    {
        var method = Added(module, "MixedLoop", module.TypeSystem.Int32, module.TypeSystem.Int32);
        method.Body.Variables.Add(new VariableDefinition(module.TypeSystem.Int32));
        var code = method.Body.Instructions;
        var head = Instruction.Create(OpCodes.Ldc_I4_0);
        var increment = Instruction.Create(OpCodes.Ldloc_0);
        code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
        code.Add(Instruction.Create(OpCodes.Stloc_0));
        code.Add(head);
        code.Add(Instruction.Create(OpCodes.Conv_I));
        code.Add(Instruction.Create(OpCodes.Ldarg_0));
        if (atLatch)
        {
            code.Add(Instruction.Create(OpCodes.Blt, head));
        }
        else
        {
            code.Add(Instruction.Create(OpCodes.Beq, increment));
            code.Add(Instruction.Create(OpCodes.Nop));
            code.Add(increment);
            code.Add(Instruction.Create(OpCodes.Ldc_I4_1));
            code.Add(Instruction.Create(OpCodes.Add));
            code.Add(Instruction.Create(OpCodes.Stloc_0));
            code.Add(Instruction.Create(OpCodes.Ldloc_0));
            code.Add(Instruction.Create(OpCodes.Ldarg_0));
            code.Add(Instruction.Create(OpCodes.Blt, head));
        }
        code.Add(Instruction.Create(OpCodes.Ldloc_0));
        code.Add(Instruction.Create(OpCodes.Ret));
    });
    if (atLatch ? mixed.Code == 0 || !mixed.Output.Contains("at its back edge", StringComparison.Ordinal)
        : mixed.Code != 0 || !mixed.Proof.Contains("not outlined:", StringComparison.Ordinal))
        throw new Exception("Mixed test lacks an outline diagnostic:\n" + mixed.Output + mixed.Proof);
    if (!(mixed.Output + mixed.Proof).Contains("operands of different widths", StringComparison.Ordinal))
        throw new Exception("Mixed test stopped before inspecting its operands:\n" + mixed.Output + mixed.Proof);
    Console.WriteLine("PASS mixed-width outline diagnostic: " + (atLatch ? "latch" : "internal branch"));
}

// The element a span read loads must be as wide as the span's elements.
var read = Outline("WrongWidth",
    "System.Boolean Examples.Loops::AllZero(System.ReadOnlySpan`1<System.UInt32>)", module =>
{
    var method = module.GetType("Examples.Loops").Methods.Single(candidate => candidate.Name == "AllZero");
    var load = method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Ldind_U4);
    load.OpCode = OpCodes.Ldind_I8;
});
if (read.Code != 0 || !read.Proof.Contains("not outlined: `.ldind .i8`", StringComparison.Ordinal))
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
if (straight.Code != 0 || !straight.Proof.Contains("not outlined: `.stloc 0` at IL_0001", StringComparison.Ordinal))
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
