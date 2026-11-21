#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PinnedMetadata.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

var extractor = Assembly.LoadFrom(ExtractorPath);
const BindingFlags flags = BindingFlags.Static | BindingFlags.NonPublic;
var enumTypes = extractor.GetType("Nethermind.LeanCIL.EnumTypes", true)!;
var begin = enumTypes.GetMethod("BeginScope", flags)!;
var arrays = extractor.GetType("Nethermind.LeanCIL.Arrays", true)!;
var descriptor = arrays.GetMethod("Storage", flags)!;
var runtime = extractor.GetType("Nethermind.LeanCIL.RuntimeModels", true)!;
var spans = extractor.GetType("Nethermind.LeanCIL.Spans", true)!;
var memberWidth = spans.GetMethod("MemberWidth", flags)!;
var arrayView = spans.GetMethod("ArrayView", flags)!;
var staticSpan = runtime.GetMethod("StaticSpanModel", flags)!;
using var pinned = new PinnedMetadata(extractor, At("Examples/Assembly/bin/Examples.dll"));
var module = pinned.Module;
var owner = module.GetType("Examples.EnumBuffers");
var element = owner.NestedTypes.Single(type => type.Name == "Small");
var field = element.Fields.Single(field => !field.IsStatic);
var getter = owner.Methods.Single(method => method.Name == "Read")
    .Body.Instructions.Single(instruction => instruction.Operand is MethodReference { Name: "get_Item" });

IDisposable Scope() => (IDisposable)begin.Invoke(null, null)!;
object Describe() => descriptor.Invoke(null, [element, null])!;
int ItemWidth() => (int?)memberWidth.Invoke(null, [getter, "get_Item", 1, "scalar"])
    ?? throw new InvalidOperationException("Missing span item at the getter call");
int Width(object value) => (int)value.GetType().GetProperty("Width")!.GetValue(value)!;
void Reject(string reason)
{
    using var scope = Scope();
    try { Describe(); }
    catch (TargetInvocationException error) when (error.InnerException is InvalidDataException)
    {
        Console.WriteLine("PASS enum cache revalidates " + reason);
        return;
    }
    throw new InvalidOperationException("Enum cache retained stale metadata: " + reason);
}

object original;
using (Scope())
{
    original = Describe();
    for (var index = 0; index < 1000; index++)
        if (!ReferenceEquals(original, Describe()))
            throw new InvalidOperationException("Enum descriptor was not reused within a request");
    if (Width(original) != 1 || ItemWidth() != 1)
        throw new InvalidOperationException("Wrong initial enum storage");

    var aggregate = module.GetType("Examples.AggregateArrays").NestedTypes.Single(type => type.Name == "Pair");
    var vector = ((ArrayType)module.GetType("Examples.AggregateArrays").Methods
        .Single(method => method.Name == "ReadVector").Parameters[0].ParameterType).ElementType;
    var words = module.GetType("Examples.SpanTables").Methods.Single(method => method.Name == "get_Words");
    var create = (GenericInstanceMethod)words.Body.Instructions.Single(instruction =>
        instruction.Operand is GenericInstanceMethod).Operand;
    var arrayMethod = module.GetType("Examples.MemorySpans").Methods
        .Single(method => method.Name == "ArrayConstructor");
    var arrayConstructor = arrayMethod.Body.Instructions.Select(instruction => instruction.Operand)
        .OfType<MethodReference>().Single(reference => reference.Name == ".ctor");
    foreach (var (type, admitted) in new[]
        { (module.TypeSystem.Int32, true), ((TypeReference)element, true), (aggregate, false), (vector, false) })
    {
        var spanOwner = new GenericInstanceType(((GenericInstanceType)arrayConstructor.DeclaringType).ElementType);
        spanOwner.GenericArguments.Add(type);
        var arrayCall = new MethodReference(".ctor", module.TypeSystem.Void, spanOwner) { HasThis = true };
        arrayCall.Parameters.Add(new ParameterDefinition(arrayConstructor.Parameters[0].ParameterType));
        var call = new GenericInstanceMethod(create.ElementMethod);
        call.GenericArguments.Add(type);
        var createsStaticSpan = staticSpan.Invoke(null, [call, "scalar"]) is not null;
        var createsArraySpan = arrayView.Invoke(null, [Instruction.Create(OpCodes.Newobj, arrayCall), "scalar", true]) is not null;
        if (createsStaticSpan != admitted || !createsArraySpan)
            throw new InvalidOperationException("Static and supplied array span admission were conflated: " + type.FullName);
    }
}
field.FieldType = module.TypeSystem.Int32;
using (Scope())
{
    var changed = Describe();
    if (ReferenceEquals(original, changed) || Width(changed) != 4 || ItemWidth() != 4)
        throw new InvalidOperationException("New request reused an old enum width or span signature table");
}
field.FieldType = module.TypeSystem.Boolean;
Reject("an invalid underlying type");
field.FieldType = module.TypeSystem.SByte;
owner.NestedTypes.Add(new TypeDefinition("", "Small", Mono.Cecil.TypeAttributes.NestedPublic));
Reject("a duplicate type identity");
Console.WriteLine("PASS enum metadata reuse and request-boundary freshness");
