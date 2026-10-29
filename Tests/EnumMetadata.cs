#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using Mono.Cecil;

var extractor = Assembly.LoadFrom(ExtractorPath);
const BindingFlags flags = BindingFlags.Static | BindingFlags.NonPublic;
var enumTypes = extractor.GetType("Nethermind.LeanCIL.EnumTypes", true)!;
var begin = enumTypes.GetMethod("BeginScope", flags)!;
var arrays = extractor.GetType("Nethermind.LeanCIL.Arrays", true)!;
var descriptor = arrays.GetMethod("Storage", flags)!;
var runtime = extractor.GetType("Nethermind.LeanCIL.RuntimeModels", true)!;
var span = runtime.GetMethod("ElementSpan", flags)!;
var spanOperations = runtime.GetMethod("BuildSpanOperations", flags)!;
using var module = ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll"));
var owner = module.GetType("Examples.EnumBuffers");
var element = owner.NestedTypes.Single(type => type.Name == "Small");
var field = element.Fields.Single(field => !field.IsStatic);
var getter = (MethodReference)owner.Methods.Single(method => method.Name == "Read")
    .Body.Instructions.Single(instruction => instruction.Operand is MethodReference { Name: "get_Item" }).Operand;

IDisposable Scope() => (IDisposable)begin.Invoke(null, null)!;
object Describe() => descriptor.Invoke(null, [element, null])!;
string Span() => (string)span.Invoke(null, [getter, "scalar"])!;
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
    if (Width(original) != 1 || Span() != ".memory (.spanItem 1)")
        throw new InvalidOperationException("Wrong initial enum storage");

    var aggregate = module.GetType("Examples.AggregateArrays").NestedTypes.Single(type => type.Name == "Pair");
    var vector = ((ArrayType)module.GetType("Examples.AggregateArrays").Methods
        .Single(method => method.Name == "ReadVector").Parameters[0].ParameterType).ElementType;
    foreach (var (type, admitted) in new[]
        { (module.TypeSystem.Int32, true), ((TypeReference)element, true), (aggregate, false), (vector, false) })
    {
        var operations = (Dictionary<string, string>)spanOperations.Invoke(null, [type, "scalar"])!;
        var createsStaticSpan = operations.Keys.Any(name =>
            name.Contains("System.Runtime.CompilerServices.RuntimeHelpers::CreateSpan<", StringComparison.Ordinal));
        if (createsStaticSpan != admitted ||
            !operations.Values.Any(operation => operation.StartsWith(".memory (.arraySpan ", StringComparison.Ordinal)))
            throw new InvalidOperationException("Static and supplied array span admission were conflated: " + type.FullName);
    }
}
field.FieldType = module.TypeSystem.Int32;
using (Scope())
{
    var changed = Describe();
    if (ReferenceEquals(original, changed) || Width(changed) != 4 || Span() != ".memory (.spanItem 4)")
        throw new InvalidOperationException("New request reused an old enum width or span signature table");
}
field.FieldType = module.TypeSystem.Boolean;
Reject("an invalid underlying type");
field.FieldType = module.TypeSystem.SByte;
owner.NestedTypes.Add(new TypeDefinition("", "Small", Mono.Cecil.TypeAttributes.NestedPublic));
Reject("a duplicate type identity");
Console.WriteLine("PASS enum metadata reuse and request-boundary freshness");
