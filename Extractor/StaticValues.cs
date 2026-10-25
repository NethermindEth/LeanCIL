using System.Collections.Concurrent;
using System.Globalization;
using System.Runtime.CompilerServices;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Readonly fields have one unconditional store, from a literal or M(constants).
// Lean rechecks stored bytes; recognizing the constructor store remains trusted.
internal static class StaticValues
{
    internal sealed record Value(FieldDefinition Field, MethodDefinition? Initializer, string[] Arguments,
        byte[] Bytes, string? Literal = null);

    internal static string Scalar(FieldDefinition field) => MetadataValidation.IsAggregate(field.FieldType, field.Module)
        ? "none" : "some " + (EnumTypes.Storage(field.FieldType).FullName is "System.SByte" or "System.Int16"
            ? "true" : "false");

    static int Width(FieldDefinition field, string architecture) =>
        MetadataValidation.IsAggregate(field.FieldType, field.Module)
            ? MetadataValidation.Layout(field.FieldType, field.Module, architecture)
            : MetadataValidation.PrimitiveWidth(field.FieldType);

    static string LeanWord(Word word) => word.Width == 8
        ? $".i64 {word.Bits.ToString(CultureInfo.InvariantCulture)}"
        : $".i32 {word.Bits.ToString(CultureInfo.InvariantCulture)}";

    static byte[] Bytes(Slot? value, FieldDefinition field, string architecture)
    {
        var width = Width(field, architecture);
        if (MetadataValidation.IsAggregate(field.FieldType, field.Module))
        {
            if (value is Snapshot snapshot && snapshot.Data.Length == width) return snapshot.Data;
        }
        else if (value is Word word && word.Width == (width == 8 ? 8 : 4))
            return Enumerable.Range(0, width).Select(index => (byte)(word.Bits >> (8 * index))).ToArray();
        throw Unsupported(field, "Its initializer does not return a complete value of the field's storage type.");
    }

    abstract record Slot;
    sealed record Word(int Width, ulong Bits) : Slot;
    sealed record Snapshot(byte[] Data) : Slot;
    sealed record Self(byte[] Data) : Slot;

    static readonly ConditionalWeakTable<FieldDefinition, ConcurrentDictionary<string, Value>> cache = new();

    static InvalidDataException Unsupported(FieldReference field, string reason) =>
        new($"Unsupported static initializer: {field.FullName}\n  {reason}");

    static FieldDefinition? Stored(Instruction i, Code code) =>
        i.OpCode.Code == code && i.Operand is FieldReference f ? f.Resolve() : null;

    static bool Constant(Instruction i) => i.OpCode.Code is Code.Ldc_I4 or Code.Ldc_I4_S or Code.Ldc_I4_M1 or Code.Ldc_I8 ||
        i.OpCode.Code is >= Code.Ldc_I4_0 and <= Code.Ldc_I4_8;

    static bool Conversion(Instruction i) => i.OpCode.Code is Code.Conv_I8 or Code.Conv_U8 or Code.Conv_I4 or Code.Conv_U4 or Code.Conv_I or Code.Conv_U;

    // The loaded field itself; its declaring type's initialization is checked by the caller.
    internal static FieldDefinition Field(FieldReference reference, ModuleDefinition module, string architecture = "scalar")
    {
        FieldDefinition? field = reference.Resolve();
        if (field is null || reference.DeclaringType.Scope != module || reference.DeclaringType is TypeSpecification ||
            field.Module != module || reference.FullName != field.FullName || !field.IsStatic || !field.IsInitOnly ||
            (field.Attributes & FieldAttributes.HasFieldRVA) != 0 ||
            field.DeclaringType.HasGenericParameters)
            throw new InvalidDataException($"Unsupported static field load: {reference.FullName}\n  Only same-assembly static readonly integer, enum or reference-free struct fields are loaded.");
        RuntimeModels.ValidateTypeIdentity(field.FieldType, module, architecture);
        _ = Width(field, architecture);
        return field;
    }

    internal static Value Resolve(FieldReference reference, ModuleDefinition module, string architecture = "scalar")
    {
        FieldDefinition field = Field(reference, module, architecture);
        ConcurrentDictionary<string, Value> values = cache.GetValue(field, _ => new());
        return values.GetOrAdd(architecture, static (selected, context) => Compute(context.Field, context.Module, selected),
            (Field: field, Module: module));
    }

    static Value Compute(FieldDefinition field, ModuleDefinition module, string architecture)
    {
        var constructor = field.DeclaringType.Methods.SingleOrDefault(m => m.IsConstructor && m.IsStatic && m.HasBody) ??
            throw Unsupported(field, "No static constructor stores its value.");
        if (constructor.Body.ExceptionHandlers.Count != 0)
            throw Unsupported(field, "The static constructor has exception handlers.");
        var code = constructor.Body.Instructions;
        var stores = code.Select((i, index) => (i, index)).Where(s => Stored(s.i, Code.Stsfld) == field).Select(s => s.index).ToArray();
        if (stores.Length != 1)
            throw Unsupported(field, $"The static constructor stores it {stores.Length} times; exactly one store is admitted.");
        var store = stores[0];
        // `jmp` has call flow but never returns, so only returning calls may precede the store.
        if (code.Take(store).Any(i => i.OpCode.FlowControl is not (FlowControl.Next or FlowControl.Call or FlowControl.Meta) || i.OpCode.Code == Code.Jmp))
            throw Unsupported(field, "Control flow precedes its store, so the store is not unconditional.");
        foreach (var branch in code.Where(i => i.Operand is Instruction or Instruction[]))
            if ((branch.Operand is Instruction target ? new[] { target } : (Instruction[])branch.Operand).Any(t => code.IndexOf(t) <= store))
                throw Unsupported(field, $"A branch re-enters the code before its store: {branch}");
        foreach (var method in module.GetTypes().SelectMany(t => t.Methods).Where(m => m.HasBody && m != constructor))
            if (method.Body.Instructions.Any(i => Stored(i, Code.Stsfld) == field))
                throw Unsupported(field, $"It is also stored outside its static constructor, in {method.FullName}.");
        foreach (var method in Closure(constructor, module))
            if (method.Body.Instructions.Any(i => Stored(i, Code.Ldsflda) == field))
                throw Unsupported(field, $"Its address is taken during initialization, in {method.FullName}.");

        if (store > 0 && Stored(code[store - 1], Code.Ldsfld) is { } source && source != field)
        {
            if (source.DeclaringType != field.DeclaringType || source.FieldType.FullName != field.FieldType.FullName ||
                !code.Take(store - 1).Any(i => Stored(i, Code.Stsfld) == source))
                throw Unsupported(field, $"It copies {source.FullName}, which is not stored earlier in the same static constructor.");
            return Resolve(source, module, architecture) with { Field = field };
        }
        if (store > 0 && !MetadataValidation.IsAggregate(field.FieldType, module) &&
            (Constant(code[store - 1]) || Conversion(code[store - 1])))
        {
            var first = store - 1;
            while (first > 0 && Conversion(code[first])) first--;
            if (!Constant(code[first])) throw Unsupported(field, "Its literal initializer is not an integer constant.");
            var literalStack = new Stack<Slot>();
            for (var index = first; index < store; index++) Step(code[index], literalStack, field);
            if (literalStack.Count != 1 || literalStack.Pop() is not Word literal)
                throw Unsupported(field, "Its literal initializer has an invalid stack.");
            return new(field, null, [], Bytes(literal, field, architecture), LeanWord(literal));
        }
        if (store == 0 || code[store - 1] is not { OpCode.Code: Code.Call, Operand: MethodDefinition initializer } ||
            initializer.Module != module || !initializer.IsStatic || initializer.HasGenericParameters ||
            initializer.ReturnType.FullName != field.FieldType.FullName ||
            initializer.Parameters.Any(p => p.ParameterType.FullName is not ("System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64")))
            throw Unsupported(field, "Its value is not a same-assembly static call with integer constant arguments, or a copy of such a field.");
        var start = store - 1;
        for (var pushed = 0; pushed < initializer.Parameters.Count; )
        {
            if (--start < 0 || !(Constant(code[start]) || Conversion(code[start])))
                throw Unsupported(field, $"The arguments of {initializer.FullName} are not integer constants.");
            if (Constant(code[start])) pushed++;
        }
        var stack = new Stack<Slot>();
        for (var i = start; i < store - 1; i++) Step(code[i], stack, field);
        var arguments = stack.Reverse().ToArray();
        for (var p = 0; p < arguments.Length; p++)
            if (((Word)arguments[p]).Width != MetadataValidation.PrimitiveWidth(initializer.Parameters[p].ParameterType))
                throw Unsupported(field, $"Argument {p} of {initializer.FullName} has the wrong width.");
        foreach (var method in Closure(initializer, module))
            if (method.Body.Instructions.Any(i => i.OpCode.Code is Code.Ldsfld or Code.Ldsflda or Code.Stsfld))
                throw Unsupported(field, $"Its initializer accesses static fields, in {method.FullName}.");
        var bytes = Bytes(Run(initializer, arguments, field, module, 0, architecture), field, architecture);
        return new Value(field, initializer, arguments.Select(a => LeanWord((Word)a)).ToArray(), bytes);
    }

    // Same-assembly methods reachable by direct calls; unmodelled code beyond them is a documented assumption.
    static IEnumerable<MethodDefinition> Closure(MethodDefinition root, ModuleDefinition module)
    {
        var seen = new HashSet<MethodDefinition>();
        var pending = new Stack<MethodDefinition>([root]);
        while (pending.TryPop(out var method))
        {
            if (!seen.Add(method) || !method.HasBody) continue;
            yield return method;
            foreach (var i in method.Body.Instructions)
                if (i.Operand is MethodReference callee && callee.Resolve() is { } resolved && resolved.Module == module)
                    pending.Push(resolved);
        }
    }

    // Computes the bytes to emit; an evaluator mistake only makes the Lean certificate fail.
    static Slot? Run(MethodDefinition method, Slot[] arguments, FieldDefinition field, ModuleDefinition module, int depth, string architecture)
    {
        if (depth > 32 || !method.HasBody || method.Body.ExceptionHandlers.Count != 0)
            throw Unsupported(field, $"Its initializer cannot be evaluated: {method.FullName}");
        var stack = new Stack<Slot>();
        foreach (var i in method.Body.Instructions)
        {
            switch (i.OpCode.Code)
            {
                case Code.Ret:
                    return method.ReturnType.FullName == "System.Void" ? null : stack.Pop();
                case Code.Newobj when i.Operand is MethodReference reference && reference.Resolve() is { IsConstructor: true, HasThis: true } constructor &&
                    constructor.Module == module && MetadataValidation.IsAggregate(constructor.DeclaringType, module):
                {
                    byte[] data = new byte[MetadataValidation.Layout(constructor.DeclaringType, module, architecture)];
                    Run(constructor, [new Self(data), .. Pop(stack, constructor.Parameters.Count)], field, module, depth + 1, architecture);
                    stack.Push(new Snapshot(data));
                    break;
                }
                case Code.Call when i.Operand is MethodReference reference && reference is not GenericInstanceMethod &&
                    reference.Resolve() is { IsStatic: true } callee && callee.Module == module:
                    if (Run(callee, Pop(stack, callee.Parameters.Count), field, module, depth + 1, architecture) is { } result) stack.Push(result);
                    break;
                case Code.Stfld when i.Operand is FieldReference target && target.Resolve() is { IsStatic: false } resolved:
                {
                    var value = stack.Pop();
                    if (stack.Pop() is not Self self) throw Unsupported(field, $"Its initializer stores outside the constructed value: {i}");
                    int offset = MetadataValidation.FieldOffset(resolved.DeclaringType, resolved, module, architecture);
                    int width = MetadataValidation.FieldSize(resolved.FieldType, module, architecture);
                    for (var b = 0; b < width; b++)
                        self.Data[offset + b] = value switch
                        {
                            Word word => (byte)(b < 8 ? word.Bits >> (8 * b) : 0),
                            Snapshot snapshot when snapshot.Data.Length == width => snapshot.Data[b],
                            _ => throw Unsupported(field, $"Its initializer stores an unsupported value: {i}")
                        };
                    break;
                }
                case Code.Ldarg_0 or Code.Ldarg_1 or Code.Ldarg_2 or Code.Ldarg_3:
                    stack.Push(arguments[i.OpCode.Code - Code.Ldarg_0]);
                    break;
                case Code.Ldarg or Code.Ldarg_S:
                    stack.Push(arguments[MethodArguments.Index(method, (ParameterDefinition)i.Operand)]);
                    break;
                default:
                    Step(i, stack, field);
                    break;
            }
        }
        throw Unsupported(field, $"Its initializer does not return: {method.FullName}");
    }

    static Slot[] Pop(Stack<Slot> stack, int count)
    {
        var values = new Slot[count];
        for (var k = count - 1; k >= 0; k--) values[k] = stack.Pop();
        return values;
    }

    static void Step(Instruction i, Stack<Slot> stack, FieldDefinition field)
    {
        ulong Top() => stack.Pop() is Word word ? word.Width == 4 ? word.Bits & 0xffffffff : word.Bits
            : throw Unsupported(field, $"Its initializer converts a non-integer value: {i}");
        switch (i.OpCode.Code)
        {
            case Code.Nop: break;
            case Code.Ldc_I4_M1: stack.Push(new Word(4, 0xffffffff)); break;
            case >= Code.Ldc_I4_0 and <= Code.Ldc_I4_8: stack.Push(new Word(4, (ulong)(i.OpCode.Code - Code.Ldc_I4_0))); break;
            case Code.Ldc_I4_S: stack.Push(new Word(4, unchecked((uint)(sbyte)i.Operand))); break;
            case Code.Ldc_I4: stack.Push(new Word(4, unchecked((uint)(int)i.Operand))); break;
            case Code.Ldc_I8: stack.Push(new Word(8, unchecked((ulong)(long)i.Operand))); break;
            case Code.Conv_I8 or Code.Conv_I:
            {
                var word = (Word)stack.Peek();
                var bits = Top();
                stack.Push(new Word(8, word.Width == 4 ? unchecked((ulong)(long)(int)(uint)bits) : bits));
                break;
            }
            case Code.Conv_U8 or Code.Conv_U: stack.Push(new Word(8, Top())); break;
            case Code.Conv_I4 or Code.Conv_U4: stack.Push(new Word(4, Top() & 0xffffffff)); break;
            default: throw Unsupported(field, $"Its initializer uses an unsupported instruction: {i}");
        }
    }
}
