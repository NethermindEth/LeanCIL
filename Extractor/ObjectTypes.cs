using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Class instances the checked heap admits: a reference is an allocation identity, and the
// allocation records the runtime type that every field access is checked against.
internal static class ObjectTypes
{
    const string Unsupported = "Unsupported class instance type: ";

    /// <summary>A class declared in a pinned assembly, before checking that its shape is admitted.</summary>
    internal static bool Candidate(TypeReference type) =>
        type is not TypeSpecification and not GenericParameter && !type.IsValueType &&
        (type.Scope is ModuleDefinition || PinnedAssemblies.Active?.ModuleOf(type) is not null);

    /// <summary>
    /// A callvirt with no constrained prefix on a method of a candidate class: a call that checks its
    /// receiver for null before entering the callee.
    /// </summary>
    internal static bool ReceiverCall(Instruction call) =>
        call is { OpCode.Code: Code.Callvirt, Operand: MethodReference callee } &&
        call.Previous?.OpCode.Code != Code.Constrained && Candidate(callee.DeclaringType) &&
        callee.DeclaringType.Resolve() is { IsInterface: false };

    /// <summary>The type is an admitted class instance type.</summary>
    internal static bool Is(TypeReference type)
    {
        if (!Candidate(type)) return false;
        try { Validate(type); return true; }
        catch (InvalidDataException) { return false; }
    }

    /// <summary>Rejects a candidate class whose instances the heap model cannot represent, naming why.</summary>
    internal static TypeDefinition Validate(TypeReference type)
    {
        if (!Candidate(type)) throw new InvalidDataException(Unsupported + type.FullName);
        var definition = type.Resolve() ?? throw new InvalidDataException("Unresolved class: " + type.FullName);
        if (definition.IsInterface)
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  Interface-typed values need interface dispatch, which is not modelled (#477).");
        if (definition.HasGenericParameters)
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  Generic classes are not modelled.");
        if (definition.IsAbstract)
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  An abstract class has no instances without inheritance, which is not modelled.");
        if (definition.BaseType is not { FullName: "System.Object" } parent ||
            !RuntimeModels.ExactScope(parent.Scope, "System.Runtime"))
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  Only classes deriving directly from System.Object are modelled; inheritance is not.");
        if (definition.IsExplicitLayout)
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  Explicit class layout is not modelled.");
        if (definition.Methods.Any(method => method.Name == "Finalize" && method.IsVirtual &&
                !method.HasParameters && method.ReturnType.MetadataType == MetadataType.Void))
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  A finalizer runs outside the extracted call graph.");
        return definition;
    }

    /// <summary>
    /// The checked operation for <c>ldfld</c> or <c>stfld</c> of an integer or admitted-class field of a
    /// class instance, at the model offset of one 8-byte slot per instance field in declaration order. A
    /// class-typed field holds an object reference in its slot, never in bytes.
    /// </summary>
    internal static string FieldOperation(FieldReference field, FieldDefinition resolved, bool store, bool address)
    {
        var owner = field.DeclaringType;
        Validate(owner);
        if (address)
            throw new InvalidDataException("Unsupported field address on a class instance: " + field.FullName +
                "\n  Class field offsets are chosen by the model, so no address may observe them.");
        var type = resolved.FieldType;
        var holdsReference = !type.IsValueType && type is not PointerType and not FunctionPointerType;
        if (holdsReference && !Is(type))
            throw new InvalidDataException("Unsupported reference-typed field: " + field.FullName +
                "\n  Only fields holding instances of admitted classes are modelled; " + type.FullName +
                " is not one.");
        if (holdsReference)
        {
            var slot = FieldSlot * FieldIndex(field, resolved);
            return store ? $".memory (.setObjectReferenceField ({GenericEvidence.ObjectType(owner)}) {slot})"
                : $".memory (.objectReferenceField ({GenericEvidence.ObjectType(owner)}) {slot})";
        }
        int width;
        try { width = MetadataValidation.PrimitiveWidth(type); }
        catch (InvalidDataException)
        {
            throw new InvalidDataException("Unsupported class instance field type: " + field.FullName +
                "\n  Only integer, Boolean, Char and enum fields of class instances are modelled.");
        }
        var offset = FieldSlot * FieldIndex(field, resolved);
        var signed = EnumTypes.Storage(type).FullName is "System.SByte" or "System.Int16";
        return store ? $".memory (.setObjectField ({GenericEvidence.ObjectType(owner)}) {offset} {width})"
            : $".memory (.objectField ({GenericEvidence.ObjectType(owner)}) {offset} {width} " +
                $"{signed.ToString().ToLowerInvariant()})";
    }

    /// <summary>The declaration-order index of an instance field among its class's instance fields.</summary>
    static int FieldIndex(FieldReference field, FieldDefinition resolved)
    {
        var index = Array.FindIndex(MetadataValidation.Fields(field.DeclaringType),
            candidate => candidate.Definition == resolved);
        return index >= 0 ? index
            : throw new InvalidDataException("Unresolved class instance field: " + field.FullName);
    }

    /// <summary>
    /// The checked operation for <c>newobj</c> of an admitted class: a fresh instance of one 8-byte slot per
    /// instance field, passed to <paramref name="constructor"/> at method index <paramref name="index"/>.
    /// </summary>
    internal static string Construction(MethodDefinition constructor, int index)
    {
        var owner = Validate(constructor.DeclaringType);
        var size = FieldSlot * MetadataValidation.Fields(owner).Length;
        return $".newObject {index} {constructor.Parameters.Count} ({GenericEvidence.ObjectType(owner)}) {size}";
    }

    // Matches `CIL.objectFieldSlot`, which Lean uses to recheck every emitted offset.
    const int FieldSlot = 8;
}
