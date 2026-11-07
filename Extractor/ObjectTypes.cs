using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Class instances the checked heap admits: a reference is an allocation identity, and the
// allocation records the runtime type, with its admitted base classes, that every field access is checked against.
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

    /// <summary>
    /// Rejects a candidate class whose instances the heap model cannot represent, naming why. A class derives from
    /// System.Object directly or through admitted classes; an abstract class is admitted as a type, never constructed.
    /// </summary>
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
        if (definition.IsExplicitLayout)
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  Explicit class layout is not modelled.");
        if (definition.Methods.Any(method => method.Name == "Finalize" && method.IsVirtual &&
                !method.HasParameters && method.ReturnType.MetadataType == MetadataType.Void))
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  A finalizer runs outside the extracted call graph.");
        var parent = definition.BaseType ?? throw new InvalidDataException(Unsupported + type.FullName);
        if (parent.FullName == "System.Object" && RuntimeModels.ExactScope(parent.Scope, "System.Runtime"))
            return definition;
        if (!Candidate(parent))
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  Only classes deriving from System.Object through admitted classes are modelled; " +
                parent.FullName + " is not one.");
        try { Validate(parent); }
        catch (InvalidDataException error)
        {
            throw new InvalidDataException(Unsupported + type.FullName + "\n  Its base class is not admitted: " +
                error.Message.Replace("\n", "\n  ", StringComparison.Ordinal), error);
        }
        return definition;
    }

    /// <summary>The admitted base classes of an admitted class, nearest first, excluding System.Object.</summary>
    internal static TypeReference[] Bases(TypeReference type)
    {
        var bases = new List<TypeReference>();
        for (var parent = Validate(type).BaseType; parent is not null && parent.FullName != "System.Object";
            parent = Validate(parent).BaseType)
            bases.Add(parent);
        return [.. bases];
    }

    /// <summary>
    /// The instance fields of an admitted class in model order: its bases' fields first, farthest base first, then
    /// its own in declaration order. Each takes one 8-byte slot, so a derived instance extends its base's layout.
    /// </summary>
    internal static FieldDefinition[] Fields(TypeReference type) =>
        [.. Bases(type).Reverse().Append(type).SelectMany(owner =>
            MetadataValidation.Fields(owner).Select(field => field.Definition))];

    /// <summary>
    /// The model slot index of an instance field of an admitted class, counting its bases' fields first.
    /// </summary>
    internal static int FieldIndex(TypeReference owner, FieldDefinition resolved)
    {
        var index = Array.IndexOf(Fields(owner), resolved);
        return index >= 0 ? index
            : throw new InvalidDataException(
                "Unresolved class instance field: " + owner.FullName + "::" + resolved.Name);
    }

    /// <summary>
    /// The checked operation for <c>ldfld</c> or <c>stfld</c> of an integer or admitted-class field of a
    /// class instance, at the model offset of its slot. A class-typed field holds an object reference in its
    /// slot, never in bytes.
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
        var offset = FieldSlot * FieldIndex(owner, resolved);
        if (holdsReference)
            return store ? $".memory (.setObjectReferenceField ({GenericEvidence.ObjectType(owner)}) {offset})"
                : $".memory (.objectReferenceField ({GenericEvidence.ObjectType(owner)}) {offset})";
        int width;
        try { width = MetadataValidation.PrimitiveWidth(type); }
        catch (InvalidDataException)
        {
            throw new InvalidDataException("Unsupported class instance field type: " + field.FullName +
                "\n  Only integer, Boolean, Char and enum fields of class instances are modelled.");
        }
        var signed = EnumTypes.Storage(type).FullName is "System.SByte" or "System.Int16";
        return store ? $".memory (.setObjectField ({GenericEvidence.ObjectType(owner)}) {offset} {width})"
            : $".memory (.objectField ({GenericEvidence.ObjectType(owner)}) {offset} {width} " +
                $"{signed.ToString().ToLowerInvariant()})";
    }

    /// <summary>The emitted list of an admitted class's base classes, nearest first.</summary>
    internal static string BaseList(TypeReference type) =>
        "[" + string.Join(", ", Bases(type).Select(parent => $"({GenericEvidence.ObjectType(parent)})")) + "]";

    /// <summary>
    /// The checked operation for <c>newobj</c> of an admitted class: a fresh instance of its runtime type, with
    /// one 8-byte slot per instance field including its bases', passed to <paramref name="constructor"/> at
    /// method index <paramref name="index"/>. An abstract class has no instances of its own.
    /// </summary>
    internal static string Construction(MethodDefinition constructor, int index)
    {
        var owner = Validate(constructor.DeclaringType);
        if (owner.IsAbstract)
            throw new InvalidDataException("Unsupported construction of an abstract class: " + owner.FullName +
                "\n  newobj of an abstract class fails at run time; only its derived classes have instances.");
        var size = FieldSlot * Fields(owner).Length;
        return $".newObject {index} {constructor.Parameters.Count} ({GenericEvidence.ObjectType(owner)}) " +
            $"{BaseList(owner)} {size}";
    }

    // Matches `CIL.objectFieldSlot`, which Lean uses to recheck every emitted offset.
    const int FieldSlot = 8;
}
