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
        if (parent.FullName == "System.Object" &&
            RuntimeModels.ExactScope(parent, PlatformAssemblies.SystemRuntime))
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
    /// The exact <c>System.String</c> of <c>System.Runtime</c>: a value of it is an object reference the model can
    /// pass, store, compare and test for null, never read through, since no admitted operation reads characters.
    /// </summary>
    internal static bool IsString(TypeReference type) =>
        type is not TypeSpecification && type.FullName == "System.String" &&
        RuntimeModels.ExactScope(type, PlatformAssemblies.SystemRuntime);

    /// <summary>
    /// A type whose values are object references on the stack and in argument and local roots: an admitted class,
    /// or <c>string</c>, which is opaque.
    /// </summary>
    internal static bool Reference(TypeReference type) => Is(type) || IsString(type);

    /// <summary>
    /// A candidate class or <c>string</c>: its values live in roots without byte storage, so neither an argument,
    /// a local nor a by-reference type may address one.
    /// </summary>
    internal static bool Rooted(TypeReference type) => Candidate(type) || IsString(type);

    /// <summary>
    /// A class, interface or delegate type outside the model, such as <c>string</c>, a generic or library class:
    /// a field of this type holds a reference the model can copy, compare and test for null but never dereference,
    /// since no admitted operation accepts the type as an owner, receiver, argument, local or result.
    /// </summary>
    internal static bool Opaque(TypeReference type) =>
        !type.IsValueType && type is GenericInstanceType or not (TypeSpecification or GenericParameter) &&
        !Is(type);

    /// <summary>
    /// The checked operation for <c>ldfld</c> or <c>stfld</c> of an integer, class-typed, class-array or
    /// value-array field of a class instance, at the model offset of its slot. A class-typed field, admitted or
    /// opaque, or a field holding an array of a class holds an object reference in its slot, never in bytes; a
    /// value-array field holds the origin of a whole array of its element type there, a struct element taking its
    /// width from the layout for <paramref name="architecture"/>.
    /// </summary>
    internal static Operation FieldOperation(FieldReference field, FieldDefinition resolved, bool store, bool address,
        string architecture)
    {
        var owner = field.DeclaringType;
        Validate(owner);
        if (address)
            throw new InvalidDataException("Unsupported field address on a class instance: " + field.FullName +
                "\n  Class field offsets are chosen by the model, so no address may observe them.");
        var type = resolved.FieldType;
        var holdsReference = !type.IsValueType && type is not PointerType and not FunctionPointerType;
        var valueArray = Arrays.Of(type, architecture);
        if (holdsReference && !Is(type) && !Opaque(type) && !ReferenceArrays.Is(type) && valueArray is null)
            throw new InvalidDataException("Unsupported reference-typed field: " + field.FullName +
                "\n  Only fields holding class instances, arrays of classes or single-dimensional arrays of " +
                "reference-free value types are modelled; " + type.FullName +
                " is another array, a generic parameter or a modified type.");
        var offset = FieldSlot * FieldIndex(owner, resolved);
        if (valueArray is not null)
            return new ClassField(new(store, GenericEvidence.ObjectType(owner), offset, ClassViews.FieldKind.Array,
                null, false, valueArray));
        if (holdsReference)
            return new ClassField(new(store, GenericEvidence.ObjectType(owner), offset,
                ClassViews.FieldKind.Reference, null, false, null));
        int width;
        try { width = MetadataValidation.PrimitiveWidth(type); }
        catch (InvalidDataException)
        {
            throw new InvalidDataException("Unsupported class instance field type: " + field.FullName +
                "\n  Only integer, Boolean, Char and enum fields of class instances are modelled.");
        }
        var signed = EnumTypes.Storage(type).FullName is "System.SByte" or "System.Int16";
        return new ClassField(new(store, GenericEvidence.ObjectType(owner), offset, ClassViews.FieldKind.Word, width,
            !store && signed, null));
    }

    /// <summary>The emitted list of an admitted class's base classes, nearest first.</summary>
    internal static string BaseList(TypeReference type) =>
        LeanText.ClassList(Bases(type).Select(GenericEvidence.ObjectType));

    /// <summary>
    /// The checked operation for <c>newobj</c> of an admitted class: a fresh instance of its runtime type, with
    /// one 8-byte slot per instance field including its bases', passed to <paramref name="constructor"/> at
    /// method index <paramref name="index"/>. An abstract class has no instances of its own.
    /// </summary>
    internal static Operation Construction(MethodDefinition constructor, int index)
    {
        var owner = Validate(constructor.DeclaringType);
        if (owner.IsAbstract)
            throw new InvalidDataException("Unsupported construction of an abstract class: " + owner.FullName +
                "\n  newobj of an abstract class fails at run time; only its derived classes have instances.");
        var size = FieldSlot * Fields(owner).Length;
        var type = GenericEvidence.ObjectType(owner);
        return new NewObject(index, constructor.Parameters.Count, type,
            [.. Bases(owner).Select(GenericEvidence.ObjectType)], size);
    }

    /// <summary>
    /// A castclass or isinst of an admitted class other than System.Object, which an instance's recorded lineage
    /// decides.
    /// </summary>
    internal static bool Testable(Instruction instruction) =>
        instruction is { OpCode.Code: Code.Castclass or Code.Isinst, Operand: TypeReference target } &&
        target.FullName != "System.Object" && Is(target);

    /// <summary>
    /// The checked type test for castclass (throwing InvalidCastException) or isinst (giving null) of an admitted
    /// class. An instance records only its own and its admitted base classes, so a test against an interface or
    /// System.Object is rejected, naming why.
    /// </summary>
    internal static Operation Test(Instruction instruction)
    {
        var target = (TypeReference)instruction.Operand;
        var site = $"Unsupported type test: {instruction.OpCode.Name} {target.FullName}\n  ";
        if (target.FullName == "System.Object")
            throw new InvalidDataException(site +
                "Every instance is a System.Object, which the model does not record.");
        if (target.Resolve() is { IsInterface: true })
            throw new InvalidDataException(site +
                "Interface type tests need the interfaces an instance implements, which the model does not record.");
        if (!Candidate(target))
            throw new InvalidDataException(site +
                "Only classes of the pinned assemblies are tested; their instances record their class lineage.");
        try { Validate(target); }
        catch (InvalidDataException error)
        {
            throw new InvalidDataException(
                site + error.Message.Replace("\n", "\n  ", StringComparison.Ordinal), error);
        }
        return new ObjectTest(GenericEvidence.ObjectType(target), instruction.OpCode.Code == Code.Castclass);
    }

    // Matches `CIL.objectFieldSlot`, which Lean uses to recheck every emitted offset.
    const int FieldSlot = 8;
}
