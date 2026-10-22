using System.Collections.Immutable;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;

namespace Nethermind.LeanCIL;

internal sealed class VectorSignatures : ISignatureTypeProvider<bool, object?>
{
    readonly HashSet<TypeSpecificationHandle> active = [];
    readonly HashSet<TypeSpecificationHandle> checkedTypes = [];

    internal static void Validate(byte[] assembly)
    {
        using PEReader image = new(new MemoryStream(assembly));
        MetadataReader reader = image.GetMetadataReader();
        VectorSignatures provider = new();
        foreach (FieldDefinitionHandle handle in reader.FieldDefinitions)
            reader.GetFieldDefinition(handle).DecodeSignature(provider, null);
        foreach (MethodDefinitionHandle handle in reader.MethodDefinitions)
        {
            System.Reflection.Metadata.MethodDefinition method = reader.GetMethodDefinition(handle);
            method.DecodeSignature(provider, null);
            if (method.RelativeVirtualAddress != 0)
            {
                StandaloneSignatureHandle locals = image.GetMethodBody(method.RelativeVirtualAddress).LocalSignature;
                if (!locals.IsNil) reader.GetStandaloneSignature(locals).DecodeLocalSignature(provider, null);
            }
        }
        foreach (MemberReferenceHandle handle in reader.MemberReferences)
        {
            MemberReference member = reader.GetMemberReference(handle);
            if (member.GetKind() == MemberReferenceKind.Field) member.DecodeFieldSignature(provider, null);
            else member.DecodeMethodSignature(provider, null);
        }
        for (int row = 1; row <= reader.GetTableRowCount(TableIndex.TypeSpec); row++)
            provider.GetTypeFromSpecification(reader, null, MetadataTokens.TypeSpecificationHandle(row), 0);
        for (int row = 1; row <= reader.GetTableRowCount(TableIndex.MethodSpec); row++)
            reader.GetMethodSpecification(MetadataTokens.MethodSpecificationHandle(row)).DecodeSignature(provider, null);
    }

    static bool Check(MetadataReader reader, StringHandle scope, StringHandle name, byte kind)
    {
        if (reader.StringComparer.Equals(scope, "System.Runtime.Intrinsics") &&
            (reader.StringComparer.Equals(name, "Vector128`1") || reader.StringComparer.Equals(name, "Vector256`1")) &&
            kind != (byte)SignatureTypeKind.ValueType)
            throw new InvalidDataException("Unsupported vector type encoding: " + reader.GetString(name) + " must use a value-type signature.");
        return false;
    }

    public bool GetTypeFromDefinition(MetadataReader reader, TypeDefinitionHandle handle, byte rawTypeKind)
    {
        System.Reflection.Metadata.TypeDefinition type = reader.GetTypeDefinition(handle);
        return Check(reader, type.Namespace, type.Name, rawTypeKind);
    }

    public bool GetTypeFromReference(MetadataReader reader, TypeReferenceHandle handle, byte rawTypeKind)
    {
        TypeReference type = reader.GetTypeReference(handle);
        return Check(reader, type.Namespace, type.Name, rawTypeKind);
    }

    public bool GetTypeFromSpecification(MetadataReader reader, object? genericContext, TypeSpecificationHandle handle, byte rawTypeKind)
    {
        if (checkedTypes.Contains(handle)) return false;
        if (active.Count >= 128 || !active.Add(handle)) throw new InvalidDataException("Cyclic or excessively nested vector type signature.");
        reader.GetTypeSpecification(handle).DecodeSignature(this, genericContext);
        active.Remove(handle);
        checkedTypes.Add(handle);
        return false;
    }

    public bool GetArrayType(bool elementType, ArrayShape shape) => false;
    public bool GetByReferenceType(bool elementType) => false;
    public bool GetFunctionPointerType(MethodSignature<bool> signature) => false;
    public bool GetGenericInstantiation(bool genericType, ImmutableArray<bool> typeArguments) => false;
    public bool GetGenericMethodParameter(object? genericContext, int index) => false;
    public bool GetGenericTypeParameter(object? genericContext, int index) => false;
    public bool GetModifiedType(bool modifier, bool unmodifiedType, bool isRequired) => false;
    public bool GetPinnedType(bool elementType) => false;
    public bool GetPointerType(bool elementType) => false;
    public bool GetPrimitiveType(PrimitiveTypeCode typeCode) => false;
    public bool GetSZArrayType(bool elementType) => false;
}
