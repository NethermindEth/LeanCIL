using System.Globalization;
using System.Numerics;
using System.Security.Cryptography;
using System.Text;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal sealed record StaticIdentityRecord(string Identity, string AssemblyIdentity, string FieldName);

internal static class StaticIdentity
{
    internal static StaticIdentityRecord Of(FieldDefinition field) =>
        new(Key(field.Module.Assembly.Name.FullName, field.FullName), field.Module.Assembly.Name.FullName, field.FullName);

    internal static string Key(string assemblyIdentity, string fieldName)
    {
        byte[] assembly = Encoding.UTF8.GetBytes(assemblyIdentity);
        byte[] field = Encoding.UTF8.GetBytes(fieldName);
        using MemoryStream encoding = new();
        using (BinaryWriter writer = new(encoding, Encoding.UTF8, leaveOpen: true))
        {
            writer.Write(assembly.Length);
            writer.Write(assembly);
            writer.Write(field.Length);
            writer.Write(field);
        }
        return new BigInteger(SHA256.HashData(encoding.ToArray()), isUnsigned: true, isBigEndian: true)
            .ToString(CultureInfo.InvariantCulture);
    }

    internal static void Validate(IEnumerable<StaticIdentityRecord> identities)
    {
        Dictionary<string, StaticIdentityRecord> keys = new(StringComparer.Ordinal);
        foreach (StaticIdentityRecord identity in identities)
        {
            if (identity is null || string.IsNullOrWhiteSpace(identity.AssemblyIdentity) || string.IsNullOrWhiteSpace(identity.FieldName) ||
                string.IsNullOrWhiteSpace(identity.Identity))
                throw new InvalidDataException("Invalid scoped static identity.");
            if (keys.TryGetValue(identity.Identity, out StaticIdentityRecord? previous) && previous != identity)
                throw new InvalidDataException($"Static identity collision {identity.Identity}: {previous.AssemblyIdentity}::{previous.FieldName} and {identity.AssemblyIdentity}::{identity.FieldName}");
            keys[identity.Identity] = identity;
            if (identity.Identity != Key(identity.AssemblyIdentity, identity.FieldName))
                throw new InvalidDataException("Invalid scoped static identity.");
        }
    }

    internal static void ValidateFields(IEnumerable<StaticIdentityRecord> identities, ModuleDefinition module)
    {
        foreach (StaticIdentityRecord identity in identities)
            if (identity.AssemblyIdentity != module.Assembly.Name.FullName || !module.GetTypes().SelectMany(type => type.Fields)
                    .Any(field => field.IsStatic && field.FullName == identity.FieldName))
                throw new InvalidDataException("Certified static field is not present in its implementation: " + identity.FieldName);
    }
}
