using System.Globalization;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Text;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal sealed record StaticIdentityRecord(string Identity, string AssemblyIdentity, string FieldName);

internal static class StaticIdentity
{
    static readonly ConditionalWeakTable<FieldDefinition, StaticIdentityRecord> identities = new();
    static readonly ConditionalWeakTable<ModuleDefinition, HashSet<string>> staticFields = new();

    internal static StaticIdentityRecord Of(FieldDefinition field) => identities.GetValue(field, static field =>
    {
        string assembly = AssemblyIdentity(field.Module.Assembly.Name);
        return new(Key(assembly, field.FullName), assembly, field.FullName);
    });

    // Published keys hash this exact text; it must not follow a metadata library's display format.
    internal static string AssemblyIdentity(AssemblyNameReference name)
    {
        byte[] token = name.PublicKeyToken;
        return string.Create(CultureInfo.InvariantCulture,
            $"{name.Name}, Version={name.Version.ToString(4)}, Culture={(string.IsNullOrEmpty(name.Culture) ? "neutral" : name.Culture)}, PublicKeyToken={(token is { Length: > 0 } ? Convert.ToHexStringLower(token) : "null")}{(name.IsRetargetable ? ", Retargetable=Yes" : "")}");
    }

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
        }
        // Collisions are reported over the whole set first, so the diagnostic names both fields.
        foreach (StaticIdentityRecord identity in keys.Values)
            if (identity.Identity != Key(identity.AssemblyIdentity, identity.FieldName))
                throw new InvalidDataException("Invalid scoped static identity.");
    }

    internal static void ValidateFields(IEnumerable<StaticIdentityRecord> identities, ModuleDefinition module)
    {
        string assembly = AssemblyIdentity(module.Assembly.Name);
        HashSet<string> fields = staticFields.GetValue(module, static module => module.GetTypes().SelectMany(type => type.Fields)
            .Where(field => field.IsStatic).Select(field => field.FullName).ToHashSet(StringComparer.Ordinal));
        foreach (StaticIdentityRecord identity in identities)
            if (identity.AssemblyIdentity != assembly || !fields.Contains(identity.FieldName))
                throw new InvalidDataException("Certified static field is not present in its implementation: " + identity.FieldName);
    }
}
