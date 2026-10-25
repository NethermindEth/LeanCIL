using System.Text.Json;

namespace Nethermind.LeanCIL;

// A deployment premise, not a claim that the CIL model executes a CLR type initializer.
internal sealed record InitializationAssumption(string AssemblyIdentity, string TypeName)
{
    internal static InitializationAssumption[] Normalize(IEnumerable<InitializationAssumption> assumptions) =>
        assumptions.Distinct().OrderBy(item => item.AssemblyIdentity, StringComparer.Ordinal)
            .ThenBy(item => item.TypeName, StringComparer.Ordinal).ToArray();

    internal static InitializationAssumption[] ForProfile(ContractExport export, string profile) =>
        export.InitializationAssumptions?.Single(item => item.Profile == profile).Types ?? [];

    internal static void ValidateExport(ContractExport export, int format)
    {
        if (export.InitializationAssumptions is not { } profiles) return;
        if (format != 2 || profiles.Any(item => item is null || item.Types is null) ||
            !profiles.Select(item => item.Profile).Order(StringComparer.Ordinal)
                .SequenceEqual(export.Profiles.Order(StringComparer.Ordinal), StringComparer.Ordinal))
            throw new InvalidDataException("Initialization assumptions require each exact exported profile.");
        foreach (var profile in profiles)
        {
            if (profile.Types.Any(item => item is null || string.IsNullOrWhiteSpace(item.AssemblyIdentity) ||
                    string.IsNullOrWhiteSpace(item.TypeName)) ||
                !profile.Types.SequenceEqual(Normalize(profile.Types)))
                throw new InvalidDataException("Initialization assumptions must be unique, scoped and sorted.");
        }
    }

    internal static string Lean(IEnumerable<InitializationAssumption> assumptions) =>
        "[" + string.Join(", ", assumptions.Select(item => "(" + JsonSerializer.Serialize(item.AssemblyIdentity) +
            ", " + JsonSerializer.Serialize(item.TypeName) + ")")) + "]";
}

internal sealed record ProfileInitializationAssumptions(string Profile, InitializationAssumption[] Types);
