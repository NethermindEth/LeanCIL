using System.Text.Json;
using Nethermind.LeanCIL;

partial class Program
{
    static InitializationAssumption[] ExportInitializationAssumptions(JsonElement identity) =>
        identity.GetProperty("initializationAssumptions")
            .Deserialize<InitializationAssumption[]>(ContractInterface.Json)
            ?? throw new InvalidDataException("Missing generated initialization assumptions.");

    static ProfileInitializationAssumptions[]? PublishedInitializationAssumptions(
        IEnumerable<PreparedContractExport> exports)
    {
        var profiles = exports.OrderBy(export => export.Profile, StringComparer.Ordinal)
            .Select(export => new ProfileInitializationAssumptions(export.Profile, export.InitializationAssumptions))
            .ToArray();
        return profiles.All(profile => profile.Types.Length == 0) ? null : profiles;
    }

    static string InitializationAuditSource(PreparedContractExport export) =>
        export.InitializationAssumptions.Length == 0 ? "" : $$"""
/-- The published runtime premises are exactly those recorded by fresh extraction. -/
theorem LeanCILExportAudit.initializationAssumptions :
    _root_.Extracted.initializationAssumptions =
      {{InitializationAssumption.Lean(export.InitializationAssumptions)}} := rfl
#print axioms LeanCILExportAudit.initializationAssumptions
""";

    static AuditRequest[] InitializationAuditRequests(PreparedContractExport export)
    {
        if (export.InitializationAssumptions.Length == 0) return [];
        static object Polymorphic(string name, params int[] levels) => new { @const = name, levels };
        var pair = new { app = new object[] { Polymorphic("Prod", 0, 0),
            AuditConstant("String"), AuditConstant("String") } };
        object list = new { app = new object[] { Polymorphic("List.nil", 0), pair } };
        foreach (var assumption in export.InitializationAssumptions.Reverse())
            list = new { app = new object[] { Polymorphic("List.cons", 0), pair,
                new { app = new object[] { Polymorphic("Prod.mk", 0, 0),
                    AuditConstant("String"), AuditConstant("String"),
                    new { str = assumption.AssemblyIdentity }, new { str = assumption.TypeName } } }, list } };
        return [new("LeanCILExportAudit.initializationAssumptions", axioms: ApprovedAxioms,
            type: new { app = new object[] { Polymorphic("Eq", 1),
                new { app = new object[] { Polymorphic("List", 0), pair } },
                AuditConstant("Extracted.initializationAssumptions"), list } })];
    }
}
