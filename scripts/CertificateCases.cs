using System.Text.Json.Nodes;

/// <summary>
/// Certificates that differ from a valid default certificate in one way every certificate reader must refuse, and
/// the form a deep run would give a valid one.
/// </summary>
static class CertificateCases
{
    static JsonArray Facts(JsonNode report) => report["binding"]!["facts"]!.AsArray();

    /// <summary>The valid default certificate `valid` as a deep run writes it: each fact reconfirmed by a theorem.
    /// </summary>
    internal static string Deep(string valid)
    {
        var report = JsonNode.Parse(valid)!;
        report["binding"]!["mode"] = "deep";
        foreach (var fact in Facts(report))
        {
            fact!["status"] = "reconfirmed";
            fact["theorem"] = "BindingAudit.bodies";
        }
        return report.ToJsonString();
    }

    /// <summary>Each variant of the valid default certificate `valid` that a default reader refuses, by name.</summary>
    internal static IEnumerable<(string Case, string Text)> Refused(string valid)
    {
        (string, string) Changed(string name, Action<JsonNode> change)
        {
            var report = JsonNode.Parse(valid)!;
            change(report);
            return (name, report.ToJsonString());
        }
        yield return Changed("schema 4", report => report["schema"] = 4);
        yield return Changed("no binding section", report => report.AsObject().Remove("binding"));
        yield return Changed("a missing fact", report => Facts(report).RemoveAt(3));
        yield return Changed("reordered facts", report =>
        {
            var facts = Facts(report);
            var first = facts[0];
            facts.RemoveAt(0);
            facts.Add(first);
        });
        yield return Changed("a repeated fact", report => Facts(report).Add(Facts(report)[0]!.DeepClone()));
        yield return Changed("an unknown fact", report => Facts(report)[0]!["id"] = "body-offsets");
        yield return Changed("an unknown status", report => Facts(report)[0]!["status"] = "assumed");
        yield return Changed("a status given as a number", report => Facts(report)[0]!["status"] = 0);
        yield return Changed("a fact without a status", report => Facts(report)[0]!.AsObject().Remove("status"));
        yield return Changed("a trusted fact naming a theorem",
            report => Facts(report)[0]!["theorem"] = "BindingAudit.bodies");
        yield return ("a deep run's certificate", Deep(valid));
    }
}
