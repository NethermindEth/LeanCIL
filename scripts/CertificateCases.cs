using System.Text.Json.Nodes;

/// <summary>
/// Certificates that differ from a valid default certificate in one way every certificate reader must refuse, and
/// the form a deep run would give a valid one.
/// </summary>
static class CertificateCases
{
    static JsonArray Facts(JsonNode report) => report["binding"]!["facts"]!.AsArray();

    /// <summary>
    /// The valid default certificate `valid` as a deep run writes it: the digest file and sources named, one
    /// pinned image and each fact reconfirmed by a theorem.
    /// </summary>
    internal static string Deep(string valid)
    {
        var report = JsonNode.Parse(valid)!;
        var binding = report["binding"]!;
        binding["mode"] = "deep";
        binding["digests"] = new JsonObject { ["path"] = "pins.sha256", ["sha256"] = new string('0', 64) };
        binding["sources"] = new JsonObject
        {
            ["strictBinding"] = new string('a', 64), ["leanToolchain"] = "leanprover/lean4:v4",
            ["lean"] = new string('1', 64)
        };
        binding["images"] = new JsonArray(new JsonObject
        {
            ["identity"] = "Examples", ["sha256"] = new string('2', 64), ["role"] = "pinned",
            ["status"] = "reconfirmed", ["theorem"] = "BindingAudit.I0.digest", ["reason"] = null
        });
        foreach (var fact in Facts(report))
        {
            fact!["status"] = "reconfirmed";
            fact["theorem"] = "BindingAudit.bodies";
        }
        return report.ToJsonString();
    }

    /// <summary>Independent malformed deep metadata values, each applied to a valid certificate.</summary>
    internal static IEnumerable<(string Case, string Text)> RefusedDeep(string valid)
    {
        (string Section, string Field, bool Hash)[] fields =
        [
            ("digests", "path", false), ("digests", "sha256", true),
            ("sources", "strictBinding", true), ("sources", "leanToolchain", false),
            ("sources", "lean", true), ("images", "identity", false), ("images", "sha256", true)
        ];
        foreach (var (section, field, hash) in fields)
        {
            string?[] values = hash
                ? [null, "", " \t\r\n", new string('a', 63), new string('a', 65), new string('g', 64),
                    new string('a', 63) + "\n", " " + new string('a', 64)]
                : [null, "", " \t\r\n"];
            foreach (var (index, value) in values.Index())
            {
                var report = JsonNode.Parse(Deep(valid))!;
                var target = report["binding"]![section]!;
                if (section == "images") target = target[0]!;
                target[field] = value;
                yield return ($"{section}.{field} malformed value {index}", report.ToJsonString());
            }
        }
    }

    /// <summary>Deep certificates with valid mixed-case digests and each settled image and fact status.</summary>
    internal static IEnumerable<string> AcceptedDeep(string valid)
    {
        var report = JsonNode.Parse(Deep(valid))!;
        var binding = report["binding"]!;
        const string digest = "0123456789abcdef" + "0123456789ABCDEF" + "0123456789abcdef" + "0123456789ABCDEF";
        binding["digests"]!["sha256"] = digest;
        binding["sources"]!["strictBinding"] = digest;
        binding["sources"]!["lean"] = digest;
        binding["images"]![0]!["sha256"] = digest;
        yield return report.ToJsonString();
        foreach (var fact in Facts(report).Append(binding["images"]![0]))
        {
            fact!["status"] = "not covered";
            fact["theorem"] = null;
            fact["reason"] = "An image was not supplied.";
        }
        yield return report.ToJsonString();
        binding["images"] = new JsonArray();
        yield return report.ToJsonString();
    }

    /// <summary>Each variant of the valid default certificate `valid` that a default reader refuses, by name.
    /// </summary>
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
        yield return Changed("a default section naming a digest file", report => report["binding"]!["digests"] =
            JsonNode.Parse(Deep(valid))!["binding"]!["digests"]!.DeepClone());
        yield return Changed("a default section without its images",
            report => report["binding"]!.AsObject().Remove("images"));
        yield return ("a deep run's certificate", Deep(valid));
    }
}
