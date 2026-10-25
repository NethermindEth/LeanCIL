using System.Globalization;
using System.Text;
using System.Text.Json;

namespace Nethermind.LeanCIL;

// Exact byte equalities pay for UTF-8 decoding once, before certificates reuse each identity.
internal sealed class ExternalIdentityEvidence
{
    readonly Dictionary<string, int> indices = new(StringComparer.Ordinal);
    readonly List<string> identities = [];
    int emitted;

    internal string Reference(string identity, bool reachable)
    {
        if (!reachable) return JsonSerializer.Serialize(identity);
        if (!indices.TryGetValue(identity, out var index))
        {
            index = identities.Count;
            identities.Add(identity);
            indices.Add(identity, index);
        }
        return "externalIdentity" + index.ToString(CultureInfo.InvariantCulture);
    }

    internal void Emit(StringBuilder lean)
    {
        while (emitted < identities.Count)
        {
            var identity = identities[emitted];
            var name = "externalIdentity" + emitted.ToString(CultureInfo.InvariantCulture);
            var literal = JsonSerializer.Serialize(identity);
            var bytes = string.Join(", ", Encoding.UTF8.GetBytes(identity)
                .Select(value => value.ToString(CultureInfo.InvariantCulture)));
            lean.AppendLine($"def {name}Bytes : ByteArray := ⟨#[{bytes}]⟩");
            lean.AppendLine($"theorem {name}Bytes_eq : {name}Bytes = ({literal}).toByteArray := by rfl");
            lean.AppendLine($"#print axioms {name}Bytes_eq");
            lean.AppendLine($"def {name} : String :=");
            lean.AppendLine($"  {{ toByteArray := {name}Bytes, isValidUTF8 := by");
            lean.AppendLine($"      rw [{name}Bytes_eq]; exact ({literal}).isValidUTF8 }}");
            lean.AppendLine($"theorem {name}_eq : {name} = {literal} :=");
            lean.AppendLine($"  String.toByteArray_inj.mp {name}Bytes_eq");
            lean.AppendLine($"#print axioms {name}_eq");
            emitted++;
        }
    }
}
