using System.Globalization;
using System.Text;
using System.Text.Json;

namespace Nethermind.LeanCIL;

// Short UTF-8 certificates avoid repeatedly encoding long metadata identities in the kernel.
internal sealed class ExternalIdentityEvidence
{
    const int ChunkBytes = 32;
    static readonly UTF8Encoding StrictUtf8 = new(false, true);
    readonly Dictionary<string, int> indices = new(StringComparer.Ordinal);
    readonly Dictionary<string, string> chunks = new(StringComparer.Ordinal);
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
            var encoded = StrictUtf8.GetBytes(identity);
            var proofs = EmitChunks(lean, encoded);
            var bytes = string.Join(", ", encoded
                .Select(value => value.ToString(CultureInfo.InvariantCulture)));
            lean.AppendLine($"def {name}Bytes : ByteArray := ⟨#[{bytes}]⟩");
            lean.AppendLine($"theorem {name}Bytes_valid : {name}Bytes.IsValidUTF8 := {AppendProof(proofs)}");
            lean.AppendLine($"#print axioms {name}Bytes_valid");
            lean.AppendLine($"def {name} : String := " +
                $"{{ toByteArray := {name}Bytes, isValidUTF8 := {name}Bytes_valid }}");
            emitted++;
        }
    }

    List<string> EmitChunks(StringBuilder lean, byte[] encoded)
    {
        var proofs = new List<string>();
        for (var offset = 0; offset < encoded.Length;)
        {
            var end = Math.Min(offset + ChunkBytes, encoded.Length);
            // A chunk must not separate a leading byte from its UTF-8 continuation bytes.
            while (end < encoded.Length && (encoded[end] & 0xc0) == 0x80) end--;
            var chunk = encoded.AsSpan(offset, end - offset);
            var key = Convert.ToHexString(chunk);
            if (!chunks.TryGetValue(key, out var chunkName))
            {
                chunkName = "externalIdentityChunk" + chunks.Count.ToString(CultureInfo.InvariantCulture);
                chunks.Add(key, chunkName);
                var chunkBytes = string.Join(", ", chunk.ToArray()
                    .Select(value => value.ToString(CultureInfo.InvariantCulture)));
                var proof = chunk.ContainsAnyInRange((byte)128, byte.MaxValue) ? "by decide +kernel" :
                    $"by exact ({JsonSerializer.Serialize(Encoding.UTF8.GetString(chunk))}).isValidUTF8";
                lean.AppendLine($"def {chunkName} : ByteArray := ⟨#[{chunkBytes}]⟩");
                lean.AppendLine($"theorem {chunkName}_valid : {chunkName}.IsValidUTF8 := {proof}");
                lean.AppendLine($"#print axioms {chunkName}_valid");
            }
            proofs.Add(chunkName + "_valid");
            offset = end;
        }
        return proofs;
    }

    static string AppendProof(List<string> proofs) => proofs.Count switch
    {
        0 => "ByteArray.isValidUTF8_empty",
        1 => proofs[0],
        _ => $"({AppendProof(proofs[..(proofs.Count / 2)])}).append ({AppendProof(proofs[(proofs.Count / 2)..])})"
    };
}
