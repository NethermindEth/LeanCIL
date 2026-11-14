using System.Buffers.Binary;
using System.Numerics;
using System.Security.Cryptography;
using System.Text;

/// <summary>
/// Lean source for an assembly file as a `StrictBinding.ImageBytes` constant, and for the SHA-256
/// proof of that constant as separate per-page lemmas, so no single kernel evaluation holds more
/// than one page of hashing. The generated text is never trusted: the kernel rejects a page lemma
/// or an image whose digest is not the stated one.
/// </summary>
static class BindingImage
{
    const int ChunkBytes = 64;
    const int PageChunks = 64;
    const int PageBytes = ChunkBytes * PageChunks;
    const int ChunkLiteralDigits = 2 * ChunkBytes;

    static readonly uint[] InitialState =
        [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];

    static readonly uint[] RoundConstants =
    [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    ];

    /// <summary>The lowercase hexadecimal SHA-256 digest of a file.</summary>
    internal static string Digest(byte[] file) => Convert.ToHexStringLower(SHA256.HashData(file));

    /// <summary>The page and image definitions of a file, in the namespace the caller has opened.</summary>
    internal static string Definitions(byte[] file)
    {
        var text = new StringBuilder();
        var pages = PageCount(file.Length);
        for (var page = 0; page < pages; page++)
        {
            var first = page * PageBytes;
            var chunks = (Math.Min(file.Length - first, PageBytes) + ChunkBytes - 1) / ChunkBytes;
            text.Append($"def page{page} : List Nat := [\n");
            for (var chunk = 0; chunk < chunks; chunk++)
            {
                var literal = ChunkLiteral(file, first + chunk * ChunkBytes);
                text.Append($"  0x{literal}{(chunk + 1 < chunks ? "," : "")}\n");
            }
            text.Append("]\n\n");
        }
        var names = string.Join(", ", Enumerable.Range(0, pages).Select(page => "page" + page));
        text.Append($"def image : StrictBinding.ImageBytes := {{ length := {file.Length}, pages := [{names}] }}\n");
        return text.ToString();
    }

    /// <summary>
    /// The digest theorem proved by one kernel evaluation: only for files of a few kilobytes, since
    /// the kernel keeps every intermediate term of the evaluation.
    /// </summary>
    internal static string SingleDigestTheorem(byte[] file) => file.Length > PageBytes
        ? throw new ArgumentException(
            "A single kernel evaluation is only for one page of file; use the paged theorem.")
        : $"theorem digest : StrictBinding.DigestIs image\n    0x{Digest(file)} := by decide +kernel\n";

    /// <summary>
    /// The digest theorem proved page by page: one lemma per page states the hash state it leaves,
    /// each checked by its own kernel evaluation, and `digest` assembles them. With
    /// <paramref name="skipCompileCheck"/> the lemmas are not checked when the module compiles, so a
    /// caller must kernel-replay the module.
    /// </summary>
    internal static string PagedDigestTheorem(byte[] file, bool skipCompileCheck)
    {
        var pages = PageCount(file.Length);
        var states = PageStates(file, pages);
        var text = new StringBuilder();
        var skip = skipCompileCheck ? "set_option debug.skipKernelTC true in\n" : "";
        for (var page = 0; page < pages; page++)
        {
            var from = page == 0 ? "StrictBinding.Sha256.initialState" : Words(states[page]);
            text.Append($"{skip}theorem hash{page} : StrictBinding.Sha256.hashBlocks {from} " +
                $"{PageTerm(page, pages, file.Length)} = {Words(states[page + 1])} := by decide +kernel\n");
        }
        // Each suffix of the page list and each proof of its hash is its own declaration, so no term nests
        // deeper than one level however many pages there are.
        text.Append($"def blocks{pages - 1} : List (List Nat) := [{PageTerm(pages - 1, pages, file.Length)}]\n");
        for (var page = pages - 2; page >= 0; page--)
            text.Append($"def blocks{page} : List (List Nat) := " +
                $"{PageTerm(page, pages, file.Length)} :: blocks{page + 1}\n");
        var final = Words(states[pages]);
        text.Append($"theorem tail{pages - 1} : StrictBinding.Sha256.PagesHash {Words(states[pages - 1])} " +
            $"blocks{pages - 1} {final} := .cons hash{pages - 1} (.nil _)\n");
        for (var page = pages - 2; page >= 0; page--)
        {
            var from = page == 0 ? "StrictBinding.Sha256.initialState" : Words(states[page]);
            text.Append($"theorem tail{page} : StrictBinding.Sha256.PagesHash {from} blocks{page} {final} := " +
                $".cons hash{page} tail{page + 1}\n");
        }
        text.Append($"theorem digest : StrictBinding.DigestIs image 0x{Digest(file)} :=\n");
        text.Append($"  StrictBinding.digestIs_of_hashes (final := {final}) (blocks := blocks0)\n");
        text.Append("    (by decide +kernel) tail0 (by decide +kernel) (by decide +kernel)\n");
        return text.ToString();
    }

    static int PageCount(int length) => (length + PageBytes - 1) / PageBytes;

    /// <summary>The page as hashed: every page but the last as it is, and the last with its padding.</summary>
    static string PageTerm(int page, int pages, int length) =>
        page + 1 < pages ? "page" + page : $"(StrictBinding.Sha256.padded page{page} {length})";

    static string ChunkLiteral(byte[] file, int offset)
    {
        var chunk = new byte[ChunkBytes];
        Array.Copy(file, offset, chunk, 0, Math.Min(ChunkBytes, file.Length - offset));
        var literal = Convert.ToHexStringLower(chunk);
        return literal.Length == ChunkLiteralDigits ? literal : throw new InvalidOperationException("Bad chunk");
    }

    static string Words(uint[] state) => "[" + string.Join(", ", state.Select(word => $"0x{word:x8}")) + "]";

    /// <summary>The hash state before page k, for k up to the page count: the state after the last page.</summary>
    static uint[][] PageStates(byte[] file, int pages)
    {
        var padding = (int)(64 - (file.LongLength + 9) % 64) % 64;
        var message = new byte[file.Length + 1 + padding + 8];
        file.CopyTo(message, 0);
        message[file.Length] = 0x80;
        BinaryPrimitives.WriteUInt64BigEndian(message.AsSpan(message.Length - 8), (ulong)file.Length * 8);
        var states = new uint[pages + 1][];
        var state = InitialState;
        states[0] = state;
        for (var page = 0; page < pages; page++)
        {
            var end = page + 1 < pages ? (page + 1) * PageBytes : message.Length;
            for (var offset = page * PageBytes; offset < end; offset += ChunkBytes)
                state = Compress(state, message.AsSpan(offset, ChunkBytes));
            states[page + 1] = state;
        }
        var final = new byte[32];
        for (var index = 0; index < 8; index++)
            BinaryPrimitives.WriteUInt32BigEndian(final.AsSpan(4 * index), state[index]);
        if (Convert.ToHexStringLower(final) != Digest(file))
            throw new InvalidOperationException("SHA-256 midstates disagree with the file digest");
        return states;
    }

    static uint Rotate(uint word, int amount) => BitOperations.RotateRight(word, amount);

    static uint[] Compress(uint[] state, ReadOnlySpan<byte> block)
    {
        Span<uint> schedule = stackalloc uint[64];
        for (var index = 0; index < 16; index++)
            schedule[index] = BinaryPrimitives.ReadUInt32BigEndian(block[(4 * index)..]);
        for (var index = 16; index < 64; index++)
        {
            var near = schedule[index - 15];
            var far = schedule[index - 2];
            var low = Rotate(near, 7) ^ Rotate(near, 18) ^ (near >> 3);
            var high = Rotate(far, 17) ^ Rotate(far, 19) ^ (far >> 10);
            schedule[index] = schedule[index - 16] + low + schedule[index - 7] + high;
        }
        var (a, b, c, d, e, f, g, h) =
            (state[0], state[1], state[2], state[3], state[4], state[5], state[6], state[7]);
        for (var index = 0; index < 64; index++)
        {
            var upperE = Rotate(e, 6) ^ Rotate(e, 11) ^ Rotate(e, 25);
            var first = h + upperE + ((e & f) ^ (~e & g)) + RoundConstants[index] + schedule[index];
            var upperA = Rotate(a, 2) ^ Rotate(a, 13) ^ Rotate(a, 22);
            var second = upperA + ((a & b) ^ (a & c) ^ (b & c));
            (h, g, f, e, d, c, b, a) = (g, f, e, d + first, c, b, a, first + second);
        }
        uint[] sum = [a, b, c, d, e, f, g, h];
        return [.. sum.Select((word, index) => state[index] + word)];
    }
}
