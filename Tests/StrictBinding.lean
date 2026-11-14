import StrictBinding
import Tests.StrictBinding.Container
import Tests.StrictBinding.Bodies

/-!
# Strict binding tests: digests

SHA-256 and SHA-1 as the kernel evaluates them must agree with the FIPS 180-4 vectors and with
reference digests computed by the .NET cryptography library, at every padding boundary: a message
that ends a block exactly (`t = 0`), one that leaves room for the length (`t < 56`), one that
does not (`t >= 56`), and one that spans several blocks. A digest or image that differs by one
bit must be rejected, because the audit trusts the digest of an image constant only through
`DigestIs`.
-/

namespace Tests.StrictBinding

open _root_.StrictBinding

/-- The message of `count` bytes whose byte at index `i` is `i % 251`. -/
private def pattern (count : Nat) : List Nat := (List.range count).map (· % 251)

/-! ## SHA-256 -/

theorem sha256_empty : DigestIs (ImageBytes.ofBytes [])
    0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 := by decide +kernel
#print axioms sha256_empty

theorem sha256_abc : DigestIs (ImageBytes.ofBytes (asciiOf "abc"))
    0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad := by decide +kernel
#print axioms sha256_abc

/-- The 56-byte FIPS message, which leaves no room for the length in its block. -/
theorem sha256_two_block_message : DigestIs
    (ImageBytes.ofBytes (asciiOf "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"))
    0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1 := by decide +kernel
#print axioms sha256_two_block_message

theorem sha256_pattern_3 : DigestIs (ImageBytes.ofBytes (pattern 3))
    0xae4b3280e56e2faf83f414a6e3dabe9d5fbe18976544c05fed121accb85b53fc := by decide +kernel
#print axioms sha256_pattern_3

/-- 55 bytes: the length fits in the first block. -/
theorem sha256_pattern_55 : DigestIs (ImageBytes.ofBytes (pattern 55))
    0x463eb28e72f82e0a96c0a4cc53690c571281131f672aa229e0d45ae59b598b59 := by decide +kernel
#print axioms sha256_pattern_55

/-- 56 bytes: the length moves to a second block. -/
theorem sha256_pattern_56 : DigestIs (ImageBytes.ofBytes (pattern 56))
    0xda2ae4d6b36748f2a318f23e7ab1dfdf45acdc9d049bd80e59de82a60895f562 := by decide +kernel
#print axioms sha256_pattern_56

theorem sha256_pattern_63 : DigestIs (ImageBytes.ofBytes (pattern 63))
    0x29af2686fd53374a36b0846694cc342177e428d1647515f078784d69cdb9e488 := by decide +kernel
#print axioms sha256_pattern_63

/-- 64 bytes: a whole block of data and a padding block of its own. -/
theorem sha256_pattern_64 : DigestIs (ImageBytes.ofBytes (pattern 64))
    0xfdeab9acf3710362bd2658cdc9a29e8f9c757fcf9811603a8c447cd1d9151108 := by decide +kernel
#print axioms sha256_pattern_64

theorem sha256_pattern_65 : DigestIs (ImageBytes.ofBytes (pattern 65))
    0x4bfd2c8b6f1eec7a2afeb48b934ee4b2694182027e6d0fc075074f2fabb31781 := by decide +kernel
#print axioms sha256_pattern_65

/-- 120 bytes: the last block keeps 56 or more bytes, so the length needs a third block. -/
theorem sha256_pattern_120 : DigestIs (ImageBytes.ofBytes (pattern 120))
    0xf52b23db1fbb6ded89ef42a23ce0c8922c45f25c50b568a93bf1c075420bbb7c := by decide +kernel
#print axioms sha256_pattern_120

/-- 128 bytes: two whole blocks of data. -/
theorem sha256_pattern_128 : DigestIs (ImageBytes.ofBytes (pattern 128))
    0x471fb943aa23c511f6f72f8d1652d9c880cfa392ad80503120547703e56a2be5 := by decide +kernel
#print axioms sha256_pattern_128

/-- 4096 bytes fill one page exactly, so its padding block joins that page. -/
theorem sha256_one_full_page : DigestIs (ImageBytes.ofBytes (pattern 4096))
    0xd67c656e01756650d77717b0839985a056ec28ffe174601d690fc407a2ceffca := by decide +kernel
#print axioms sha256_one_full_page

/-- One chunk more starts a second page. -/
theorem sha256_second_page_of_one_chunk : DigestIs (ImageBytes.ofBytes (pattern 4097))
    0xa16560d668b843fb3be99ace41dbd18471f342bd3255a1d21204b35e43f74436 := by decide +kernel
#print axioms sha256_second_page_of_one_chunk

/-- The 64 bytes `0, 1, ..., 63` as one chunk. -/
private def firstChunk : Nat := CIL.Crypto.bytesValue (List.range 64)

/-- The byte 64 and its zero padding. -/
private def secondChunk : Nat := 0x40 * 2 ^ 504

/-- Two pages of one chunk each, holding `pattern 65`. -/
private def twoPages : ImageBytes := { length := 65, pages := [[firstChunk], [secondChunk]] }

/-- The state after the first page, as a generated module states it. -/
private def afterFirstPage : List Nat := Sha256.hashBlocks Sha256.initialState [firstChunk]

/-- The state after the second page and its padding block. -/
private def afterSecondPage : List Nat :=
  Sha256.hashBlocks afterFirstPage (CIL.Crypto.padded [secondChunk] 65)

/-- A digest assembled from separate page results equals the one a single evaluation proves. -/
theorem digest_from_page_results : DigestIs twoPages
    0x4bfd2c8b6f1eec7a2afeb48b934ee4b2694182027e6d0fc075074f2fabb31781 :=
  digestIs_of_hashes (final := afterSecondPage)
    (blocks := [[firstChunk], CIL.Crypto.padded [secondChunk] 65]) (by decide +kernel)
    (.cons (next := afterFirstPage) (by decide +kernel)
      (.cons (by decide +kernel) (.nil _))) (by decide +kernel) (by decide +kernel)
#print axioms digest_from_page_results

/-! ## Rejected digests and images -/

/-- A digest one above the true one is not the image's digest. -/
theorem wrong_digest_is_rejected : ¬ DigestIs (ImageBytes.ofBytes (asciiOf "abc"))
    (0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad + 1) := by
  decide +kernel
#print axioms wrong_digest_is_rejected

/-- One changed byte changes the digest, so the true digest no longer holds. -/
theorem flipped_byte_is_rejected : ¬ DigestIs (ImageBytes.ofBytes (0x62 :: asciiOf "bc"))
    0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad := by decide +kernel
#print axioms flipped_byte_is_rejected

/-- A chunk at or above `2 ^ 512` would hash as one value and read as another. -/
private def oversizedChunk : ImageBytes :=
  { length := 3, pages := [[0x616263 * 2 ^ 488 + 2 ^ 512]] }

theorem oversized_chunk_is_malformed : oversizedChunk.wellFormed = false := by decide +kernel
#print axioms oversized_chunk_is_malformed

theorem oversized_chunk_has_no_digest : ¬ DigestIs oversizedChunk
    0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad := by decide +kernel
#print axioms oversized_chunk_has_no_digest

/-- Nonzero padding after the last byte would be read as file content. -/
theorem nonzero_padding_is_malformed :
    ({ length := 3, pages := [[0x616263 * 2 ^ 488 + 1]] } : ImageBytes).wellFormed = false := by
  decide +kernel
#print axioms nonzero_padding_is_malformed

/-- A chunk count that does not match the length is malformed. -/
theorem short_chunk_list_is_malformed :
    ({ length := 65, pages := [[0x616263 * 2 ^ 488]] } : ImageBytes).wellFormed = false := by
  decide +kernel
#print axioms short_chunk_list_is_malformed

/-! ## SHA-1 and key tokens -/

theorem sha1_abc : CIL.Crypto.Sha1.ofBytes (asciiOf "abc") =
    0xa9993e364706816aba3e25717850c26c9cd0d89d := by
  decide +kernel
#print axioms sha1_abc

theorem sha1_empty : CIL.Crypto.Sha1.ofBytes [] = 0xda39a3ee5e6b4b0d3255bfef95601890afd80709 := by
  decide +kernel
#print axioms sha1_empty

theorem sha1_pattern_55 : CIL.Crypto.Sha1.ofBytes (pattern 55) =
    0x8ae2d46729cfe68ff927af5eec9c7d1b66d65ac2 := by decide +kernel
#print axioms sha1_pattern_55

theorem sha1_pattern_56 : CIL.Crypto.Sha1.ofBytes (pattern 56) =
    0x636e2ec698dac903498e648bd2f3af641d3c88cb := by decide +kernel
#print axioms sha1_pattern_56

theorem sha1_pattern_63 : CIL.Crypto.Sha1.ofBytes (pattern 63) =
    0x6d942da0c4392b123528f2905c713a3ce28364bd := by decide +kernel
#print axioms sha1_pattern_63

theorem sha1_pattern_65 : CIL.Crypto.Sha1.ofBytes (pattern 65) =
    0x69bd728ad6e13cd76ff19751fde427b00e395746 := by decide +kernel
#print axioms sha1_pattern_65

theorem sha1_pattern_64 : CIL.Crypto.Sha1.ofBytes (pattern 64) =
    0xc6138d514ffa2135bfce0ed0b8fac65669917ec7 := by decide +kernel
#print axioms sha1_pattern_64

theorem sha1_pattern_120 : CIL.Crypto.Sha1.ofBytes (pattern 120) =
    0xd3dbd653bd8597b7475321b60a36891278e6a04a := by decide +kernel
#print axioms sha1_pattern_120

/-- The token of a 160-byte key is the last eight digest bytes in reverse order. -/
theorem key_token_of_a_160_byte_key : CIL.Crypto.Sha1.keyToken (pattern 160) =
    0x473c444ebb4661a5 := by
  decide +kernel
#print axioms key_token_of_a_160_byte_key

end Tests.StrictBinding
