import CIL.Crypto.Words

/-!
# SHA-1 and public key tokens

FIPS 180-4 SHA-1 for kernel evaluation, sharing the padding and word helpers of
`CIL.Crypto`. SHA-1 appears only in the strong-name public key token of an assembly
identity: the token is the last eight bytes of the SHA-1 of the public key, reversed.
-/

namespace CIL.Crypto.Sha1

open CIL.Crypto (add xor3 choose majority blockWords padded wordsValue)

/-- Rotation of a 32-bit word to the left. -/
def rotl (word amount : Nat) : Nat :=
  Nat.lor (Nat.mod (Nat.shiftLeft word amount) 4294967296) (Nat.shiftRight word (32 - amount))

/-- The initial state. -/
def initialState : List Nat := [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]

/-- The `count` message schedule words that follow the sixteen words of a block. -/
def expand : Nat → List Nat → List Nat
  | 0, _ => []
  | count + 1, w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 ::
      w13 :: w14 :: w15 :: _ =>
    let next := rotl (xor3 w13 w8 (Nat.xor w2 w0)) 1
    next :: expand count [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, next]
  | _ + 1, _ => []

/-- The round function and constant of round `index`. -/
def roundFunction (index b c d : Nat) : Nat × Nat :=
  if index < 20 then (choose b c d, 0x5a827999)
  else if index < 40 then (xor3 b c d, 0x6ed9eba1)
  else if index < 60 then (majority b c d, 0x8f1bbcdc)
  else (xor3 b c d, 0xca62c1d6)

/-- The 80 rounds over the schedule words, returning the working variables. -/
def rounds (index : Nat) : List Nat → Nat → Nat → Nat → Nat → Nat → List Nat
  | w :: ws, a, b, c, d, e =>
    let (f, k) := roundFunction index b c d
    rounds (index + 1) ws (add (add (add (rotl a 5) f) (add e k)) w) a (rotl b 30) c d
  | [], a, b, c, d, e => [a, b, c, d, e]

/-- One block applied to the state. -/
def compress (state : List Nat) (block : Nat) : List Nat :=
  match state with
  | [a, b, c, d, e] =>
    let words := blockWords block
    match rounds 0 (words ++ expand 64 words) a b c d e with
    | [a', b', c', d', e'] => [add a a', add b b', add c c', add d d', add e e']
    | _ => []
  | _ => []

/-- All blocks applied in order, evaluating each block's state once. -/
def hashBlocks : List Nat → List Nat → List Nat
  | state, [] => state
  | state, block :: blocks =>
    let next := compress state block
    bif Nat.beq (next.foldl Nat.add 0) 0 then hashBlocks next blocks else hashBlocks next blocks

/-- The SHA-1 digest, as a number, of a byte list. -/
def ofBytes (bytes : List Nat) : Nat :=
  wordsValue (hashBlocks initialState (padded (chunkValues bytes.length bytes) bytes.length))

/-- The strong-name token of a public key, as the number whose big-endian hex is the token's
    text. -/
def keyToken (key : List Nat) : Nat :=
  littleEndian 8 (ofBytes key % 2 ^ 64)

end CIL.Crypto.Sha1
