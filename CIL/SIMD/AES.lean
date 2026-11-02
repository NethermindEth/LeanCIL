import CIL.SIMD.Vector

/-!
# AES rounds

The AES round steps of FIPS-197 on one 128-bit state, and the x86 AESENC and ARM64 AESE/AESMC
instructions built from them. Byte `i` of the vector is state byte `i`, so row `r` and column
`c` hold byte `r + 4 * c`, as when the state is loaded from memory in FIPS-197 order.
-/

namespace CIL.Vector

/-- Multiplication by `x` in GF(2^8) modulo the AES polynomial x^8 + x^4 + x^3 + x + 1. -/
def aesXtime (value : BitVec 8) : BitVec 8 :=
  (value <<< 1) ^^^ (if value.msb then 0x1b else 0)

/-- Multiplication in the AES field GF(2^8). -/
def aesMultiply (left right : BitVec 8) : BitVec 8 :=
  ((List.range 8).foldl (fun (product, power) bit =>
    (if right.getLsbD bit then product ^^^ power else product, aesXtime power)) (0, left)).1

/-- The multiplicative inverse in GF(2^8), `value ^ 254`, with zero mapped to zero. -/
def aesInverse (value : BitVec 8) : BitVec 8 :=
  -- Six square-and-multiply steps reach value ^ 127; squaring gives value ^ 254.
  let power := (List.range 6).foldl (fun result _ => aesMultiply (aesMultiply result result) value)
    value
  aesMultiply power power

/-- The S-box: the field inverse followed by the FIPS-197 affine transformation. -/
def aesSubByte (value : BitVec 8) : BitVec 8 :=
  let inverse := aesInverse value
  inverse ^^^ inverse.rotateLeft 1 ^^^ inverse.rotateLeft 2 ^^^ inverse.rotateLeft 3 ^^^
    inverse.rotateLeft 4 ^^^ 0x63

/-- The state whose byte `i` is `byte i`. -/
def aesState (byte : Nat → BitVec 8) : V128 :=
  (List.range 16).foldl (fun result index =>
    result ||| ((byte index).zeroExtend 128 <<< (8 * index))) 0

/-- SubBytes: the S-box applied to every byte. -/
def aesSubBytes (state : V128) : V128 := aesState fun index => aesSubByte (lane8 state index)

/-- ShiftRows: row `r` rotates left by `r` columns. -/
def aesShiftRows (state : V128) : V128 :=
  aesState fun index =>
    let row := index % 4
    lane8 state (row + 4 * ((index / 4 + row) % 4))

/-- MixColumns: each column is multiplied by the FIPS-197 matrix circulant(2, 3, 1, 1). -/
def aesMixColumns (state : V128) : V128 :=
  aesState fun index =>
    let column := 4 * (index / 4)
    let entry (row : Nat) := lane8 state (column + (index % 4 + row) % 4)
    aesMultiply 2 (entry 0) ^^^ aesMultiply 3 (entry 1) ^^^ entry 2 ^^^ entry 3

/-- AESENC: one middle encryption round, ShiftRows, SubBytes and MixColumns, then the round
    key. -/
def aesEncryptRound (state roundKey : V128) : V128 :=
  aesMixColumns (aesSubBytes (aesShiftRows state)) ^^^ roundKey

/-- AESE: the round key first, then ShiftRows and SubBytes, without MixColumns. -/
def armAesEncrypt (state roundKey : V128) : V128 :=
  aesSubBytes (aesShiftRows (state ^^^ roundKey))

/-- ARM64's AESE with a zero key, AESMC and a separate key XOR compute x86 AESENC, so a hash
    round written either way has the same result on every state and key. -/
theorem armAes_round_eq_aesEncryptRound (state roundKey : V128) :
    aesMixColumns (armAesEncrypt state 0) ^^^ roundKey = aesEncryptRound state roundKey := by
  simp [armAesEncrypt, aesEncryptRound]

end CIL.Vector
