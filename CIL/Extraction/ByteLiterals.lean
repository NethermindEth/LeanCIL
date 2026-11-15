import CIL.Identity

/-!
# Byte literals

The extractor writes a list of bytes, such as a method body, a metadata row or a UTF-8 name, as
`fixedBytes count code`: the byte count and one hexadecimal numeral holding the bytes big-endian.
A list longer than 256 bytes is several such literals joined by `++`, since the elaborator parses
a numeral in time quadratic in its digits. A numeral costs the elaborator a few allocations, where
a list literal costs a numeral and a cons per byte. The kernel recovers the list by splitting the
code in halves down to words of at most eight bytes, so a decode takes a linear number of steps
on numerals of at most 256 bytes, and `fixedBytes_eq_fixedDigits` ties it to the digit lists of
`CIL.Identity`.
-/

namespace CIL.Extraction
open CIL

/-- The most bytes the decoder reads from one word without splitting it further. -/
def wordBytes : Nat := 8

/-- The low `count` bytes of `word`, most significant first, followed by `tail`. -/
def wordDigits : Nat → Nat → List Nat → List Nat
  | 0, _, tail => tail
  | count + 1, word, tail =>
    wordDigits count (Nat.shiftRight word 8) (Nat.mod word 256 :: tail)

/-- The low `count` bytes of `code`, most significant first, followed by `tail`; each of the
    `depth` levels halves a code longer than a word. -/
def fixedBytesWithin : Nat → Nat → Nat → List Nat → List Nat
  | 0, count, code, tail => wordDigits count code tail
  | depth + 1, count, code, tail =>
    bif Nat.ble count wordBytes then wordDigits count code tail
    else
      let low := Nat.div count 2
      let lowBits := Nat.mul 8 low
      fixedBytesWithin depth (Nat.sub count low) (Nat.shiftRight code lowBits)
        (fixedBytesWithin depth low (Nat.mod code (Nat.shiftLeft 1 lowBits)) tail)

/-- The `count` bytes that `code` holds big-endian, as the extractor writes a byte list. -/
def fixedBytes (count code : Nat) : List Nat := fixedBytesWithin count count code []

/-- Reading the bytes of a word back as base-256 digits appends the word to the code read. -/
theorem wordDigits_spec : ∀ (count word : Nat) (tail : List Nat) (start : Nat),
    word < 256 ^ count →
      radixCode? 256 (wordDigits count word tail) start =
        radixCode? 256 tail (start * 256 ^ count + word)
  | 0, word, tail, start, bounded => by
    have zero : word = 0 := by simpa using bounded
    subst zero
    simp [wordDigits]
  | count + 1, word, tail, start, bounded => by
    have quotient : Nat.shiftRight word 8 = word / 256 := by
      show word >>> 8 = _
      rw [Nat.shiftRight_eq_div_pow]
    have remainder : Nat.mod word 256 = word % 256 := rfl
    have upper : word / 256 < 256 ^ count := by
      rw [Nat.pow_succ] at bounded
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact bounded)
    have small : word % 256 < 256 := Nat.mod_lt word (by decide)
    rw [wordDigits, quotient, remainder, wordDigits_spec count (word / 256) _ start upper]
    simp only [radixCode?, small, ↓reduceIte]
    congr 1
    have joined := Nat.div_add_mod word 256
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    generalize start * 256 ^ count = scaled
    omega

#print axioms wordDigits_spec

/-- Reading the decoded bytes back as base-256 digits appends the code to the code read, at
    every depth. -/
theorem fixedBytesWithin_spec : ∀ (depth count code : Nat) (tail : List Nat) (start : Nat),
    code < 256 ^ count →
      radixCode? 256 (fixedBytesWithin depth count code tail) start =
        radixCode? 256 tail (start * 256 ^ count + code)
  | 0, count, code, tail, start, bounded => by
    rw [fixedBytesWithin]
    exact wordDigits_spec count code tail start bounded
  | depth + 1, count, code, tail, start, bounded => by
    rw [fixedBytesWithin]
    cases Nat.ble count wordBytes
    · have power : 2 ^ (8 * (count / 2)) = 256 ^ (count / 2) := by rw [Nat.pow_mul]
      have positive : 0 < 256 ^ (count / 2) := Nat.pow_pos (by decide)
      have splitCount : count - count / 2 + count / 2 = count := by omega
      have upper : code / 256 ^ (count / 2) < 256 ^ (count - count / 2) := by
        apply (Nat.div_lt_iff_lt_mul positive).mpr
        rw [← Nat.pow_add, splitCount]
        exact bounded
      have lower : code % 256 ^ (count / 2) < 256 ^ (count / 2) := Nat.mod_lt _ positive
      change radixCode? 256 (fixedBytesWithin depth (count - count / 2)
        (code >>> (8 * (count / 2)))
        (fixedBytesWithin depth (count / 2) (code % (1 <<< (8 * (count / 2)))) tail)) start = _
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul, power,
        fixedBytesWithin_spec depth _ _ _ start upper,
        fixedBytesWithin_spec depth _ _ _ _ lower]
      congr 1
      have joined := Nat.div_add_mod code (256 ^ (count / 2))
      rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, splitCount]
      generalize 256 ^ (count / 2) = scale at joined
      generalize start * 256 ^ count = scaled
      rw [Nat.mul_comm] at joined
      omega
    · exact wordDigits_spec count code tail start bounded

#print axioms fixedBytesWithin_spec

/-- A code below `256 ^ count` decodes to the `count` base-256 digits `fixedDigits` gives. -/
theorem fixedBytes_eq_fixedDigits (count code : Nat) (bounded : code < 256 ^ count) :
    fixedBytes count code = fixedDigits 8 count code [] := by
  have decoded := fixedBytesWithin_spec count count code [] 1 bounded
  have digits := fixedDigits_spec 8 count code (by simpa using bounded) [] 1
  simp only [radixCode?] at decoded digits
  exact radixCode?_injective (base := 256) (by decide) decoded (by simpa using digits)

#print axioms fixedBytes_eq_fixedDigits

end CIL.Extraction
