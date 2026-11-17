import CIL.Identity

/-!
# Byte literals

The extractor writes a list of bytes, such as a method body, a metadata row or a UTF-8 name, as
`fixedBytes count code`: the byte count and one number holding the bytes big-endian. The code of
a list of at most 256 bytes is one hexadecimal numeral. A longer list's code joins numerals of at
most 256 bytes with `Nat.lor` and `Nat.shiftLeft`, since the elaborator parses a numeral in time
quadratic in its digits, and the kernel keys its caches by a hash that reads only the low 64 bits
of a numeral, so separate numerals with equal last bytes would collide there. A numeral costs the
elaborator a few allocations, where a list literal costs a numeral and a cons per byte. The kernel
recovers the list by splitting the code in halves down to words of at most eight digits, so a
decode takes a linear number of steps. `fixedDigitsWithin` splits a code into digits of any width,
and `fixedDigitsWithin_eq_fixedDigits` ties it to the digit lists of `CIL.Identity`.
-/

namespace CIL.Extraction
open CIL

/-- The most digits the decoder reads from one word without splitting it further. -/
def wordDigitCount : Nat := 8

/-- The low `count` digits of `width` bits of `word`, most significant first, followed by
    `tail`. -/
def wordDigits (width : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, tail => tail
  | count + 1, word, tail =>
    wordDigits width count (Nat.shiftRight word width)
      (Nat.mod word (Nat.shiftLeft 1 width) :: tail)

/-- The low `count` digits of `width` bits of `code`, most significant first, followed by
    `tail`; each of the `depth` levels halves a code longer than a word. -/
def fixedDigitsWithin (width : Nat) : Nat → Nat → Nat → List Nat → List Nat
  | 0, count, code, tail => wordDigits width count code tail
  | depth + 1, count, code, tail =>
    bif Nat.ble count wordDigitCount then wordDigits width count code tail
    else
      let low := Nat.div count 2
      let lowBits := Nat.mul width low
      fixedDigitsWithin width depth (Nat.sub count low) (Nat.shiftRight code lowBits)
        (fixedDigitsWithin width depth low (Nat.mod code (Nat.shiftLeft 1 lowBits)) tail)

/-- The `count` bytes that `code` holds big-endian, as the extractor writes a byte list. -/
def fixedBytes (count code : Nat) : List Nat := fixedDigitsWithin 8 count count code []

/-- Reading the digits of a word back appends the word to the code read. -/
theorem wordDigits_spec (width : Nat) : ∀ (count word : Nat) (tail : List Nat) (start : Nat),
    word < (2 ^ width) ^ count →
      radixCode? (2 ^ width) (wordDigits width count word tail) start =
        radixCode? (2 ^ width) tail (start * (2 ^ width) ^ count + word)
  | 0, word, tail, start, bounded => by
    have zero : word = 0 := by simpa using bounded
    subst zero
    simp [wordDigits]
  | count + 1, word, tail, start, bounded => by
    have quotient : Nat.shiftRight word width = word / 2 ^ width :=
      Nat.shiftRight_eq_div_pow word width
    have remainder : Nat.mod word (Nat.shiftLeft 1 width) = word % 2 ^ width := by
      show word % (1 <<< width) = _
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    have upper : word / 2 ^ width < (2 ^ width) ^ count := by
      rw [Nat.pow_succ] at bounded
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact bounded)
    have small : word % 2 ^ width < 2 ^ width := Nat.mod_lt word (Nat.two_pow_pos width)
    rw [wordDigits, quotient, remainder,
      wordDigits_spec width count (word / 2 ^ width) _ start upper]
    simp only [radixCode?, small, ↓reduceIte]
    congr 1
    have joined := Nat.div_add_mod word (2 ^ width)
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    generalize 2 ^ width = base at joined ⊢
    generalize start * base ^ count = scaled
    rw [Nat.add_mul, Nat.mul_comm (word / base)]
    omega

#print axioms wordDigits_spec

/-- Reading the split digits back appends the code to the code read, at every depth. -/
theorem fixedDigitsWithin_spec (width : Nat) :
    ∀ (depth count code : Nat) (tail : List Nat) (start : Nat),
    code < (2 ^ width) ^ count →
      radixCode? (2 ^ width) (fixedDigitsWithin width depth count code tail) start =
        radixCode? (2 ^ width) tail (start * (2 ^ width) ^ count + code)
  | 0, count, code, tail, start, bounded => by
    rw [fixedDigitsWithin]
    exact wordDigits_spec width count code tail start bounded
  | depth + 1, count, code, tail, start, bounded => by
    rw [fixedDigitsWithin]
    cases Nat.ble count wordDigitCount
    · have power : 2 ^ (width * (count / 2)) = (2 ^ width) ^ (count / 2) := Nat.pow_mul ..
      have positive : 0 < (2 ^ width) ^ (count / 2) := Nat.pow_pos (Nat.two_pow_pos width)
      have splitCount : count - count / 2 + count / 2 = count := by omega
      have upper : code / (2 ^ width) ^ (count / 2) < (2 ^ width) ^ (count - count / 2) := by
        apply (Nat.div_lt_iff_lt_mul positive).mpr
        rw [← Nat.pow_add, splitCount]
        exact bounded
      have lower : code % (2 ^ width) ^ (count / 2) < (2 ^ width) ^ (count / 2) :=
        Nat.mod_lt _ positive
      change radixCode? (2 ^ width) (fixedDigitsWithin width depth (count - count / 2)
        (code >>> (width * (count / 2)))
        (fixedDigitsWithin width depth (count / 2) (code % (1 <<< (width * (count / 2))))
          tail)) start = _
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul, power,
        fixedDigitsWithin_spec width depth _ _ _ start upper,
        fixedDigitsWithin_spec width depth _ _ _ _ lower]
      congr 1
      have joined := Nat.div_add_mod code ((2 ^ width) ^ (count / 2))
      rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, splitCount]
      generalize (2 ^ width) ^ (count / 2) = scale at joined
      generalize start * (2 ^ width) ^ count = scaled
      rw [Nat.mul_comm] at joined
      omega
    · exact wordDigits_spec width count code tail start bounded

#print axioms fixedDigitsWithin_spec

/-- A code below `(2 ^ width) ^ count` splits into the `count` digits of `width` bits that
    `fixedDigits` gives; `fixedBytes count code` is the case of eight bits. -/
theorem fixedDigitsWithin_eq_fixedDigits (width count code : Nat) (wide : 0 < width)
    (bounded : code < (2 ^ width) ^ count) :
    fixedDigitsWithin width count count code [] = fixedDigits width count code [] := by
  have decoded := fixedDigitsWithin_spec width count count code [] 1 bounded
  have digits := fixedDigits_spec width count code bounded [] 1
  simp only [radixCode?] at decoded digits
  exact radixCode?_injective (Nat.le_self_pow (by omega) 2) decoded digits

#print axioms fixedDigitsWithin_eq_fixedDigits

end CIL.Extraction
