/-!
# Fixed-width digit lists

The splitter that turns one number into its digits of a fixed width, which the extractor's byte
lists (`fixedBytes`) and the pages of a strict binding image (`fixedDigitsWithin 512`) are
written through. The module imports only the prelude, so a generated module that needs only the
splitter, such as an image module, does not load `Lean`; its specifications are in
[ByteLiterals](ByteLiterals.lean).
-/

namespace CIL.Extraction

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

end CIL.Extraction
