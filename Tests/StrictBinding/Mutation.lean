import StrictBinding.Image
import CIL.Extraction.FixedDigits

/-!
# Strict binding tests: mutations

Helpers that read or change the bytes of an image or of carried metadata and inspect the error a
check gives, shared by the tests that reject a changed file or a changed claim.
-/

namespace Tests.StrictBinding

open _root_.StrictBinding

/-- The image with the byte at `offset` xor-ed with `mask`. -/
def flipByte (image : ImageBytes) (offset mask : Nat) : ImageBytes :=
  let rec flipIn : List (List Nat) → Nat → List (List Nat)
    | [], _ => []
    | page :: rest, chunk =>
      if chunk < page.length then
        let flipped := Nat.xor (page.getD chunk 0) (mask * 2 ^ (8 * (63 - offset % 64)))
        page.set chunk flipped :: rest
      else page :: flipIn rest (chunk - page.length)
  { image with pages := flipIn image.pages (offset / 64) }

/-- The image with several bytes changed: each `(offset, mask)` xor-ed in turn. -/
def flipBytes (image : ImageBytes) (changes : List (Nat × Nat)) : ImageBytes :=
  changes.foldl (fun changed (offset, mask) => flipByte changed offset mask) image

/-- The bytes of a well-formed image in file order, without the last chunk's padding. -/
def imageBytes (image : ImageBytes) : List Nat :=
  if image.wellFormed then
    (image.chunks.foldr (CIL.Extraction.fixedDigitsWithin 8 64 64) []).take image.length
  else []

/-- The little-endian value of `width` bytes at `offset`. -/
def readLittle (bytes : List Nat) (offset width : Nat) : Nat :=
  (List.range width).foldl
    (fun value index => value + bytes.getD (offset + index) 0 * 256 ^ index) 0

/-- The bytes with `replacement` written from `offset` up to the end of the input. -/
def writeBytes : List Nat → Nat → List Nat → List Nat
  | bytes, _, [] => bytes
  | [], _, _ => []
  | _ :: rest, 0, byte :: more => byte :: writeBytes rest 0 more
  | byte :: rest, offset + 1, replacement => byte :: writeBytes rest offset replacement

/-- The bytes with `width` bytes at `offset` replaced by the little-endian `value`. -/
def writeLittle (bytes : List Nat) (offset width value : Nat) : List Nat :=
  writeBytes bytes offset ((List.range width).map fun index => value / 256 ^ index % 256)

/-- The bytes with the byte at `index` xor-ed with `mask`. -/
def flipAt (bytes : List Nat) (index mask : Nat) : List Nat :=
  bytes.set index (Nat.xor (bytes.getD index 0) mask)

/-- Whether a check failed with exactly this error. -/
def failsWith {α : Type} (result : Except AuditError α) (error : AuditError) : Bool :=
  match result with
  | .error found => found == error
  | .ok _ => false

end Tests.StrictBinding
