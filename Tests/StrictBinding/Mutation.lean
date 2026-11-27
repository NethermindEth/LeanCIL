import StrictBinding.Image
import CIL.Extraction.FixedDigits

/-!
# Strict binding tests: mutations

Helpers that read or change the bytes of an image or of carried metadata and inspect the error a
check gives, shared by the tests that reject a changed file or a changed claim.
-/

namespace Tests.StrictBinding

open _root_.StrictBinding

/-- Apply a change to the chunk containing the byte offset. -/
private def modifyChunk (image : ImageBytes) (offset : Nat) (change : Nat → Nat) : ImageBytes :=
  let rec update : List (List Nat) → Nat → List (List Nat)
    | [], _ => []
    | page :: rest, chunk =>
      if chunk < page.length then page.modify chunk change :: rest
      else page :: update rest (chunk - page.length)
  { image with pages := update image.pages (offset / 64) }

/-- The position of a byte within a big-endian 64-byte chunk, in bits. -/
private def byteShift (offset : Nat) : Nat := 8 * (63 - offset % 64)

/-- The image with the byte at `offset` xor-ed with `mask`. -/
def flipByte (image : ImageBytes) (offset mask : Nat) : ImageBytes :=
  modifyChunk image offset (· ^^^ (mask <<< byteShift offset))

/-- Write the replacement bytes into their image chunks, stopping at the end of the file. -/
def writeImageBytes (image : ImageBytes) (offset : Nat) (replacement : List Nat) : ImageBytes :=
  match replacement with
  | [] => image
  | byte :: rest =>
    if offset ≥ image.length then image
    else
      let shift := byteShift offset
      let updated := modifyChunk image offset fun chunk =>
        let oldByte := (chunk >>> shift) % 256
        chunk ^^^ ((oldByte ^^^ (byte % 256)) <<< shift)
      writeImageBytes updated (offset + 1) rest

/-- A write can cross a page boundary and leaves the padding after the last byte unchanged. -/
private theorem write_across_pages :
    writeImageBytes ⟨65, [[0], [0]]⟩ 63 [1, 2, 3] = ⟨65, [[1], [2 <<< 504]]⟩ := rfl
#print axioms write_across_pages

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
