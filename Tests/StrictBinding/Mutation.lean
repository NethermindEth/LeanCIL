import StrictBinding.Image

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

/-- The bytes of an image, read one at a time; empty when the image is malformed. -/
def imageBytes (image : ImageBytes) : List Nat :=
  match ImageView.ofImage image >>= (·.bytes 0 image.length) with
  | .ok bytes => bytes
  | .error _ => []

/-- The little-endian value of `width` bytes at `offset`. -/
def readLittle (bytes : List Nat) (offset width : Nat) : Nat :=
  (List.range width).foldl
    (fun value index => value + bytes.getD (offset + index) 0 * 256 ^ index) 0

/-- The bytes with `width` bytes at `offset` replaced by the little-endian `value`. -/
def writeLittle (bytes : List Nat) (offset width value : Nat) : List Nat :=
  (List.range width).foldl
    (fun bytes index => bytes.set (offset + index) (value / 256 ^ index % 256)) bytes

/-- The bytes with `replacement` written from `offset` on. -/
def writeBytes (bytes : List Nat) (offset : Nat) (replacement : List Nat) : List Nat :=
  replacement.zipIdx.foldl (fun bytes (byte, index) => bytes.set (offset + index) byte) bytes

/-- The bytes with the byte at `index` xor-ed with `mask`. -/
def flipAt (bytes : List Nat) (index mask : Nat) : List Nat :=
  bytes.set index (Nat.xor (bytes.getD index 0) mask)

/-- Whether a check failed with exactly this error. -/
def failsWith {α : Type} (result : Except AuditError α) (error : AuditError) : Bool :=
  match result with
  | .error found => found == error
  | .ok _ => false

end Tests.StrictBinding
