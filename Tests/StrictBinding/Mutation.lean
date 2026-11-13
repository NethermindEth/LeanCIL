import StrictBinding.Image

/-!
# Strict binding tests: mutations

Helpers that change one byte of an image or inspect the error a check gives, shared by the tests
that reject a changed file.
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

/-- Whether a check failed with exactly this error. -/
def failsWith {α : Type} (result : Except AuditError α) (error : AuditError) : Bool :=
  match result with
  | .error found => found == error
  | .ok _ => false

end Tests.StrictBinding
