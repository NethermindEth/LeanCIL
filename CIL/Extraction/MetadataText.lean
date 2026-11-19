import Lean

/-!
# UTF-8 metadata literals

Checked matchers compare long assembly and type names by byte. A literal keeps its bytes in
the definition, and the source string supplies the kernel's UTF-8 proof for those exact bytes.
-/

namespace CIL.Extraction

/-- A byte-backed metadata spelling definitionally equal to the source string. -/
macro "metadata_text% " spelling:str : term => do
  let bytes : Array Lean.Term := spelling.getString.toByteArray.data.map fun byte =>
    ⟨Lean.Syntax.mkNumLit (toString byte.toNat)⟩
  `(({ toByteArray := ⟨#[$[$bytes],*]⟩, isValidUTF8 := ($spelling).isValidUTF8 } : String))

end CIL.Extraction
