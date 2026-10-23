import CIL.ImportMetadata

/-! Import slots: methods of another assembly that an extraction calls without a body. -/

namespace CIL

/-- Slot `j` is method index `program.length + j`; a call there must match this identity and arity. -/
structure ImportSlot where
  identity : String
  closureDigest : String
  parameterCount : Nat
  hasThis : Bool
  returnsValue : Bool
  signature : Option Extraction.ImportSignature := none
  layouts : Extraction.ImportLayoutCatalog := {}
  deriving DecidableEq, Repr

end CIL
