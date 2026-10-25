import Std

/-! # Primitive array element types shared by extraction and checked storage -/

namespace CIL

/-- Primitive integer array identity, retained separately from its physical byte width. -/
inductive ArrayElement where
  | signed8 | unsigned8 | signed16 | unsigned16 | signed32 | unsigned32
  | signed64 | unsigned64 | nativeInt | nativeUInt | boolean | character
  deriving DecidableEq, Repr

/-- Storage width on the admitted 64-bit runtime profiles. -/
def ArrayElement.width : ArrayElement → Nat
  | .signed8 | .unsigned8 | .boolean => 1
  | .signed16 | .unsigned16 | .character => 2
  | .signed32 | .unsigned32 => 4
  | .signed64 | .unsigned64 | .nativeInt | .nativeUInt => 8

/-- Native elements keep their stack kind distinct from fixed-width int64 elements. -/
def ArrayElement.native : ArrayElement → Bool
  | .nativeInt | .nativeUInt => true
  | _ => false

end CIL
