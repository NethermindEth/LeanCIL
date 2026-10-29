import Std

/-! # Reference-free array element types shared by extraction and checked storage -/

namespace CIL

/-- The eight CLI integer encodings permitted as enum backing storage. -/
inductive EnumStorage where
  | signed8 | unsigned8 | signed16 | unsigned16 | signed32 | unsigned32
  | signed64 | unsigned64
  deriving DecidableEq, Repr

/-- Every enum has one of the four supported nonzero integer storage widths. -/
def EnumStorage.width : EnumStorage → Nat
  | .signed8 | .unsigned8 => 1
  | .signed16 | .unsigned16 => 2
  | .signed32 | .unsigned32 => 4
  | .signed64 | .unsigned64 => 8

/-- Only narrow signed enum loads need sign extension to the evaluation-stack width. -/
def EnumStorage.signed : EnumStorage → Bool
  | .signed8 | .signed16 => true
  | _ => false

/-- Exact reference-free array element identity and physical storage shape. -/
inductive ArrayElement where
  | signed8 | unsigned8 | signed16 | unsigned16 | signed32 | unsigned32
  | signed64 | unsigned64 | nativeInt | nativeUInt | boolean | character
  | enumeration (identity : String) (storage : EnumStorage)
  | aggregate (identity : String) (size : Nat)
  | vector (identity : String) (size : Nat)
  deriving DecidableEq, Repr

/-- Storage width on the admitted 64-bit runtime profiles. -/
def ArrayElement.width : ArrayElement → Nat
  | .signed8 | .unsigned8 | .boolean => 1
  | .signed16 | .unsigned16 | .character => 2
  | .signed32 | .unsigned32 => 4
  | .signed64 | .unsigned64 | .nativeInt | .nativeUInt => 8
  | .enumeration _ storage => storage.width
  | .aggregate _ size | .vector _ size => size

/-- Narrow loads sign-extend signed integer and enum storage. -/
def ArrayElement.signed : ArrayElement → Bool
  | .signed8 | .signed16 => true
  | .enumeration _ storage => storage.signed
  | _ => false

/-- Native elements keep their stack kind distinct from fixed-width int64 elements. -/
def ArrayElement.native : ArrayElement → Bool
  | .nativeInt | .nativeUInt => true
  | _ => false

/-- Aggregate widths come from layout evidence, separately from exact metadata identity. -/
def ArrayElement.metadata : ArrayElement → ArrayElement
  | .aggregate identity _ => .aggregate identity 0
  | element => element

end CIL
