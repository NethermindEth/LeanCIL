import CIL.Types

/-!
# Memory

Memory is a total map from addresses to optional values. Multi-byte numbers are stored
little-endian, one `i8` value per byte address.
-/

namespace CIL

abbrev Memory := Address → Option Value

/-- Memory with `address` now holding `value`. -/
def write (memory : Memory) (address : Address) (value : Value) : Memory :=
  fun other => if other = address then some value else memory other

/-- The little-endian number in `width` caller bytes from `base`. Caller storage may be
    referenced through partially overlapping aggregates; locals live in a separate space. -/
def readBytes (memory : Memory) (base : Nat) : (width : Nat) → Option Nat
  | 0 => some 0
  | width + 1 => do
    let .i8 low ← memory (.byte base) | none
    let high ← readBytes memory (base + 1) width
    return low.toNat + 256 * high

/-- Stores `value` little-endian in `width` caller bytes from `base`. -/
def writeBytes (memory : Memory) (base : Nat) (value : Nat) : (width : Nat) → Memory
  | 0 => memory
  | width + 1 => writeBytes (write memory (.byte base) (.i8 (BitVec.ofNat 8 value)))
      (base + 1) (value / 256) width

/-- The little-endian number at `offset` in read-only data. It does not depend on memory,
    and no store can change it. -/
def readStaticBytes (bytes : List (BitVec 8)) (offset : Nat) : (width : Nat) → Option Nat
  | 0 => some 0
  | width + 1 => do
    let low ← bytes[offset]?
    let high ← readStaticBytes bytes (offset + 1) width
    return low.toNat + 256 * high

/-- The little-endian number at `offset` in a private vector home. -/
def readHomeBytes (memory : Memory) (frame kind index offset : Nat) : (width : Nat) → Option Nat
  | 0 => some 0
  | width + 1 => do
    let .i8 low ← memory (.home frame kind index offset) | none
    let high ← readHomeBytes memory frame kind index (offset + 1) width
    return low.toNat + 256 * high

/-- Stores `value` little-endian at `offset` in a private vector home. -/
def writeHomeBytes (memory : Memory) (frame kind index offset value : Nat) : (width : Nat) → Memory
  | 0 => memory
  | width + 1 =>
    writeHomeBytes (write memory (.home frame kind index offset) (.i8 (BitVec.ofNat 8 value)))
      frame kind index (offset + 1) (value / 256) width

/-- Reads a 64-bit word. A local must already hold an `i64`; a home read must stay
    within its 32 bytes. -/
def read64 (memory : Memory) : Address → Option Value
  | .byte base => do return .i64 (BitVec.ofNat 64 (← readBytes memory base 8))
  | .local frame index => do
    let .i64 w ← memory (.local frame index) | none
    return .i64 w
  | .static bytes offset => do
    return .i64 (BitVec.ofNat 64 (← readStaticBytes bytes offset 8))
  | .home frame kind index offset => do
    if offset + 8 ≤ 32 then
      return .i64 (BitVec.ofNat 64 (← readHomeBytes memory frame kind index offset 8))
    else none

/-- Writes a 64-bit word. Read-only data cannot be written; a home write must stay
    within its 32 bytes. -/
def write64 (memory : Memory) (address : Address) (word : W64) : Option Memory :=
  match address with
  | .byte base => some (writeBytes memory base word.toNat 8)
  | .local frame index => some (write memory (.local frame index) (.i64 word))
  | .static _ _ => none
  | .home frame kind index offset =>
    if offset + 8 ≤ 32 then some (writeHomeBytes memory frame kind index offset word.toNat 8) else none

end CIL
