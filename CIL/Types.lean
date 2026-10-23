import Std

namespace CIL

abbrev W64 := BitVec 64
abbrev W32 := BitVec 32

/-- Storage shapes admitted by value reinterpretation; lane type does not change bytes. -/
inductive SnapshotShape where
  | aggregate (width : Nat)
  | vector128 | vector256 | vector512
  deriving DecidableEq, Repr

def SnapshotShape.width : SnapshotShape → Nat
  | .aggregate width => width
  | .vector128 => 16
  | .vector256 => 32
  | .vector512 => 64

inductive Address where
  | byte (address : Nat)
  | local (frame index : Nat)
  | static (bytes : List (BitVec 8)) (offset : Nat)
  | home (frame kind index offset : Nat)
  deriving DecidableEq, Repr

inductive Value where
  /-- Partial value snapshots retain every byte and its initialization bit. -/
  | snapshot (shape : SnapshotShape) (bytes : List (BitVec 8 × Bool))
  | aggregate (bytes : List (BitVec 8))
  | i8 (word : BitVec 8)
  | i64 (word : W64)
  | i32 (word : W32)
  | v128 (bits : BitVec 128)
  | v128Low64 (low : W64)
  | v256 (bits : BitVec 256)
  | v512 (bits : BitVec 512)
  | span (address : Address) (length : Nat)
  | object (id : Nat)
  | ref (address : Address)
  | nullRef
  | unmodeled
  deriving DecidableEq, Repr

def Value.hasUnspecified : Value → Bool
  | .v128Low64 _ => true
  | _ => false

def Value.initialized : Value → Bool
  | .unmodeled => false
  | _ => true

end CIL
