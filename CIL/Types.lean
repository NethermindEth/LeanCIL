import Std

/-!
# Values and addresses

The data the interpreter manipulates: evaluation-stack values and the addresses that
memory maps to values.
-/

namespace CIL

abbrev W64 := BitVec 64
abbrev W32 := BitVec 32

/-- Storage shapes admitted by value reinterpretation; lane type does not change bytes. -/
inductive SnapshotShape where
  | aggregate (width : Nat)
  | vector128 | vector256 | vector512
  deriving DecidableEq, Repr

/-- Size of a shape in bytes. -/
def SnapshotShape.width : SnapshotShape → Nat
  | .aggregate width => width
  | .vector128 => 16
  | .vector256 => 32
  | .vector512 => 64

/-- A memory location. The four kinds are disjoint address spaces. -/
inductive Address where
  /-- A byte of caller-provided storage; aggregate references may overlap. -/
  | byte (address : Nat)
  /-- Scalar local `index` of call frame `frame`. -/
  | local (frame index : Nat)
  /-- Byte `offset` of read-only data extracted from the assembly. -/
  | static (bytes : List (BitVec 8)) (offset : Nat)
  /-- Byte `offset` of a private 32-byte vector home; `kind` is 0 for locals, 1 for
      arguments and 2 for construction temporaries. -/
  | home (frame kind index offset : Nat)
  deriving DecidableEq, Repr

/-- An evaluation-stack or memory value. -/
inductive Value where
  /-- Partial value snapshots retain every byte and its initialization bit. -/
  | snapshot (shape : SnapshotShape) (bytes : List (BitVec 8 × Bool))
  /-- A fully initialized value-type aggregate, byte by byte. -/
  | aggregate (bytes : List (BitVec 8))
  | i8 (word : BitVec 8)
  | i64 (word : W64)
  | i32 (word : W32)
  | v128 (bits : BitVec 128)
  /-- A 128-bit vector whose upper half is unspecified. -/
  | v128Low64 (low : W64)
  | v256 (bits : BitVec 256)
  | v512 (bits : BitVec 512)
  | span (address : Address) (length : Nat)
  /-- A managed object, identified by the base of its storage. -/
  | object (id : Nat)
  | ref (address : Address)
  | nullRef
  /-- A value the model does not track; reading it as data is stuck. -/
  | unmodeled
  deriving DecidableEq, Repr

/-- Whether some bits of the value are unspecified and must not be observed. -/
def Value.hasUnspecified : Value → Bool
  | .v128Low64 _ => true
  | _ => false

/-- Whether the value may be read; only `unmodeled` may not. -/
def Value.initialized : Value → Bool
  | .unmodeled => false
  | _ => true

end CIL
