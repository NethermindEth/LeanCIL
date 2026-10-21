import CIL.Types
import CIL.IntegerArithmetic
import CIL.Features
import CIL.SIMD.Availability
import CIL.VectorMemory

namespace CIL

/-- Small integer storage types; all extend to the 32-bit evaluation-stack type. -/
inductive NarrowKind where
  | signed8 | unsigned8 | signed16 | unsigned16
  deriving DecidableEq, Repr

def NarrowKind.width : NarrowKind → Nat
  | .signed8 | .unsigned8 => 1
  | .signed16 | .unsigned16 => 2

@[simp] theorem NarrowKind.width_lt (kind : NarrowKind) : kind.width < 2^64 := by
  cases kind <;> decide

def NarrowKind.extend (kind : NarrowKind) (bits : W32) : W32 :=
  match kind with
  | .signed8 => (bits.setWidth 8).signExtend 32
  | .unsigned8 => (bits.setWidth 8).zeroExtend 32
  | .signed16 => (bits.setWidth 16).signExtend 32
  | .unsigned16 => (bits.setWidth 16).zeroExtend 32

def narrowValue (kind : Option NarrowKind) (value : Value) : Option Value :=
  match kind, value with
  | none, value => some value
  | some kind, .i32 bits => some (.i32 (kind.extend bits))
  | _, _ => none

/-- Physical local storage, retained even when InitLocals is false. Reference
    slots retain managed-reference values rather than numerical addresses. -/
inductive LocalKind where
  | narrow (kind : NarrowKind)
  | aggregate (size : Fin (2^64))
  | byte | word32 | word64 | vector128 | vector256 | reference
  deriving DecidableEq, Repr

inductive Op where
  /-- Widen the int32 operand of a metadata-validated mixed native operation. -/
  | nativeBinary (operation : Op)
  | divide (signed remainder : Bool)
  | checkedArithmetic (kind : CheckedBinaryKind) (signed : Bool)
  | checkedConvert (width : Nat) (signed unsignedInput : Bool)
  | nop | neg | gt
  | bgt (target : Nat)
  | ble (target : Nat)
  | bleu (target : Nat)
  | loadAggregate (size : Nat)
  | copyObject (size : Nat)
  | storeAggregate (size : Nat)
  | initAggregate (size : Nat)
  | loadScalar (width : Nat) (signed : Bool := false)
  | storeScalar (width : Nat)
  | fieldAt (offset width : Nat) (signed : Bool := false)
  | fieldAddress (offset : Nat)
  | setFieldAt (offset width : Nat)
  | aggregateFieldAt (offset size : Nat)
  | setAggregateFieldAt (offset size : Nat)
  | arg (index : Nat) (narrow : Option NarrowKind := none)
  | vectorArg (index : Nat)
  | vectorArgAddr (index : Nat)
  | local (index : Nat) (narrow : Option NarrowKind := none)
  | vectorLocal (index : Nat)
  | vectorLocalAddr (index : Nat)
  | setVectorLocal (index : Nat)
  | localAddr (index : Nat)
  | setLocal (index : Nat) (narrow : Option NarrowKind := none)
  | lane (index : Fin 4)
  | laneAddress (index : Fin 4)
  | setLane (index : Fin 4)
  | const32 (word : W32)
  | const64 (word : W64)
  | convI1 | convI2 | convU2
  | convI8 | convI4 | convU1 | convU4 | convU8 | convU | bnot | add | sub | mul | band | bor | bxor
  | shl | shr | shrUn | lt | ltu | gtu | eq | load64 | store64 | dup | pop
  | branch (target : Nat)
  | switch (targets : List Nat)
  | brzero (target : Nat)
  | brnonzero (target : Nat)
  | bltu (target : Nat)
  | bgeu (target : Nat)
  | bgtu (target : Nat)
  | bge (target : Nat)
  | blt (target : Nat)
  | beq (target : Nat)
  | bne (target : Nat)
  | call (method : Nat) (argc : Nat)
  | newVector256 (constructor : Nat) (argc : Nat)
  | newAggregate (constructor : Nat) (argc : Nat) (size : Fin (2^64))
  | skipInit | asRef
  | feature (id : Feature)
  | intrinsic (operation : Intrinsic) (argc : Nat)
  | memory (operation : MemoryOp)
  | ret (narrow : Option NarrowKind := none)
  /-- Raises an exception of the named type; there are no handlers. -/
  | throw (exception : String)
  | unsupported (description : String)
  deriving Repr

structure StaticDescriptor where
  identity : Nat
  fieldName : String
  bytes : List (BitVec 8)
  deriving DecidableEq, Repr

structure Method where
  profile : FeatureProfile := FeatureProfile.scalar
  code : List Op
  locals : List Value
  localKinds : List LocalKind := []
  staticSites : List (Nat × StaticDescriptor) := []
  vectorLocals : List Nat := []
  vectorArgs : List Nat := []
  parameterHomes : List (Nat × LocalKind) := []
  returnsValue : Bool
  deriving Repr

abbrev Program := List Method

end CIL
