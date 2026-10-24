import CIL.Types
import CIL.IntegerArithmetic
import CIL.Features
import CIL.SIMD.Availability
import CIL.VectorMemory

/-!
# Instructions and methods

`Op` is the instruction set the extractor emits; `Method` is one extracted method body
and `Program` the list a call index refers into.
-/

namespace CIL

/-- Small integer storage types; all extend to the 32-bit evaluation-stack type. -/
inductive NarrowKind where
  | signed8 | unsigned8 | signed16 | unsigned16
  deriving DecidableEq, Repr

/-- Storage size in bytes. -/
def NarrowKind.width : NarrowKind → Nat
  | .signed8 | .unsigned8 => 1
  | .signed16 | .unsigned16 => 2

@[simp] theorem NarrowKind.width_lt (kind : NarrowKind) : kind.width < 2^64 := by
  cases kind <;> decide

/-- Truncates to the storage width, then sign- or zero-extends back to 32 bits. -/
def NarrowKind.extend (kind : NarrowKind) (bits : W32) : W32 :=
  match kind with
  | .signed8 => (bits.setWidth 8).signExtend 32
  | .unsigned8 => (bits.setWidth 8).zeroExtend 32
  | .signed16 => (bits.setWidth 16).signExtend 32
  | .unsigned16 => (bits.setWidth 16).zeroExtend 32

/-- A boolean result already fits every narrow kind, so a narrowed comparison return is unchanged. -/
theorem NarrowKind.extend_ite_one_zero (kind : NarrowKind) (p : Prop) [Decidable p] :
    kind.extend (if p then 1 else 0) = if p then 1 else 0 := by
  cases kind <;> split <;> rfl

/-- The `1#32`/`0#32` literals comparisons produce are not syntactically `1`/`0`, so simp needs this form too. -/
theorem NarrowKind.extend_ite_ofNat_one_zero (kind : NarrowKind) (p : Prop) [Decidable p] :
    kind.extend (if p then 1#32 else 0#32) = if p then 1#32 else 0#32 := by
  cases kind <;> split <;> rfl

#print axioms NarrowKind.extend_ite_one_zero
#print axioms NarrowKind.extend_ite_ofNat_one_zero

/-- Applies an optional narrowing to an `i32`; narrowing anything else is stuck. -/
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
  | byte | word32 | word64 | vector128 | vector256 | vector512 | reference
  deriving DecidableEq, Repr

/-- One instruction. Branch targets and call indices are positions in the method's code
    and in the `Program`. Constructors that `CIL.step` does not execute are handled by the
    checked interpreter in `CIL.Safety`. -/
inductive Op where
  /-- Widen the int32 operand of a metadata-validated mixed native operation. -/
  | nativeBinary (operation : Op)
  | divide (signed remainder : Bool)
  | checkedArithmetic (kind : CheckedBinaryKind) (signed : Bool)
  | checkedConvert (width : Nat) (signed unsignedInput : Bool)
  | nop | neg | gt
  -- Signed and unsigned compare-and-branch; more follow `switch` below.
  | bgt (target : Nat)
  | ble (target : Nat)
  | bleu (target : Nat)
  -- Value-type aggregates and fields, by byte offset and width.
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
  -- Arguments, locals and their vector homes.
  | arg (index : Nat) (narrow : Option NarrowKind := none)
  | vectorArg (index : Nat)
  | vectorArgAddr (index : Nat)
  | local (index : Nat) (narrow : Option NarrowKind := none)
  | vectorLocal (index : Nat)
  | vectorLocalAddr (index : Nat)
  | setVectorLocal (index : Nat)
  | localAddr (index : Nat)
  | setLocal (index : Nat) (narrow : Option NarrowKind := none)
  -- 64-bit lanes of a 256-bit vector.
  | lane (index : Fin 4)
  | laneAddress (index : Fin 4)
  | setLane (index : Fin 4)
  -- Constants, conversions, arithmetic, 64-bit memory access and stack shuffling.
  | const32 (word : W32)
  | const64 (word : W64)
  | convI1 | convI2 | convU2
  | convI8 | convI4 | convU1 | convU4 | convU8 | convU | bnot | add | sub | mul | band | bor | bxor
  | shl | shr | shrUn | lt | ltu | gtu | eq | load64 | store64 | dup | pop
  -- Control flow.
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
  -- Calls and constructors; `argc` values are popped as arguments.
  | call (method : Nat) (argc : Nat)
  | newVector256 (constructor : Nat) (argc : Nat)
  | newAggregate (constructor : Nat) (argc : Nat) (size : Fin (2^64))
  | skipInit | asRef
  /-- Pushes `1` when the method's feature profile has the feature, else `0`. -/
  | feature (id : Feature)
  | intrinsic (operation : Intrinsic) (argc : Nat)
  | memory (operation : MemoryOp)
  | ret (narrow : Option NarrowKind := none)
  /-- Raises an exception of the named type; there are no handlers. -/
  | throw (exception : String)
  | unsupported (description : String)
  deriving DecidableEq, Repr
-- Irreducible: unfolding it while generating the interpreter's equation lemmas exceeds the
-- heartbeat limit. Decide instruction lists with `decide +kernel`.
attribute [irreducible] instDecidableEqOp

/-- The call `method arguments` whose result a static constructor stores in a readonly field. -/
structure StaticInitializer where
  method : Nat
  arguments : List Value
  deriving DecidableEq, Repr

/-- A static field the method reads: its bytes as extracted, and where they came from. -/
structure StaticDescriptor where
  identity : Nat
  fieldName : String
  bytes : List (BitVec 8)
  /-- `some` for a value fixed by its static constructor, `none` for RVA data. -/
  initializer : Option StaticInitializer := none
  assemblyIdentity : String := ""
  deriving DecidableEq, Repr

/-- An extracted method body with the frame layout the interpreter needs. -/
structure Method where
  /-- The hardware features the method was compiled against. -/
  profile : FeatureProfile := FeatureProfile.scalar
  code : List Op
  /-- Initial values of the scalar locals. -/
  locals : List Value
  localKinds : List LocalKind := []
  staticSites : List (Nat × StaticDescriptor) := []
  /-- Locals kept in 256-bit vector homes rather than scalar slots. -/
  vectorLocals : List Nat := []
  opaqueVectorLocals : List Nat := []
  /-- Arguments kept in 256-bit vector homes rather than scalar slots. -/
  vectorArgs : List Nat := []
  parameterHomes : List (Nat × LocalKind) := []
  returnsValue : Bool
  deriving Repr

/-- The methods a call refers to, by index. -/
abbrev Program := List Method

end CIL
