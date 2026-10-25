import CIL.Extraction.LayoutUses
import CIL.Extraction.Lockstep

/-!
# Parameter homes

A parameter that the body stores to or takes the address of is given a home: an extra
local slot appended after the raw locals, because emitted code only ever reads an
argument. `ParameterHomesValid` derives the home set from the raw body and the
reachability mask, and checks that every emitted argument and local instruction uses the
slot that set implies.
-/

namespace CIL.Extraction

/-- Metadata storage types, before native widths and aggregate sizes are lowered. -/
inductive StorageType where
  | field (type : FieldType)
  | reference | vector128 | vector256 | vector512
  | span (width : Nat) (writable : Bool)
  deriving DecidableEq, Repr

/-- One entry per original instruction, including instructions pruned by the profile. -/
inductive ArgumentOp where
  | load (index : Nat)
  | store (index : Nat)
  | address (index : Nat)
  | other
  deriving DecidableEq, Repr

/-- The storage of a method's arguments (`this` first) and locals, and how each raw
    instruction touches arguments. -/
structure RawArguments where
  arguments : List StorageType
  locals : List StorageType
  code : List ArgumentOp
  deriving DecidableEq, Repr

/-- The frame slot kind for a storage type; small integers keep their narrowing and a
    struct takes its computed size, which must be below 2^64. -/
def storageKind (layouts : Array ComputedLayout) : StorageType → Option LocalKind
  | .reference => some .reference
  | .span width writable =>
    if width ∈ [1, 2, 4, 8] then some (.span width writable) else none
  | .vector128 => some .vector128
  | .vector256 => some .vector256
  | .vector512 => some .vector512
  | .field .vector128 => some .vector128
  | .field .vector256 => some .vector256
  | .field .signed8 => some (.narrow .signed8)
  | .field .unsigned8 | .field .boolean => some (.narrow .unsigned8)
  | .field .signed16 => some (.narrow .signed16)
  | .field .unsigned16 | .field .character => some (.narrow .unsigned16)
  | .field .signed32 | .field .unsigned32 => some .word32
  | .field .signed64 | .field .unsigned64 | .field .nativeInt | .field .nativeUInt => some .word64
  | .field (.aggregate index) => do
    let layout ← layouts[index]?
    if bounded : layout.layout.size < 2^64 then
      return .aggregate ⟨layout.layout.size, bounded⟩
    else none

/-- Derive the sorted, duplicate-free home set from the complete raw body. -/
def requiredHomeIndices (raw : RawArguments) (reachable : List Bool) : List Nat :=
  (List.range raw.arguments.length).filter fun index =>
    (raw.code.zip reachable).any fun (operation, live) => live && match operation with
      | .store argument | .address argument => argument == index
      | _ => false

/-- Each homed argument index with the slot kind of its home, in argument order. -/
def expectedHomes (layouts : Array ComputedLayout) (raw : RawArguments)
    (reachable : List Bool) : Option (List (Nat × LocalKind)) :=
  (requiredHomeIndices raw reachable).mapM fun index => do
    let type ← raw.arguments[index]?
    return (index, ← storageKind layouts type)

/-- The narrowing a load of a small-integer argument applies. -/
private def argumentNarrow : StorageType → Option NarrowKind
  | .field .signed8 => some .signed8
  | .field .unsigned8 | .field .boolean => some .unsigned8
  | .field .signed16 => some .signed16
  | .field .unsigned16 | .field .character => some .unsigned16
  | _ => none

/-- The local slot of argument `index`'s home, if it has one: homes follow the raw
    locals in home-set order. -/
private def homeSlot (raw : RawArguments) (homes : List Nat) (index : Nat) : Option Nat :=
  if index ∈ homes then some (raw.locals.length + homes.idxOf index) else none

/-- Check one argument instruction against a precomputed home set; hidden accesses
    to appended home slots are rejected. -/
def validateArgumentOpIn (raw : RawArguments) (homes : List Nat)
    (operation : ArgumentOp) (live : Bool) (emitted : Op) : Bool :=
  if !live then match emitted with | .unsupported _ => true | _ => false
  else match operation with
  | .load index => (do
      let type ← raw.arguments[index]?
      match homeSlot raw homes index, emitted with
      | some slot, .local actual narrow => return actual == slot && narrow.isNone
      | none, .arg actual narrow => return actual == index && narrow == argumentNarrow type
      | _, _ => return false).getD false
  | .store index => (do
      let _ ← raw.arguments[index]?
      let slot ← homeSlot raw homes index
      match emitted with
      | .setLocal actual narrow => return actual == slot && narrow.isNone
      | _ => return false).getD false
  | .address index => (do
      let type ← raw.arguments[index]?
      if type == StorageType.reference then return false
      let slot ← homeSlot raw homes index
      match emitted with
      | .localAddr actual => return actual == slot
      | .local actual none => return actual == slot && match type with
          | .span .. => true | _ => false
      | _ => return false).getD false
  | .other => match emitted with
      | .arg .. | .vectorArg .. | .vectorArgAddr .. => false
      | .local index _ | .setLocal index _ | .localAddr index
      | .vectorLocal index | .vectorLocalAddr index | .setVectorLocal index =>
        index < raw.locals.length
      | _ => true

/-- `validateArgumentOpIn` with the home set derived from the body. -/
def validateArgumentOp (raw : RawArguments) (reachable : List Bool) :
    ArgumentOp → Bool → Op → Bool :=
  validateArgumentOpIn raw (requiredHomeIndices raw reachable)

/-- A complete mapping check, not a list of optional argument-use claims. -/
def ParameterHomesValid (layouts : Array ComputedLayout) (raw : RawArguments)
    (reachable : List Bool) (method : Method) : Prop :=
  reachable.length = raw.code.length ∧
  method.code.length = raw.code.length ∧
  raw.locals.mapM (storageKind layouts) = some method.localKinds ∧
  method.locals.length = raw.locals.length ∧
  expectedHomes layouts raw reachable = some method.parameterHomes ∧
  all3 (validateArgumentOpIn raw (requiredHomeIndices raw reachable)) raw.code reachable
    method.code = true

instance (layouts : Array ComputedLayout) (raw : RawArguments)
    (reachable : List Bool) (method : Method) :
    Decidable (ParameterHomesValid layouts raw reachable method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- `ParameterHomesValid` as a Boolean, for checking by evaluation. -/
def validateParameterHomes (layouts : Array ComputedLayout) (raw : RawArguments)
    (reachable : List Bool) (method : Method) : Bool :=
  decide (ParameterHomesValid layouts raw reachable method)

theorem validateParameterHomes_sound {layouts : Array ComputedLayout} {raw : RawArguments}
    {reachable : List Bool} {method : Method}
    (checked : validateParameterHomes layouts raw reachable method = true) :
    ParameterHomesValid layouts raw reachable method := of_decide_eq_true checked

theorem validated_parameter_homes {layouts : Array ComputedLayout} {raw : RawArguments}
    {reachable : List Bool} {method : Method}
    (valid : ParameterHomesValid layouts raw reachable method) :
    expectedHomes layouts raw reachable = some method.parameterHomes := valid.2.2.2.2.1

/-- Every emitted instruction passes the argument check at its pc. -/
theorem validated_argument_access {layouts : Array ComputedLayout} {raw : RawArguments}
    {reachable : List Bool} {method : Method}
    (valid : ParameterHomesValid layouts raw reachable method)
    (pc : Fin raw.code.length) (operation : ArgumentOp) (live : Bool) (emitted : Op)
    (rawAt : raw.code[pc.val]? = some operation) (reachableAt : reachable[pc.val]? = some live)
    (emittedAt : method.code[pc.val]? = some emitted) :
    validateArgumentOp raw reachable operation live emitted = true := by
  exact all3_at valid.2.2.2.2.2 rawAt reachableAt emittedAt

/-- Once a parameter has a home, loading its original argument slot is rejected. -/
theorem home_load_rejects_original_arg (raw : RawArguments) (reachable : List Bool)
    (index actual : Nat) (narrow : Option NarrowKind)
    (home : index ∈ requiredHomeIndices raw reachable) :
    validateArgumentOp raw reachable (.load index) true (.arg actual narrow) = false := by
  cases found : raw.arguments[index]? <;>
    simp [validateArgumentOp, validateArgumentOpIn, homeSlot, home, found]

end CIL.Extraction
