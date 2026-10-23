import CIL.Extraction.LayoutUses
import CIL.Extraction.Lockstep

namespace CIL.Extraction

/-- Metadata storage types, before native widths and aggregate sizes are lowered. -/
inductive StorageType where
  | field (type : FieldType)
  | reference | vector128 | vector256 | vector512
  deriving DecidableEq, Repr

/-- One entry per original instruction, including instructions pruned by the profile. -/
inductive ArgumentOp where
  | load (index : Nat)
  | store (index : Nat)
  | address (index : Nat)
  | other
  deriving DecidableEq, Repr

structure RawArguments where
  arguments : List StorageType
  locals : List StorageType
  code : List ArgumentOp
  deriving DecidableEq, Repr

def storageKind (layouts : Array ComputedLayout) : StorageType → Option LocalKind
  | .reference => some .reference
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

def expectedHomes (layouts : Array ComputedLayout) (raw : RawArguments)
    (reachable : List Bool) : Option (List (Nat × LocalKind)) :=
  (requiredHomeIndices raw reachable).mapM fun index => do
    let type ← raw.arguments[index]?
    return (index, ← storageKind layouts type)

private def argumentNarrow : StorageType → Option NarrowKind
  | .field .signed8 => some .signed8
  | .field .unsigned8 | .field .boolean => some .unsigned8
  | .field .signed16 => some .signed16
  | .field .unsigned16 | .field .character => some .unsigned16
  | _ => none

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
      | _ => return false).getD false
  | .other => match emitted with
      | .arg .. | .vectorArg .. | .vectorArgAddr .. => false
      | .local index _ | .setLocal index _ | .localAddr index
      | .vectorLocal index | .vectorLocalAddr index | .setVectorLocal index => index < raw.locals.length
      | _ => true

def validateArgumentOp (raw : RawArguments) (reachable : List Bool) : ArgumentOp → Bool → Op → Bool :=
  validateArgumentOpIn raw (requiredHomeIndices raw reachable)

/-- A complete mapping check, not a list of optional argument-use claims. -/
def ParameterHomesValid (layouts : Array ComputedLayout) (raw : RawArguments)
    (reachable : List Bool) (method : Method) : Prop :=
  reachable.length = raw.code.length ∧
  method.code.length = raw.code.length ∧
  raw.locals.mapM (storageKind layouts) = some method.localKinds ∧
  method.locals.length = raw.locals.length ∧
  expectedHomes layouts raw reachable = some method.parameterHomes ∧
  all3 (validateArgumentOpIn raw (requiredHomeIndices raw reachable)) raw.code reachable method.code = true

instance (layouts : Array ComputedLayout) (raw : RawArguments)
    (reachable : List Bool) (method : Method) : Decidable (ParameterHomesValid layouts raw reachable method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

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

theorem validated_argument_access {layouts : Array ComputedLayout} {raw : RawArguments}
    {reachable : List Bool} {method : Method} (valid : ParameterHomesValid layouts raw reachable method)
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
