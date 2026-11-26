import CIL.Extraction.UnsafeModels
import CIL.Extraction.TransferKinds

/-! # Unsafe memory transfer models

Each closed address overload binds its own external member and open declaration.
The layout reader supplies the representation of the transferred element and its alignment.
-/

namespace CIL.Extraction

/-- A transfer takes an address and, for a write, the value to store. -/
private def parameters (store : Bool) (address element : TypeExpr) : List TypeExpr :=
  if store then [address, element] else [address]

/-- A read returns the transferred element. A write returns void. -/
private def result (store : Bool) (element : TypeExpr) : TypeExpr :=
  if store then .void else element

/-- The closed reference identifies the address overload independently of the element layout. -/
private def accepts (store : Bool) (address : TypeExpr) (method : MethodRef) : Bool :=
  (unsafeArgument method).any fun element =>
    method.parameters == parameters store address element &&
      method.returnType == result store element

/-- The required alignment is the aggregate's checked alignment or the scalar or vector width. -/
private def alignment (reader : CallLayouts) (element : TypeExpr) (kind : TransferKind) :
    Option Nat :=
  match kind with
  | .snapshot (.aggregate _) => reader.alignment? element
  | _ => some kind.width

/-- Aligned pointer reads and writes check natural alignment before transferring the value. -/
private def transfer (aligned store : Bool) (reader : CallLayouts) (method : MethodRef) :
    Option RuntimeModel := do
  let element ← unsafeArgument method
  let kind ← transferKind? reader element
  if aligned then
    let bytes ← alignment reader element kind
    return .memory (.pointerTransfer kind bytes store)
  else return .typedTransfer kind store

/-- One external member with its open declaration and corresponding closed address type. -/
private def overload (name : String) (aligned store byref : Bool) : ModelOverload :=
  let address := if byref then TypeExpr.byref (.primitive .byte)
    else .pointer .void
  let spelling := if byref then "System.Byte&" else "System.Void*"
  { operand := unsafeOperand name (if store then "System.Void" else "!!0")
      (if store then s!"{spelling},!!0" else spelling)
      (unsafeDeclaration (parameters store address) (result store)),
    accepts := accepts store address, resolve := transfer aligned store }

/-- An aligned member has one pointer overload. An unaligned member also takes a byte reference. -/
private def entry (key : MetadataName) (name : String) (aligned store : Bool) : ModelEntry :=
  { opcode := .call, owner := unsafeOwner, name := key, ownsName := true,
    overloads := overload name aligned store false ::
      (if aligned then [] else [overload name aligned store true]) }

/-- The four Unsafe calls that transfer a value between an address and the stack. -/
def unsafeTransferEntries : List ModelEntry :=
  [entry name!"Read" "Read" true false, entry name!"Write" "Write" true true,
   entry name!"ReadUnaligned" "ReadUnaligned" false false,
   entry name!"WriteUnaligned" "WriteUnaligned" false true]

/-- Each selected overload runs an aligned memory operation or an unaligned typed transfer. -/
theorem unsafeTransferEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation))
    (typed : ∀ kind store, property (.typedTransfer kind store)) :
    ∀ candidate ∈ unsafeTransferEntries, candidate.Yields property := by
  intro candidate listed reader method model found
  simp only [unsafeTransferEntries, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl <;>
    simp only [entry, ModelEntry.resolve, ModelEntry.select?, ModelEntry.select?.select,
      Bool.false_eq_true, ite_false, ite_true, List.any_cons, List.any_nil, Bool.or_false] at found
  all_goals
    repeat' split at found
    all_goals simp_all [overload, transfer, Option.bind_eq_some_iff, Option.pure_def]
  all_goals grind

#print axioms unsafeTransferEntries_yields

end CIL.Extraction
