import CIL.Extraction.UnsafeModels
import CIL.Extraction.TransferKinds

/-! # Unsafe reference and value reinterpretations

The closed member reference selects the overload. A byref cast between field or vector storage
preserves a formed address.
A value cast moves a snapshot of equal width, or a byte into a Boolean.
-/

namespace CIL.Extraction

/-- The two method arguments of a static generic member on the exact Unsafe owner. -/
private def unsafeTypePair (method : MethodRef) : Option (TypeExpr × TypeExpr) :=
  if method.owner != unsafeOwner || method.hasThis || method.genericArity != 2 then none
  else match method.methodArguments with
    | [source, target] => some (source, target)
    | _ => none

/-- The reference cast between two closed types of field or vector storage. A span, array,
    class, byref, pointer or type variable has none, and its reference is not the address of
    bytes the target can name, so such a site decodes to the hole of its opcode. -/
private def asOperation (reader : CallLayouts) (method : MethodRef) : Option MemoryOp := do
  let (source, target) ← unsafeTypePair method
  _root_.guard ([source, target].all (fun type =>
      (reader.storage type).any StorageType.isFieldOrVector) &&
    method.parameters == [.byref source] && method.returnType == .byref target)
  return .asRef

/-- BitCast reinterprets equally wide snapshots or the byte representation of a Boolean. -/
private def bitCastOperation (reader : CallLayouts) (method : MethodRef) :
    Option MemoryOp := do
  let (source, target) ← unsafeTypePair method
  _root_.guard (method.parameters == [source] && method.returnType == target)
  if source == .atom runtimeScope "System.Byte" && target == .atom runtimeScope "System.Boolean"
    then return .bitcastByteBool
  let .snapshot fromShape ← transferKind? reader source | none
  let .snapshot toShape ← transferKind? reader target | none
  _root_.guard (fromShape.width == toShape.width)
  return .bitcastValue fromShape toShape

/-- One generic declaration of the reinterpretation family over its method variables. -/
private def reinterpretDeclaration (parameter result : TypeExpr) : OpenSignature :=
  { convention := 0x10, parameters := [parameter], returnType := result }

/-- The two-argument reference and value casts. Each resolves its own checked memory operation. -/
def unsafeReinterpretEntries : List ModelEntry :=
  let source := TypeExpr.parameter 0
  let target := TypeExpr.parameter 1
  [unsafeEntry name!"As" "As" "!!1&" "!!0&"
     (reinterpretDeclaration (.byref source) (.byref target))
     (fun reader method => (asOperation reader method).map .memory),
   unsafeEntry name!"BitCast" "BitCast" "!!1" "!!0" (reinterpretDeclaration source target)
     (fun reader method => (bitCastOperation reader method).map .memory)]

/-- Each reinterpretation runs a checked memory operation. -/
theorem unsafeReinterpretEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation)) :
    ∀ entry ∈ unsafeReinterpretEntries, entry.Yields property := by
  simp only [unsafeReinterpretEntries, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨?_, ?_⟩ <;> intro environment method model found <;>
    simp only [unsafeEntry, ModelEntry.resolve_single, Option.map_eq_some_iff] at found <;>
    obtain ⟨operation, _, rfl⟩ := found <;> exact memory operation

#print axioms unsafeReinterpretEntries_yields

/-- A stored reference helper binds the same signature at the open and closed type arguments. -/
private def referenceOverload (name result parameters : String)
    (signature : TypeExpr → OpenSignature) (admitted : StorageType → Bool)
    (operation : MemoryOp) : ModelOverload :=
  { operand := unsafeOperand name result parameters (signature (.parameter 0))
    accepts := fun method => (unsafeArgument method).any fun element =>
      method.signature 0x10 == signature element
    resolve := fun reader method => unsafeGuarded
      (method.methodArguments.any fun type => (reader.storage type).any admitted)
      (.memory operation) }

/-- Both AsRef overloads form the reference supplied by the caller. -/
private def asRefOverload (pointer : Bool) : ModelOverload :=
  referenceOverload "AsRef" "!!0&" (if pointer then "System.Void*" else "!!0&")
    (fun element => reinterpretDeclaration (if pointer then .pointer .void else .byref element)
      (.byref element)) StorageType.isFieldOrVector .asRef

/-- The reserved reference helpers and their exact external overloads. -/
def unsafeReferenceEntries : List ModelEntry :=
  let nonReference := fun (storage : StorageType) => storage != .reference
  let boolean := TypeExpr.atom runtimeScope "System.Boolean"
  [{ opcode := .call, owner := unsafeOwner, name := name!"AsRef", ownsName := true,
     overloads := [asRefOverload false, asRefOverload true] },
   { opcode := .call, owner := unsafeOwner, name := name!"NullRef", ownsName := true,
     overloads := [referenceOverload "NullRef" "!!0&" "" (fun element =>
       { convention := 0x10, parameters := [], returnType := .byref element })
       nonReference .nullRef] },
   { opcode := .call, owner := unsafeOwner, name := name!"IsNullRef", ownsName := true,
     overloads := [referenceOverload "IsNullRef" "System.Boolean" "!!0&" (fun element =>
       reinterpretDeclaration (.byref element) boolean) nonReference .isNullRef] }]

/-- Every selected reference overload runs its checked memory operation. -/
theorem unsafeReferenceEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation)) :
    ∀ entry ∈ unsafeReferenceEntries, entry.Yields property := by
  intro entry listed reader method model found
  simp only [unsafeReferenceEntries, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl <;>
    simp only [ModelEntry.resolve, ModelEntry.select?, ModelEntry.select?.select,
      List.any_cons, List.any_nil, Bool.or_false, Bool.false_eq_true, ite_false] at found <;>
    repeat' split at found
  all_goals first
    | contradiction
    | rw [unsafeGuarded_eq found]; exact memory _

#print axioms unsafeReferenceEntries_yields

end CIL.Extraction
