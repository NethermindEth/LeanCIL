import CIL.Extraction.UnsafeModels
import CIL.Extraction.TransferKinds

/-! # Unsafe reference and value reinterpretations

The closed member reference selects the overload. A byref cast preserves a formed address.
A value cast moves a snapshot of equal width, or a byte into a Boolean.
-/

namespace CIL.Extraction

/-- The two method arguments of a static generic member on the exact Unsafe owner. -/
private def unsafeTypePair (method : MethodRef) : Option (TypeExpr × TypeExpr) :=
  if method.owner != unsafeOwner || method.hasThis || method.genericArity != 2 then none
  else match method.methodArguments with
    | [source, target] => some (source, target)
    | _ => none

/-- As excludes a byref, pointer or variable at the root of either type argument. -/
private def asArgument : TypeExpr → Bool
  | .byref _ | .pointer _ | .parameter _ | .ownerParameter _ => false
  | _ => true

/-- The reference cast between the two closed types. Its operation reads no storage. -/
private def asOperation (method : MethodRef) : Option MemoryOp := do
  let (source, target) ← unsafeTypePair method
  _root_.guard (asArgument source && asArgument target && method.parameters == [.byref source] &&
    method.returnType == .byref target)
  return .asRef

/-- BitCast reinterprets equally wide snapshots or the byte representation of a Boolean. -/
private def bitCastOperation (shape : TypeExpr → ValueShape) (method : MethodRef) :
    Option MemoryOp := do
  let (source, target) ← unsafeTypePair method
  _root_.guard (method.parameters == [source] && method.returnType == target)
  if source == .atom runtimeScope "System.Byte" && target == .atom runtimeScope "System.Boolean"
    then return .bitcastByteBool
  let .snapshot fromShape ← transferKind? shape source | none
  let .snapshot toShape ← transferKind? shape target | none
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
     (fun _ method => (asOperation method).map .memory),
   unsafeEntry name!"BitCast" "BitCast" "!!1" "!!0" (reinterpretDeclaration source target)
     (fun shape method => (bitCastOperation shape method).map .memory)]

/-- Each reinterpretation runs a checked memory operation. -/
theorem unsafeReinterpretEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation)) :
    ∀ entry ∈ unsafeReinterpretEntries, entry.Yields property := by
  simp only [unsafeReinterpretEntries, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨?_, ?_⟩ <;> intro environment method model found <;>
    simp only [unsafeEntry, Option.map_eq_some_iff] at found <;>
    obtain ⟨operation, _, rfl⟩ := found <;> exact memory operation

#print axioms unsafeReinterpretEntries_yields

end CIL.Extraction
