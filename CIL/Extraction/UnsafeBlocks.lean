import CIL.Extraction.UnsafeModels
import CIL.Extraction.Prefixes

/-! Runtime models for Unsafe byte-block copies and fills on references and pointers. -/

namespace CIL.Extraction

/-- One static, non-generic overload with its exact address type and external target. -/
private def blockRow (name : String) (copy pointer : Bool) (operation : MemoryOp) :
    ModelOverload :=
  let byte := TypeExpr.primitive .byte
  let address := if pointer then TypeExpr.pointer .void else .byref byte
  let addressName := if pointer then "System.Void*" else "System.Byte&"
  let sourceName := if copy then addressName else "System.Byte"
  let declared : OpenSignature := { convention := 0, parameters :=
    [address, if copy then address else byte, .primitive .uint32] }
  { operand := unsafeOperand name "System.Void" s!"{addressName},{sourceName},System.UInt32"
      declared
    accepts := fun method => method.owner == unsafeOwner && !method.hasThis &&
      method.genericArity == 0 && method.methodArguments.isEmpty && method.signature 0 == declared
    resolve := fun _ _ => some (.memory operation) }

/-- The by-reference and pointer overloads of one reserved block helper. -/
private def blockEntry (key : MetadataName) (name : String) (copy : Bool) (alignment : Nat) :
    ModelEntry :=
  let operation := if copy then MemoryOp.copyBlock alignment else .initBlock alignment
  { opcode := .call, owner := unsafeOwner, name := key, ownsName := true,
    overloads := [blockRow name copy false operation, blockRow name copy true operation] }

/-- Aligned block calls require eight-byte alignment and unaligned calls require one byte. -/
def unsafeBlockEntries : List ModelEntry :=
  [blockEntry name!"CopyBlock" "CopyBlock" true defaultBlockAlignment,
   blockEntry name!"CopyBlockUnaligned" "CopyBlockUnaligned" true 1,
   blockEntry name!"InitBlock" "InitBlock" false defaultBlockAlignment,
   blockEntry name!"InitBlockUnaligned" "InitBlockUnaligned" false 1]

/-- Both overloads of each block helper run its checked memory operation. -/
theorem unsafeBlockEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation)) :
    ∀ entry ∈ unsafeBlockEntries, entry.Yields property := by
  have yields (key name copy alignment) :
      (blockEntry key name copy alignment).Yields property := by
    intro reader method model found
    let operation := if copy then MemoryOp.copyBlock alignment else .initBlock alignment
    let byref := blockRow name copy false operation
    let pointer := blockRow name copy true operation
    change ((ModelEntry.select?.select method [byref, pointer]).bind
      (fun row => row.resolve reader method)) = some model at found
    cases href : byref.accepts method <;> cases hptr : pointer.accepts method <;>
      simp [ModelEntry.select?.select, href, hptr] at found
    all_goals cases found <;> exact memory operation
  simp only [unsafeBlockEntries, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨yields _ _ _ _, yields _ _ _ _, yields _ _ _ _, yields _ _ _ _⟩

#print axioms unsafeBlockEntries_yields

end CIL.Extraction
