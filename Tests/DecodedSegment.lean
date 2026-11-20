import CIL.Safety.DecodedSegment
import Tests.DecodedSummary

/-! A summary of the adder's instruction at pc 2, reused after reversing its argument loads. -/

namespace Tests.DecodedSegment
open CIL CIL.Extraction CIL.Safety Tests.BodyEncoding Tests.BodyDecoding Tests.DecodedMethod
open Tests.DecodedSummary

/-- The stack supplies both addends. Only their sum remains when control reaches the return. -/
private def addStack (left right : W64) : SegmentContract :=
  .continuing 3 (fun _ before => before.stack = [.scalar (.i64 right), .scalar (.i64 left)])
    (fun _ before after => after = { before with stack := [.scalar (.i64 (left + right))] })
    (fun _ _ => [])

/-- Stepping the add on the decoded body proves its framed continuation for every incoming frame. -/
theorem add_region (left right : W64) :
    DecodedSegmentSummary [addMethod] [addItem] testProfile testEnvironment 0 2 pin
      addItem.original.token [] .add [] (addStack left right) := by
  refine ⟨decoded_summary.bound, ⟨addMethod, rfl, rfl⟩, ?_⟩
  rintro args ⟨frame, stack, memory⟩ permitted
  change stack = _ at permitted
  subst stack
  let after : SegmentState := ⟨frame, [.scalar (.i64 (left + right))], memory⟩
  refine ⟨.reaches 3 after, ⟨1, by decide, SegmentRun.reaches ?_⟩, Confined.refl _ _,
    rfl, rfl⟩
  intro fuel
  rfl

#print axioms add_region

/-- Swapping the two loads changes the method bytes outside the arithmetic suffix. -/
private def swappedRaw : RawMethod := { addArgumentsRaw with
  code := [instr 0 0x03, instr 1 0x02, instr 2 0x58, instr 3 0x2A] }

/-- Bytes and metadata encoded for the reversed loads. -/
private def swappedBody := (encodeBody pin swappedRaw).get (by decide +kernel)
/-- The decoded method with the reversed prefix. -/
private def swappedMethod := { addMethod with code := [.ldarg 1, .ldarg 0, .add, .ret] }
/-- The second extraction carries the new body under the same method identity. -/
private def swappedItem : MethodEvidence := { addItem with
  original := swappedRaw, closed := swappedRaw, body := swappedBody }

/-- The new body decodes and its own metadata still binds the selected method. -/
private theorem swapped_bound :
    DecodedAt [swappedMethod] [swappedItem] testProfile testEnvironment 0
      pin addItem.original.token [] := by
  apply DecodedAt.of_decoded (imports := []) (item := swappedItem)
  · cil_kernel_rfl
  · rfl
  · exact ⟨[], by decide +kernel⟩
  · cil_kernel_rfl

#print axioms swapped_bound

/-- The add and its return form a closed region starting at instruction two. -/
private abbrev suffix (method pc : Nat) := inStarts [(0, 2)] method pc = true

/-- The changed prefix needs no new proof of the add's stack result or memory confinement. -/
theorem reuse_after_changed_loads (left right : W64) :
    DecodedSegmentSummary [swappedMethod] [swappedItem] testProfile testEnvironment 0 2 pin
      addItem.original.token [] .add [] (addStack left right) := by
  apply (add_region left right).congr_region (region := suffix) swapped_bound
    (RegionClosed.of_check (by decide +kernel))
  · exact AgreesOn.set (program := [addMethod]) (index := 0) rfl swappedMethod.code fun _ inside =>
      code_agrees_of_drop (lower := 2) rfl (by simpa [suffix, inStarts] using inside)
  · intro i _
    simp [suffix, inStarts]
  · intro args before pc after _ post
    obtain ⟨rfl, _⟩ := post
    decide

#print axioms reuse_after_changed_loads

/-- Substitution of the instruction inside the region invalidates its placement. -/
theorem wrong_instruction_refused (left right : W64) :
    ¬ DecodedSegmentSummary [swappedMethod] [swappedItem] testProfile testEnvironment 0 2 pin
      addItem.original.token [] .sub [] (addStack left right) := by
  intro summary
  obtain ⟨body, present, placed⟩ := summary.placed
  cases present
  have wrong := placed.lookup 0 (op := .sub) rfl
  contradiction

#print axioms wrong_instruction_refused

/-- A different return convention invalidates reuse even when the suffix bytes agree. -/
theorem changed_return_shape_refused :
    ¬ AgreesOn [addMethod] [{ swappedMethod with returnsValue := false }] suffix := by
  intro agrees
  obtain ⟨body, found, metadata, _⟩ := agrees.2 0 2 addMethod (by decide) rfl
  cases found
  have same := congrArg Method.returnsValue metadata
  contradiction

#print axioms changed_return_shape_refused

end Tests.DecodedSegment
