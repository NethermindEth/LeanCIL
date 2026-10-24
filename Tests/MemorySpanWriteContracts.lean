import Extracted
import CIL.Safety.MethodContract
import CIL.Safety.BufferContents

/-! # Sequence update contracts for a compiled writable span helper -/
namespace Tests.MemorySpanWriteContracts
open CIL CIL.Safety

/-- A writable sequence, selected index and replacement element. -/
structure WriteInput where
  base : Reference
  values : List W32
  index : W32
  replacement : W32

/-- The writable view whose extent matches the input sequence. -/
def WriteInput.view (input : WriteInput) : SpanView :=
  ⟨.address input.base, input.values.length, 4, true⟩

/-- A single element update preserves the remainder of the sequence and neighbouring storage. -/
def writeContract : MethodContract WriteInput Unit where
  args input := [.bufferSpan input.view, .scalar (.i32 input.index),
    .scalar (.i32 input.replacement)]
  results _ := []
  pre input memory := input.view.validate memory = .ok () ∧
    Contents memory input.base 4 input.values ∧ input.index.toNat < input.values.length ∧
    access memory (input.base.element 4 input.index.toNat) 4 1 true = .ok ()
  footprint input := [(input.base.element 4 input.index.toNat, 4)]
  post input _ final _ := Contents final input.base 4
    (input.values.set input.index.toNat input.replacement)

theorem write_holds : writeContract.Holds Extracted.program 2 := by
  intro input memory permitted
  obtain ⟨valid, contents, bound, writable⟩ := permitted
  have formed := access_reference_valid _ _ _ _ _ writable
  obtain ⟨final, written⟩ := write_succeeds
    (bytes := numberBytes input.replacement.toNat 4) (by simpa using writable)
  have updated := contents.write_element written
  have element : input.view.element memory input.index.toNat =
      .ok (input.base.element 4 input.index.toNat) := by
    unfold SpanView.element
    rw [valid]
    simpa [WriteInput.view, bound, Reference.element, Nat.mul_comm,
      Bind.bind, Except.bind] using formed
  have item (rest : List Safety.Value) :
      memoryInstruction (.spanItem 4) (.scalar (.i32 input.index) :: .bufferSpan input.view :: rest)
        memory = .ok (memory, .reference
          (.address (input.base.element 4 input.index.toNat)) :: rest) := by
    simp only [memoryInstruction]
    simp only [WriteInput.view] at element ⊢
    simp [bound, element, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure, unspecifiedOperands, MemoryOp.argumentCount,
      Safety.Value.hasUnspecified, CIL.Value.hasUnspecified]
  have entered : enterFrame Extracted.method2 (writeContract.args input) memory =
      .ok (⟨memory.nextIdentity, [.span 4 true (some input.view)], [], [], 0⟩, memory) := by
    have checked := valid
    dsimp only [WriteInput.view] at checked
    simp [enterFrame, Extracted.method2, writeContract, makeLocals, makeArgumentHomes,
      makeParameterHomes, makeLocal, storeLocal, Safety.Value.hasUnspecified, WriteInput.view,
      checked, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨10, final, [], ?_, Confined.write written (by simp [writeContract]), (), rfl, updated⟩
  simp only [Safety.invoke, Extracted.lookup2]
  simp [writeContract, checkedValue, numericValue, valid, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure] at entered ⊢
  rw [entered]
  cil_checked_steps [WriteInput.view, checkedValue, numericValue, loadLocal, instruction,
    staticInstruction, valid, item, formed, formValue, written, referenceAt,
    observerCount, unspecifiedOperands, MemoryOp.argumentCount,
    Safety.Value.hasUnspecified, CIL.Value.hasUnspecified, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms write_holds
end Tests.MemorySpanWriteContracts
