import Extracted
import CIL.Safety.MethodContract
import CIL.Safety.BufferContents

/-!
# Contract for a readonly by-reference span read

`SpanReferences::At(in ReadOnlySpan<byte>, int)` receives its span reference as the referenced
view, so the ordinary symbolic span contents prove its result without a separate span-home model.
-/

namespace Tests.SpanReferenceContracts
open CIL CIL.Safety

/-- A byte sequence in caller storage and the index and byte selected by a caller. -/
structure ReadInput where
  base : Reference
  values : List (BitVec 8)
  index : W32
  expected : BitVec 8

/-- The readonly view of the complete input sequence. -/
def ReadInput.view (input : ReadInput) : SpanView :=
  ⟨.address input.base, input.values.length, 1, false⟩

/-- Reading through an `in` span returns the selected byte, zero-extended, and changes nothing. -/
def readContract : MethodContract ReadInput (BitVec 8) where
  args input := [.bufferSpan input.view, .scalar (.i32 input.index)]
  results value := [.scalar (.i32 (value.zeroExtend 32))]
  pre input memory := input.view.validate memory = .ok () ∧
    Contents memory input.base 1 input.values ∧
    input.values[input.index.toNat]? = some input.expected
  footprint _ := []
  post input before after value := after = before ∧ value = input.expected

/-- The unsigned byte return narrowing leaves a zero-extended byte unchanged. -/
theorem extend_byte (x : BitVec 8) :
    NarrowKind.unsigned8.extend (x.setWidth 32) = x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  have small := x.isLt
  simp only [NarrowKind.extend, BitVec.toNat_setWidth, BitVec.zeroExtend_eq_setWidth]
  omega

#print axioms extend_byte

/-- The compiled `At` satisfies the contract for every caller sequence, index and storage. -/
theorem read_holds : readContract.Holds Extracted.program 0 := by
  intro input memory permitted
  obtain ⟨valid, contents, selected⟩ := permitted
  have bound : input.index.toNat < input.values.length :=
    List.getElem?_eq_some_iff.mp selected |>.1
  have loaded := contents input.index.toNat input.expected selected
  have formed := access_reference_valid _ _ _ _ _ (read_access loaded)
  have element : input.view.element memory input.index.toNat =
      .ok (input.base.element 1 input.index.toNat) := by
    unfold SpanView.element
    rw [valid]
    simpa [ReadInput.view, bound, Reference.element, Bind.bind, Except.bind] using formed
  have scalar := Contents.load contents (by decide : ScalarWidth 1) selected
  have item (rest : List Safety.Value) :
      memoryInstruction (.spanItem 1)
        (.scalar (.i32 input.index) :: .bufferSpan input.view :: rest) memory =
        .ok (memory, .readOnlyReference
          (.address (input.base.element 1 input.index.toNat)) :: rest) := by
    simp only [memoryInstruction, otherMemoryInstruction]
    simp only [ReadInput.view] at element ⊢
    simp [bound, element, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure, unspecifiedOperands, MemoryOp.argumentCount,
      Safety.Value.hasUnspecified, CIL.Value.hasUnspecified]
  refine ⟨6, memory, [.scalar (.i32 (input.expected.zeroExtend 32))], ?_, Confined.refl _ _,
    input.expected, rfl, rfl, rfl⟩
  dsimp only [readContract]
  simp only [Safety.invoke, Extracted.lookup0]
  simp [checkedValue, numericValue, valid, enterFrame, Extracted.method0, makeLocals,
    makeArgumentHomes, makeParameterHomes, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure, List.mapM_cons, List.mapM_nil]
  cil_checked_steps [readContract, ReadInput.view, valid, element, scalar, bound, numericOfWidth,
    formed, item, extend_byte]

#print axioms read_holds

end Tests.SpanReferenceContracts
