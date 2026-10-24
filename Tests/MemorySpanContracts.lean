import Extracted
import CIL.Safety.MethodContract
import CIL.Safety.BufferContents

/-! # Functional contracts for compiled span helpers -/

namespace Tests.MemorySpanContracts
open CIL CIL.Safety

/-- A logical sequence and the index and value selected by a caller. -/
structure ReadInput where
  base : Reference
  values : List W32
  index : W32
  expected : W32

/-- The readonly view of the complete input sequence. -/
def ReadInput.view (input : ReadInput) : SpanView :=
  ⟨.address input.base, input.values.length, 4, false⟩

/-- Reading a span returns its mathematical sequence element without changing memory. -/
def readContract : MethodContract ReadInput W32 where
  args input := [.bufferSpan input.view, .scalar (.i32 input.index)]
  results value := [.scalar (.i32 value)]
  pre input memory := input.view.validate memory = .ok () ∧
    Contents memory input.base 4 input.values ∧
    input.values[input.index.toNat]? = some input.expected
  footprint _ := []
  post input before after value := after = before ∧ value = input.expected

theorem read_holds : readContract.Holds Extracted.program 1 := by
  intro input memory permitted
  obtain ⟨valid, contents, selected⟩ := permitted
  have bound : input.index.toNat < input.values.length :=
    List.getElem?_eq_some_iff.mp selected |>.1
  have loaded := contents input.index.toNat input.expected selected
  have formed := access_reference_valid _ _ _ _ _ (read_access loaded)
  have element : input.view.element memory input.index.toNat =
      .ok (input.base.element 4 input.index.toNat) := by
    unfold SpanView.element
    rw [valid]
    simpa [ReadInput.view, bound, Reference.element, Nat.mul_comm,
      Bind.bind, Except.bind] using formed
  have scalar := Contents.load contents (by decide : ScalarWidth 4) selected
  have item (rest : List Safety.Value) :
      memoryInstruction (.spanItem 4) (.scalar (.i32 input.index) :: .bufferSpan input.view :: rest)
        memory = .ok (memory, .readOnlyReference
          (.address (input.base.element 4 input.index.toNat)) :: rest) := by
    simp only [memoryInstruction]
    simp only [ReadInput.view] at element ⊢
    simp [bound, element, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure, unspecifiedOperands, MemoryOp.argumentCount,
      Safety.Value.hasUnspecified, CIL.Value.hasUnspecified]
  have entered : enterFrame Extracted.method1
      [.bufferSpan input.view, .scalar (.i32 input.index)] memory =
      .ok (⟨memory.nextIdentity, [.span 4 false (some input.view)], [], []⟩, memory) := by
    have checked := valid
    dsimp only [ReadInput.view] at checked
    simp [enterFrame, Extracted.method1, makeLocals, makeArgumentHomes, makeParameterHomes,
      makeLocal, storeLocal, Safety.Value.hasUnspecified, ReadInput.view, checked,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨10, memory, [.scalar (.i32 input.expected)], ?_, Confined.refl _ _,
    input.expected, rfl, rfl, rfl⟩
  dsimp only [readContract]
  simp only [Safety.invoke, Extracted.lookup1]
  simp [checkedValue, numericValue, valid, entered, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure, List.mapM_cons, List.mapM_nil]
  cil_checked_steps [readContract, ReadInput.view, checkedValue, numericValue, makeParameterHomes,
    makeLocal, storeLocal, loadLocal, instruction, staticInstruction, valid, element, scalar,
    bound, numericOfWidth, formed, formValue, item,
    observerCount, unspecifiedOperands, MemoryOp.argumentCount,
    Safety.Value.hasUnspecified, CIL.Value.hasUnspecified,
    checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms read_holds

/-- The compiled caller composes a slice read through any implementation of the helper contract. -/
theorem slice_read_composes (program : Program)
    (caller : program[0]? = some Extracted.method0)
    (helper : readContract.Holds program 1)
    (input : ReadInput) (memory : Safety.Memory) (source : SpanView) (start length index : W32)
    (sourceValid : source.validate memory = .ok ())
    (sourceWidth : source.width = 4) (sourceReadonly : source.writable = false)
    (startBound : start.toNat ≤ source.length)
    (lengthBound : length.toNat ≤ source.length - start.toNat)
    (sliced : source.slice memory start.toNat length.toNat = .ok input.view)
    (selectedIndex : index = input.index) (permitted : readContract.pre input memory) :
    ∃ fuel final returned,
      Safety.invoke program fuel 0
        [.bufferSpan source, .scalar (.i32 start), .scalar (.i32 length), .scalar (.i32 index)]
        memory = .ok (final, returned) ∧
      final = memory ∧ returned =
        [.scalar (.i32 (input.expected + BitVec.ofNat 32 input.values.length))] := by
  subst index
  have valid := permitted.1
  let args : List Safety.Value :=
    [.bufferSpan source, .scalar (.i32 start), .scalar (.i32 length), .scalar (.i32 input.index)]
  let frame : Frame := ⟨memory.nextIdentity,
    [.span 4 false (some ⟨.null, 0, 4, false⟩), .span 4 false (some source)], [], []⟩
  have entered : enterFrame Extracted.method0 args memory = .ok (frame, memory) := by
    simp [enterFrame, Extracted.method0, args, frame, makeLocals, makeArgumentHomes,
      makeParameterHomes, makeLocal, storeLocal, sourceWidth, sourceReadonly, sourceValid,
      Safety.Value.hasUnspecified, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  have execution : ∃ fuel final returned,
      Safety.run program fuel 0 0 args frame [] memory = .ok (final, returned) ∧
      final = memory ∧ returned =
        [.scalar (.i32 (input.expected + BitVec.ofNat 32 input.values.length))] := by
    cil_contract_steps [caller, args, frame, checkedValue, numericValue, loadLocal, storeLocal,
      sourceValid, sourceWidth, sourceReadonly, valid, sliced, startBound, lengthBound,
      ReadInput.view, instruction, staticInstruction, memoryInstruction, MemoryOp.argumentCount,
      observerCount, unspecifiedOperands, Safety.Value.hasUnspecified, CIL.Value.hasUnspecified,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    cil_contract_call helper input [caller, args, ReadInput.view, checkedValue, numericValue,
      sourceValid,
      valid, Safety.Value.hasUnspecified, CIL.Value.hasUnspecified, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    · exact permitted
    · intro final values invoked confined returned
      obtain ⟨value, rfl, rfl, rfl⟩ := returned
      cil_contract_steps [caller, args, loadLocal, checkedValue, numericValue, valid,
        ReadInput.view, instruction, staticInstruction, memoryInstruction, MemoryOp.argumentCount,
        observerCount, unspecifiedOperands, Safety.Value.hasUnspecified, CIL.Value.hasUnspecified,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl⟩
  obtain ⟨fuel, final, returned, ran, result⟩ := execution
  refine ⟨fuel, final, returned, ?_, result⟩
  simpa [Safety.invoke, caller, args, checkedValue, numericValue, sourceValid, entered,
    checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] using ran

#print axioms slice_read_composes
end Tests.MemorySpanContracts
