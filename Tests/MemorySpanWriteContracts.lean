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
    simp only [memoryInstruction, otherMemoryInstruction]
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
    simp only [memoryInstruction, otherMemoryInstruction]
    simp only [ReadInput.view] at element ⊢
    simp [bound, element, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure, unspecifiedOperands, MemoryOp.argumentCount,
      Safety.Value.hasUnspecified, CIL.Value.hasUnspecified]
  have entered : enterFrame Extracted.method1
      [.bufferSpan input.view, .scalar (.i32 input.index)] memory =
      .ok (⟨memory.nextIdentity, [.span 4 false (some input.view)], [], [], 0⟩, memory) := by
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

/-- A writable slice composes mutation and readback contracts without either helper body. -/
theorem slice_write_composes (program : Program)
    (caller : program[0]? = some Extracted.method0)
    (writer : writeContract.Holds program 2) (reader : readContract.Holds program 1)
    (input : WriteInput) (memory : Safety.Memory) (source : SpanView) (start length : W32)
    (sourceValid : source.validate memory = .ok ())
    (sourceWidth : source.width = 4) (sourceWritable : source.writable = true)
    (startBound : start.toNat ≤ source.length)
    (lengthBound : length.toNat ≤ source.length - start.toNat)
    (sliced : source.slice memory start.toNat length.toNat = .ok input.view)
    (backingAllocation : input.base.allocation < memory.nextIdentity)
    (permitted : writeContract.pre input memory) :
    ∃ fuel final returned,
      Safety.invoke program fuel 0
        [.bufferSpan source, .scalar (.i32 start), .scalar (.i32 length),
          .scalar (.i32 input.index), .scalar (.i32 input.replacement)] memory =
        .ok (final, returned) ∧
      Contents final input.base 4 (input.values.set input.index.toNat input.replacement) ∧
      returned = [.scalar (.i32 input.replacement)] := by
  have valid := permitted.1
  have bound := permitted.2.2.1
  let args : List Safety.Value := [.bufferSpan source, .scalar (.i32 start),
    .scalar (.i32 length), .scalar (.i32 input.index), .scalar (.i32 input.replacement)]
  let frame : Frame := ⟨memory.nextIdentity, [.span 4 true (some source)], [], [], 0⟩
  have entered : enterFrame Extracted.method0 args memory = .ok (frame, memory) := by
    simp [enterFrame, Extracted.method0, args, frame, makeLocals, makeArgumentHomes,
      makeParameterHomes, makeLocal, storeLocal, sourceWidth, sourceWritable, sourceValid,
      Safety.Value.hasUnspecified, checkedAt, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  have execution : ∃ fuel final returned,
      Safety.run program fuel 0 0 args frame [] memory = .ok (final, returned) ∧
      Contents final input.base 4 (input.values.set input.index.toNat input.replacement) ∧
      returned = [.scalar (.i32 input.replacement)] := by
    cil_contract_steps [caller, args, frame, checkedValue, numericValue, loadLocal, storeLocal,
      sourceValid, sourceWidth, sourceWritable, valid, sliced, startBound, lengthBound,
      WriteInput.view, instruction, staticInstruction, memoryInstruction,
        otherMemoryInstruction, MemoryOp.argumentCount,
      observerCount, unspecifiedOperands, Safety.Value.hasUnspecified, CIL.Value.hasUnspecified,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    cil_contract_call writer input [caller, args, WriteInput.view, checkedValue, numericValue,
      sourceValid, valid, Safety.Value.hasUnspecified, CIL.Value.hasUnspecified, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · exact permitted
    · intro updated values invoked confined returned
      obtain ⟨result, rfl, contents⟩ := returned
      have validUpdated : input.view.validate updated = .ok () := by
        simpa only [SpanView.validate, WriteInput.view, liveAllocation,
          confined.allocations _ backingAllocation] using valid
      let readInput : ReadInput := ⟨input.base,
        input.values.set input.index.toNat input.replacement, input.index, input.replacement⟩
      have readView : readInput.view = input.view.asReadOnly := by
        simp [readInput, ReadInput.view, WriteInput.view, SpanView.asReadOnly]
      have readValid : readInput.view.validate updated = .ok () := by
        simpa only [readView, SpanView.validate, SpanView.asReadOnly] using validUpdated
      have readonlyValid :
          (⟨.address input.base, input.values.length, 4, false⟩ : SpanView).validate updated =
            .ok () := by
        exact validUpdated
      have readPermitted : readContract.pre readInput updated := by
        refine ⟨readValid, contents, ?_⟩
        simp [readInput, bound]
      cil_contract_steps [caller, args, writeContract, loadLocal, checkedValue, numericValue,
        validUpdated,
        WriteInput.view, instruction, staticInstruction, memoryInstruction,
        otherMemoryInstruction, MemoryOp.argumentCount,
        observerCount, unspecifiedOperands, Safety.Value.hasUnspecified, CIL.Value.hasUnspecified,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      refine run_call_of_contract reader readInput
        (by cil_lookup [caller]) (by cil_lookup [caller])
        (by cil_checked_step [caller, args, SpanView.asReadOnly, readonlyValid, checkedValue, numericValue,
          Safety.Value.hasUnspecified, CIL.Value.hasUnspecified, checkedAt, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure])
        (by simp [readContract, readInput, ReadInput.view]) ?_ ?_
      · exact readPermitted
      · intro final values invoked confined returned
        obtain ⟨value, rfl, rfl, rfl⟩ := returned
        cil_contract_steps [caller, args, readContract, checkedValue, numericValue, readInput,
          observerCount, unspecifiedOperands, Safety.Value.hasUnspecified, CIL.Value.hasUnspecified,
          checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        exact ⟨contents, rfl⟩
  obtain ⟨fuel, final, returned, ran, result⟩ := execution
  refine ⟨fuel, final, returned, ?_, result⟩
  simpa [Safety.invoke, caller, args, checkedValue, numericValue, sourceValid, entered,
    checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] using ran

#print axioms slice_write_composes
end Tests.MemorySpanWriteContracts
