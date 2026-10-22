import Extracted
import Examples.Support
import CIL.Safety.SymbolicExecution
import CIL.Safety.NumericLocals
import CIL.Safety.ReturnMemory
import CIL.Safety.CallComposition
import CIL.Safety.WordMemory

open CIL.Safety
namespace ExampleProof

/-- The compiled struct stores and helper call return every input word.
    All caller allocation metadata, bytes, initialization and permissions survive;
    only fresh frame-owned storage may be allocated, written and expired. -/
theorem correctness (memory : Memory) (x : CIL.W64) (wellFormed : memory.WellFormed) :
    ∃ fuel result, invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =
      .ok (result, [.scalar (.i64 x)]) ∧ MemoryBelow memory.nextIdentity memory result := by
  obtain ⟨reference, entered, made, initialRead, writable, preserved⟩ :=
    make_numeric_local memory memory.nextIdentity (.aggregate 12)
      (.aggregate (List.replicate 12 0)) 0 wellFormed rfl
  let frame : Frame := ⟨memory.nextIdentity, [.bytes (.aggregate 12) reference], [reference.allocation], []⟩
  have opaqueLocalsEmpty : Extracted.method0.opaqueVectorLocals = [] := rfl
  have setup : enterFrame Extracted.method0 [.scalar (.i64 x)] memory = .ok (frame, entered) := by
    simp only [enterFrame, Extracted.method0_locals, Extracted.method0_localKinds,
      Extracted.method0_vectorArgs, Extracted.method0_parameterHomes, opaqueLocalsEmpty,
      makeSelectedLocals, List.isEmpty, ↓reduceIte, makeLocals, made, makeArgumentHomes, makeParameterHomes,
      frame, Bind.bind, Except.bind, Pure.pure, Except.pure, List.map_nil, List.append_nil]
  have enteredWF := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ wellFormed made
  have fresh := (makeLocal_fresh _ _ _ _ _ _ _ made).2 reference.allocation (by simp)
  change access entered reference 12 1 true = .ok () at writable
  obtain ⟨allocation, ready⟩ := access_requirements writable
  obtain ⟨initialized, initializedWrite⟩ := write_succeeds
    (bytes := List.replicate 12 (0 : BitVec 8)) (by simpa using writable)
  have initializedWF := write_preserves_wellFormed _ _ _ _ _ enteredWF initializedWrite
  have initReady := ready.after_write initializedWrite
  have payloadReady := initReady.slice initializedWF 0 8 (by decide) (by decide)
  obtain ⟨payload, payloadWrite⟩ := write_succeeds
    (bytes := numberBytes x.toNat 8) (by simpa [numberBytes] using payloadReady.access)
  have payloadWF := write_preserves_wellFormed _ _ _ _ _ initializedWF payloadWrite
  have tagReady := (initReady.after_write payloadWrite).slice payloadWF 8 4 (by decide) (by decide)
  obtain ⟨tagged, tagWrite⟩ := write_succeeds
    (bytes := numberBytes 3 4) (by simpa [numberBytes] using tagReady.access)
  have payloadRead := write_readback _ _ _ _ _ payloadWrite
  have finalRead := write_preserves_disjoint_read tagWrite payloadRead (Or.inr (Or.inl (by simp [numberBytes])))
  have taggedWF := write_preserves_wellFormed _ _ _ _ _ payloadWF tagWrite
  have payloadFull := initReady.after_write payloadWrite
  have taggedFull := payloadFull.after_write tagWrite
  have enteredForm := access_reference_valid _ _ _ _ _ writable
  have initializedForm := access_reference_valid _ _ _ _ _ initReady.access
  have payloadForm := access_reference_valid _ _ _ _ _ payloadFull.access
  have taggedForm := access_reference_valid _ _ _ _ _ taggedFull.access
  have payloadAddress : add initialized reference 1 (BitVec.ofNat 64 0) = .ok reference := by
    simpa using initReady.add_slice initializedWF 1 0 8 (by decide) (by decide)
  have tagAddress := payloadFull.add_slice payloadWF 1 8 4 (by decide) (by decide)
  have readAddress : add tagged reference 1 (BitVec.ofNat 64 0) = .ok reference := by
    simpa using taggedFull.add_slice taggedWF 1 0 8 (by decide) (by decide)
  have readWord : read tagged reference 8 1 = .ok (numberBytes x.toNat 8) := by
    simpa only [numberBytes, List.length_map, List.length_range, Nat.add_zero] using finalRead
  have loaded := load_word64_of_read readWord
  have initStep (body : CIL.Method) (pc : Nat) (args rest : List Value) (f : Frame) :
      step body (.initAggregate 12) pc args f (.reference (.address reference) :: rest) entered =
        .ok (.next (pc + 1) rest f initialized) := by
    simp only [step, pureArity, instruction, observerCount, unspecifiedOperands,
      List.take_succ_cons, List.take_zero, List.any_cons, List.any_nil,
      Value.hasUnspecified, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
      referenceAt, ordinaryAccessAlignment, initializedWrite,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨CIL.executionBound Extracted.program 0, leaveFrame frame tagged, ?_, ?_⟩
  · apply invoke_of_run (by simp only [cil_code] <;> rfl) rfl setup
    cil_checked_steps [checkedValue, numericValue, initStep, instruction,
      observerCount, CIL.MemoryOp.argumentCount, unspecifiedOperands,
      Value.hasUnspecified, CIL.Value.hasUnspecified, localAddress, frame, formValue,
      enteredForm, initializedForm, payloadForm, taggedForm, payloadAddress, tagAddress,
      readAddress, loaded, initializedWrite, payloadWrite, tagWrite, referenceAt, ordinaryAccessAlignment,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have first := write_preserves_memory_below _ _ _ _ _ memory.nextIdentity fresh.1 initializedWrite
    have second := write_preserves_memory_below _ _ _ _ _ memory.nextIdentity fresh.1 payloadWrite
    have third := write_preserves_memory_below _ _ { reference with offset := reference.offset + 8 } _ _ memory.nextIdentity fresh.1 tagWrite
    have last := leaveFrame_preserves_memory_below frame tagged memory.nextIdentity (by
      intro id member
      have same : id = reference.allocation := by simpa [frame] using member
      simpa [same] using fresh.1)
    exact ((preserved.trans first).trans second).trans (third.trans last)

#print axioms correctness
end ExampleProof
