import CIL

/-!
# Consumer proof surface

These proofs use the public umbrella and named evidence. They pin call continuations, vector
literal rewrites, overlapping inputs, mixed local snapshots and checked segment boundaries.
-/

namespace Tests.PublicProofSurface
open CIL.Safety

/-- An opaque scalar helper returns its input's successor without writing caller storage. -/
def successor : MethodContract CIL.W32 CIL.W32 where
  args value := [.scalar (.i32 value)]
  results value := [.scalar (.i32 value)]
  pre _ _ := True
  footprint _ := []
  post input _ _ output := output = input + 1

/-- The caller forwards one checked scalar and returns the helper's output. -/
@[cil_code] def forwarding : CIL.Method :=
  { locals := [], returnsValue := true, code := [.call 1 1, .ret] }

/-- A call continuation selects postcondition and preservation facts by their names. -/
theorem named_call_continuation (program : CIL.Program) (memory : Memory) (value : CIL.W32)
    (found : program[0]? = some forwarding) (holds : successor.Holds program 1)
    (formed : memory.WellFormed) :
    WP (fun fuel => run program fuel 0 0 [] { activation := 0, locals := [], owned := [] }
      [.scalar (.i32 value)] memory)
      (fun final values => final.WellFormed ∧ values = [.scalar (.i32 (value + 1))]) := by
  apply run_call_of_contract_formed holds value found (by rfl)
    (by cil_checked_step [successor]) rfl trivial formed
  intro final output result preserved
  guard_hyp result :ₐ CallResult successor program 1 value memory final output
  guard_hyp preserved :ₐ FrameInvariants program memory final
  have output_eq := result.post
  have final_formed := preserved.formed
  cil_contract_steps [found, successor]
  exact ⟨final_formed, by rw [output_eq]⟩
#print axioms named_call_continuation

/-- The vector control is an ordinary literal in the emitted instructions. -/
@[cil_code] def reverseVector : CIL.Method :=
  { profile := { architecture := .x64, avx2 := true }, locals := [], returnsValue := true,
    code := [.const32 27, .intrinsic (.avx2 .permute4x64) 2, .ret] }

/-- A rewrite stated with a literal still matches the vector value left by stepping. -/
theorem vector_literal_rewrite (memory : Memory) (frame : Frame) (vector reversed : BitVec 256)
    (fuel : Nat) (reverse : CIL.Vector.permute4x64 vector 27 = reversed) :
    run [reverseVector] (fuel + 2) 0 0 [] frame [.scalar (.v256 vector)] memory =
      run [reverseVector] fuel 0 2 [] frame [.scalar (.v256 reversed)] memory := by
  have evaluated : CIL.evalIntrinsic (.avx2 .permute4x64) [.v256 vector, .i32 27] =
      some (.v256 (CIL.Vector.permute4x64 vector 27)) := rfl
  cil_checked_steps 2 [evaluated]
  change run [reverseVector] fuel 0 2 [] frame
    [.scalar (.v256 (CIL.Vector.permute4x64 vector 27))] memory = _
  rw [reverse]
#print axioms vector_literal_rewrite

/-- An aggregate is reinterpreted as a vector and compared with zero before a narrow return. -/
@[cil_code] def aggregateZero : CIL.Method :=
  { locals := [], returnsValue := true, code := [.loadAggregate 32,
    .memory (.bitcastValue (.aggregate 32) .vector256),
    .intrinsic (.vector (.zero 256)) 0, .intrinsic (.vector (.equalsAll 256)) 2,
    .ret (some .unsigned8)] }

/-- Snapshot map rewrites and symbolic intrinsic results remain usable after checked stepping. -/
theorem aggregate_boolean_return (memory : Memory) (frame : Frame) (input : Reference)
    (byte : Nat → BitVec 8)
    (loaded : ∀ rest, instruction (.loadAggregate 32) (.reference (.address input) :: rest)
      memory = .ok (memory, .scalar (.aggregate ((List.range 32).map byte)) :: rest)) :
    run [aggregateZero] 5 0 0 [] frame [.reference (.address input)] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if BitVec.ofNat 256 (byteNumber ((List.range 32).map byte)) = 0
          then 1 else 0))]) := by
  cil_checked_steps [loaded, staticInstruction]
  simp only [Function.comp_def]
#print axioms aggregate_boolean_return

/-- A vector comparison returns its scalar Boolean through the narrow return instruction. -/
@[cil_code] def equalVector : CIL.Method :=
  { locals := [], returnsValue := true,
    code := [.intrinsic (.vector (.equalsAll 128)) 2, .ret (some .unsigned8)] }

/-- An intrinsic's private result helper does not obstruct a symbolic scalar return. -/
theorem vector_boolean_return (memory : Memory) (frame : Frame) (left right : BitVec 128) :
    run [equalVector] 2 0 0 [] frame [.scalar (.v128 right), .scalar (.v128 left)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if left = right then 1 else 0))]) := by
  cil_checked_steps []
#print axioms vector_boolean_return

/-- A supplied checked conversion remains an opaque premise of a single instruction proof. -/
theorem checked_conversion_result (body : CIL.Method) (frame : Frame) (memory : Memory)
    (input : CIL.W64)
    (calculated : CIL.convertInteger 32 false true (.i64 input) =
      .ok (.i32 (BitVec.ofNat 32 input.toNat))) :
    step body (.checkedConvert 32 false true) 0 [] frame [.scalar (.i64 input)] memory =
      .ok (.next 1 [.scalar (.i32 (BitVec.ofNat 32 input.toNat))] frame memory) := by
  cil_checked_step [calculated]
#print axioms checked_conversion_result

/-- A two-word aggregate argument is described independently of any callee body. -/
def pairView (reference : Reference) : ArgumentView := ⟨reference, 16⟩

/-- Both source fields are loaded before any output could overwrite them. -/
@[cil_code] def readPair : CIL.Method :=
  { locals := [], returnsValue := true, code := [.arg 2, .skipInit,
      .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 8 8, .add, .ret] }

/-- Named call validity supplies field reads even when output aliases an entire input. -/
theorem overlapping_fields (memory : Memory) (left right : Reference)
    (call : ValidCall memory [pairView left, pairView right] [pairView left]) :
    WP (fun fuel => invoke [readPair] fuel 0
      [.reference (.address left), .reference (.address right), .reference (.address left)]
      memory)
      (fun final values => final = memory ∧ values = [.scalar (.i64
        ((pairView left).word memory 0 + (pairView right).word memory 8))]) := by
  cil_contract_steps []
  exact ⟨rfl, rfl⟩
#print axioms overlapping_fields

/-- A helper initializes one private word while the caller retains a vector snapshot. -/
theorem mixed_local_snapshot {caller current final : Memory} {word vector : Reference}
    {known : Nat → Option CIL.Value} {value : CIL.W64} {saved : BitVec 256}
    (context : LoopFrame [] caller current [.word64, .vector256]
      [.bytes .word64 word, .bytes .vector256 vector] known)
    (remembered : known 1 = some (.v256 saved))
    (confined : Confined [(word, 8)] current final) (formed : final.WellFormed)
    (loaded : read final word 8 1 = .ok (numberBytes value.toNat 8))
    (body : CIL.Method) (pc : Nat) (arguments stack : List Value) :
    step body (.local 1) pc arguments
      { activation := 0, locals := [.bytes .word64 word, .bytes .vector256 vector], owned := [] }
      stack final = .ok (.next (pc + 1) (.scalar (.v256 saved) :: stack)
        { activation := 0, locals := [.bytes .word64 word, .bytes .vector256 vector], owned := [] }
        final) := by
  have updated := context.after_local_write 0 .word64 word (.i64 value) value.toNat
    rfl confined formed rfl loaded
  have retained : rememberLocal known 0 (localResult .word64 (.i64 value)) 1 =
      some (.v256 saved) := remembered
  exact updated.snapshots.load (.v256 saved) retained
#print axioms mixed_local_snapshot

/-- One reusable arithmetic prefix adds one to the top word. -/
def incrementCode : List CIL.Op := [.const32 1, .add]

/-- A placed segment computes its stack value through the shared checked stepper. -/
theorem increment_segment {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (placed : CodeAt body start incrementCode)
    (arguments : List Value) (frame : Frame) (memory : Memory) (value : CIL.W32) :
    Segment program method start (start + 2)
      (SegmentState.exact arguments ⟨frame, [.scalar (.i32 value)], memory⟩)
      (SegmentState.exact arguments ⟨frame, [.scalar (.i32 (value + 1))], memory⟩) := by
  cil_segment 2 [found, placed, incrementCode]
#print axioms increment_segment

/-- Repeated code composes existing segment proofs without expanding their instructions again. -/
theorem repeated_segment {program : CIL.Program} {method : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (placed : CodeAt body 0 (incrementCode ++ incrementCode))
    (arguments : List Value) (frame : Frame) (memory : Memory) (value : CIL.W32) :
    Segment program method 0 4
      (SegmentState.exact arguments ⟨frame, [.scalar (.i32 value)], memory⟩)
      (SegmentState.exact arguments ⟨frame, [.scalar (.i32 (value + 1 + 1))], memory⟩) := by
  exact (increment_segment found placed.append_left arguments frame memory value).trans
    (increment_segment found placed.append_right arguments frame memory (value + 1))
#print axioms repeated_segment

/-- A countdown body has one return and one continuing edge. -/
@[cil_code] def countdown : CIL.Method :=
  { locals := [], returnsValue := true,
    code := [.dup, .brzero 5, .const32 1, .sub, .branch 0, .ret] }

/-- The checked continuing path retains the exact stack expression at the loop head. -/
theorem loop_cutpoint (memory : Memory) (frame : Frame) (value : CIL.W32)
    (nonzero : value ≠ 0) :
    LoopReaches [countdown] 0 []
      ⟨1, frame, [.scalar (.i32 value), .scalar (.i32 value)], memory⟩
      ⟨0, frame, [.scalar (.i32 (value - 1))], memory⟩ := by
  cil_loop_steps [nonzero]
#print axioms loop_cutpoint

end Tests.PublicProofSurface
