import CIL.Safety.LocalCalls
import CIL.Safety.WideMultiply
import Tests.LoopFrames

/-!
# Private outputs of checked helpers

A wide-multiply helper writes the low word through an out reference and returns the high word.
Its caller retains initialized vector snapshots alongside an initially unknown word home.
The same transition applies to vector outputs without assuming any previous initialization.
-/

namespace Tests.LocalCalls
open CIL.Safety

/-- The checked body of an unsigned wide multiply with an out reference. -/
@[cil_code] def multiplyBody : CIL.Method :=
  { locals := [], returnsValue := true,
    code := [.arg 0, .arg 1, .arg 2, .memory (.bigMul64 false), .ret] }

/-- Inputs name the two factors and the actual low-word destination. -/
structure MultiplyInput where
  left : CIL.W64
  right : CIL.W64
  low : Reference

/-- Multiplication initializes the low word and returns the exact high word, confined to the
    destination. It does not require the destination to have an initial value. -/
def multiplyContract : MethodContract MultiplyInput CIL.W64 where
  args input := [.scalar (.i64 input.left), .scalar (.i64 input.right),
    .reference (.address input.low)]
  results value := [.scalar (.i64 value)]
  pre input memory := access memory input.low 8 1 true = .ok ()
  footprint input := [(input.low, 8)]
  post input _ final high := high = CIL.WideMultiply.high64 input.left input.right ∧
    read final input.low 8 1 = .ok (numberBytes (input.left * input.right).toNat 8)

/-- The helper contract follows from its actual checked instructions and a successful write. -/
theorem multiply_holds {program : CIL.Program} {callee : Nat}
    (found : program[callee]? = some multiplyBody) : multiplyContract.Holds program callee := by
  intro input memory writable
  obtain ⟨final, written, _, readback⟩ := store_word64 (input.left * input.right) writable
  have formed := access_reference_valid _ _ _ _ _ writable
  cil_contract_steps [found, formed, step_bigMul64_of_write written]
  exact ⟨Confined.write written (by simp [numberBytes_length]),
    CIL.WideMultiply.high64 input.left input.right, rfl, rfl, readback⟩

#print axioms multiply_holds

/-- A real helper invocation replaces the selected word snapshot and preserves a vector in
    any other local. The result contains both the exact low word and the exact high word. -/
theorem multiply_updates_mixed_frame {program : CIL.Program} {callee : Nat}
    {caller current : Memory} {kinds : List CIL.LocalKind} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} {low : Reference}
    (context : LoopFrame [] caller current kinds slots known)
    (found : program[callee]? = some multiplyBody)
    (slot : slots[0]? = some (.bytes .word64 low)) (left right : CIL.W64) :
    WP (fun fuel => invoke program fuel callee
      [.scalar (.i64 left), .scalar (.i64 right), .reference (.address low)] current)
      (fun final values =>
        values = [.scalar (.i64 (CIL.WideMultiply.high64 left right))] ∧
        LoopFrame [] caller final kinds slots (rememberLocal known 0 (.i64 (left * right)))) := by
  have execution := multiply_holds found ⟨left, right, low⟩ current
    (context.homes.writable_at slot)
  obtain ⟨fuel, final, values, invoked, confined, high, encoded, correct⟩ := execution
  obtain ⟨rfl, loaded⟩ := correct
  have formed := invoke_preserves_wellFormed _ _ _ _ _ _ _ context.wellFormed invoked
  exact ⟨fuel, final, values, invoked, encoded,
    context.after_local_write 0 .word64 low (.i64 (left * right)) (left * right).toNat
      slot confined formed rfl loaded⟩

#print axioms multiply_updates_mixed_frame

/-- A caller returns its low-word local after the helper returned the high word. -/
@[cil_code] def callerBody : CIL.Method :=
  { locals := [.unmodeled, .unmodeled], localKinds := [.word64, .vector256],
    returnsValue := true, code := [.call 1 3, .pop, .local 0, .ret] }

/-- The checked call rule carries the low-word snapshot through the caller's load and return.
    The vector and all other known homes remain in the named frame evidence at the call boundary. -/
theorem caller_loads_helper_output {caller current : Memory} {frame : Frame}
    {known : Nat → Option CIL.Value} {low : Reference}
    (context : LoopFrame [] caller current callerBody.localKinds frame.locals known)
    (slot : frame.locals[0]? = some (.bytes .word64 low)) (left right : CIL.W64) :
    WP (fun fuel => run [callerBody, multiplyBody] fuel 0 0 [] frame
      [.reference (.address low), .scalar (.i64 right), .scalar (.i64 left)] current)
      (fun _ values => values = [.scalar (.i64 (left * right))]) := by
  have formed := context.form_home 0 slot
  apply WP.local_call context (multiply_holds (callee := 1) (by rfl)) ⟨left, right, low⟩
    (by rfl) (by rfl) (by cil_checked_step [formed]) (context.homes.writable_at slot)
    0 .word64 low slot rfl (fun _ => .i64 (left * right)) (fun _ => (left * right).toNat)
    (fun _ => rfl) (fun _ _ result => result.2)
  intro final high result updated
  have loaded := updated.snapshots.load (index := 0) (.i64 (left * right)) rfl
    (body := callerBody) (pc := 2) (args := []) (stack := [])
  cil_contract_steps [loaded]
  rfl

#print axioms caller_loads_helper_output

/-- A vector helper output replaces its whole snapshot while retaining distinct scalar homes. -/
theorem vector_output {caller current after : Memory} {kinds : List CIL.LocalKind}
    {slots : List LocalSlot} {known : Nat → Option CIL.Value} {home : Reference}
    (context : LoopFrame [] caller current kinds slots known) (vector : BitVec 256)
    (slot : slots[1]? = some (.bytes .vector256 home))
    (confined : Confined [(home, 32)] current after) (formed : after.WellFormed)
    (loaded : read after home 32 1 = .ok (numberBytes vector.toNat 32)) :
    LoopFrame [] caller after kinds slots (rememberLocal known 1 (.v256 vector)) :=
  context.after_local_write 1 .vector256 home (.v256 vector) vector.toNat slot confined
    formed rfl loaded

#print axioms vector_output

/-- Updating a snapshot cannot validate the value that an overlapping write replaced. -/
theorem stale_snapshot_rejected {current after : Memory} {home : Reference}
    (written : write current home (numberBytes 6 4) 1 = .ok after) :
    ¬ LocalSnapshots after [.bytes .word32 home] (knownLocals [some (.i32 5)]) :=
  Tests.LoopFrames.overwritten_forgets written

#print axioms stale_snapshot_rejected

end Tests.LocalCalls
