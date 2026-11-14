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
structure BinaryOutputInput where
  left : CIL.W64
  right : CIL.W64
  low : Reference

/-- Multiplication initializes the low word and returns the exact high word, confined to the
    destination. It does not require the destination to have an initial value. -/
def multiplyContract : MethodContract BinaryOutputInput CIL.W64 where
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
    WP (Execution (fun fuel => invoke program fuel callee
      [.scalar (.i64 left), .scalar (.i64 right), .reference (.address low)] current))
      (fun (final, values) => values = [.scalar (.i64 (CIL.WideMultiply.high64 left right))] ∧
        LoopFrame [] caller final kinds slots (rememberLocal known 0 (.i64 (left * right)))) := by
  have execution := (multiply_holds found ⟨left, right, low⟩ current
    (context.homes.writable_at slot)).frame
    (assertion := fun result => result.1.WellFormed) (initial := (current, []))
    context.wellFormed (fun _ _ invoked formed =>
      invoke_preserves_wellFormed _ _ _ _ _ _ _ formed invoked)
  apply execution.consequence
  rintro ⟨final, values⟩ ⟨⟨confined, high, encoded, correct⟩, formed⟩
  obtain ⟨rfl, loaded⟩ := correct
  exact ⟨encoded,
    context.after_local_write 0 .word64 low (.i64 (left * right)) (left * right).toNat
      slot confined formed rfl loaded⟩

#print axioms multiply_updates_mixed_frame

/-- A caller returns its low-word local after the helper returned the high word. -/
@[cil_code] def callerBody : CIL.Method :=
  { locals := [.unmodeled, .v256 42], localKinds := [.word64, .vector256],
    returnsValue := true,
    code := [.arg 0, .arg 1, .ldloca 0, .call 1 3, .pop, .ldloc 0, .ret] }

bind_entry callerEntry (memory : Memory) (left right : CIL.W64)
    (formed : memory.WellFormed) := callerBody
  with [.scalar (.i64 left), .scalar (.i64 right)] from memory allocating formed

/-- The checked call rule carries the low-word snapshot through the caller's load and return.
    The vector and all other known homes remain in the named frame evidence at the call boundary. -/
theorem caller_loads_helper_output {caller current : Memory} {frame : Frame}
    {known : Nat → Option CIL.Value} {low : Reference}
    (context : LoopFrame [] caller current callerBody.localKinds frame.locals known)
    (slot : frame.locals[0]? = some (.bytes .word64 low)) (left right : CIL.W64)
    {entered : Memory}
    (setup : enterFrame callerBody [.scalar (.i64 left), .scalar (.i64 right)] caller =
      .ok (frame, entered)) :
    WP (Execution (fun fuel => run [callerBody, multiplyBody] fuel 0 3
      [.scalar (.i64 left), .scalar (.i64 right)] frame
      [.reference (.address low), .scalar (.i64 right), .scalar (.i64 left)] current))
      (fun (final, values) => Confined [] caller final ∧
        values = [.scalar (.i64 (left * right))]) := by
  have formed := context.form_home 0 slot
  apply WP.local_call context (multiply_holds (callee := 1) (by rfl)) ⟨left, right, low⟩
    (by rfl) (by rfl) (by cil_checked_step [formed]) (context.homes.writable_at slot)
    0 .word64 low slot rfl (fun _ => .i64 (left * right)) (fun _ => (left * right).toNat)
    (fun _ => rfl) (fun _ _ result => result.2)
  intro final high result updated
  have loaded := updated.snapshots.load (index := 0) (.i64 (left * right)) rfl
    (body := callerBody) (pc := 5)
    (args := [.scalar (.i64 left), .scalar (.i64 right)]) (stack := [])
  cil_contract_steps [loaded]
  exact ⟨(updated.leave setup).1, rfl⟩

#print axioms caller_loads_helper_output

/-- The whole caller allocates an unknown word and an initialized vector, calls the checked
    helper, reloads its private output and returns after the actual frame teardown. -/
theorem caller_invokes (memory : Memory) (formed : memory.WellFormed) (left right : CIL.W64) :
    WP (Execution (fun fuel => invoke [callerBody, multiplyBody] fuel 0
      [.scalar (.i64 left), .scalar (.i64 right)] memory))
      (fun (final, values) => Confined [] memory final ∧
        values = [.scalar (.i64 (left * right))]) := by
  obtain ⟨low, vector, entered, setup⟩ := callerEntry.checked memory left right formed
  have context := setup.frame []
  have suffix := caller_loads_helper_output
    (frame := callerEntry.frame memory low vector) context (by rfl) left right setup.setup
  apply WP.enter (by rfl) (by rfl) setup.setup
  cil_contract_steps [callerEntry.frame] until suffix

#print axioms caller_invokes

/-- Omitting the helper exposes the actual uninitialized local read, at its checked location. -/
theorem uninitialized_output_rejected :
    invoke [{ callerBody with code := [.ldloc 0, .ret] }] 1 0 [] Memory.empty =
      .error ⟨0, 0, .memory .uninitialized (.address ⟨0, 0⟩) 8⟩ := by
  rfl

#print axioms uninitialized_output_rejected

/-- A returned address to a private home is checked after teardown and cannot escape. -/
theorem escaped_home_rejected :
    invoke [{ callerBody with code := [.ldloca 0, .ret] }] 2 0 [] Memory.empty =
      .error ⟨0, 1, .memory .expiredLifetime (.address ⟨0, 0⟩) 0⟩ := by
  rfl

#print axioms escaped_home_rejected

/-- Changing the selected helper to a missing method fails at the actual call instruction. -/
theorem wrong_helper_rejected :
    invoke [{ callerBody with code := callerBody.code.set 3 (.call 2 3) }, multiplyBody]
      4 0 [.scalar (.i64 2), .scalar (.i64 3)] Memory.empty =
      .error ⟨0, 3, .invalidState⟩ := by
  rfl

#print axioms wrong_helper_rejected

/-- Writing the vector home instead of the selected word leaves the word uninitialized. -/
theorem wrong_output_home_rejected :
    invoke [{ callerBody with code := callerBody.code.set 2 (.ldloca 1) }, multiplyBody]
      10 0 [.scalar (.i64 2), .scalar (.i64 3)] Memory.empty =
      .error ⟨0, 5, .memory .uninitialized (.address ⟨0, 0⟩) 8⟩ := by
  rfl

#print axioms wrong_output_home_rejected

/-- Checked allocation evidence cannot describe two private slots as the same home. -/
theorem aliased_private_homes_rejected {caller current : Memory}
    {known : Nat → Option CIL.Value} (home : Reference) :
    ¬ LoopFrame [] caller current [.word64, .vector256]
      [.bytes .word64 home, .bytes .vector256 home] known := by
  intro context
  exact context.homes.distinct 0 1 .word64 .vector256 home home (by decide) rfl rfl rfl

#print axioms aliased_private_homes_rejected

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

/-- The wrapped word of an addition or subtraction helper. -/
def arithmeticWord (subtract : Bool) (left right : CIL.W64) : CIL.W64 :=
  if subtract then left - right else left + right

/-- The exact unsigned carry or borrow bit returned by the scalar helper. -/
def arithmeticFlag (subtract : Bool) (left right : CIL.W64) : CIL.W32 :=
  if (if subtract then left < right else left + right < left) then 1 else 0

/-- Both helpers store their wrapped word before returning the unsigned carry or borrow. -/
@[cil_code] def arithmeticBody (subtract : Bool) : CIL.Method :=
  { locals := [], returnsValue := true,
    code := [.arg 2, .arg 0, .arg 1, if subtract then .sub else .add, .store64] ++
      (if subtract then [.arg 0, .arg 1] else [.arg 0, .arg 1, .add, .arg 0]) ++
      [.clt_un, .ret] }

/-- Arithmetic output storage needs write authority, while the returned flag remains exact. -/
def arithmeticContract (subtract : Bool) : MethodContract BinaryOutputInput CIL.W32 where
  args := multiplyContract.args
  results value := [.scalar (.i32 value)]
  pre := multiplyContract.pre
  footprint := multiplyContract.footprint
  post input _ final flag := flag = arithmeticFlag subtract input.left input.right ∧
    read final input.low 8 1 =
      .ok (numberBytes (arithmeticWord subtract input.left input.right).toNat 8)

/-- Scalar carry and borrow contracts follow from the checked store and comparison. -/
theorem arithmetic_holds (subtract : Bool) {program : CIL.Program} {callee : Nat}
    (found : program[callee]? = some (arithmeticBody subtract)) :
    (arithmeticContract subtract).Holds program callee := by
  intro input memory writable
  obtain ⟨final, written, _, readback⟩ :=
    store_word64 (arithmeticWord subtract input.left input.right) writable
  have formed := access_reference_valid _ _ _ _ _ writable
  have stored := step_store64_of_write written
  cases subtract <;>
    cil_contract_steps [found, formed, stored, arithmeticBody, arithmeticContract,
      multiplyContract, arithmeticWord, arithmeticFlag]
  all_goals exact ⟨Confined.write written (by simp [numberBytes_length]), _, rfl, rfl, readback⟩

#print axioms arithmetic_holds

/-- Carry and borrow helpers compose with the same mixed-home caller and named frame evidence. -/
theorem arithmetic_caller (subtract : Bool) (memory : Memory) (formed : memory.WellFormed)
    (left right : CIL.W64) :
    WP (Execution (fun fuel => invoke [callerBody, arithmeticBody subtract] fuel 0
      [.scalar (.i64 left), .scalar (.i64 right)] memory))
      (fun (final, values) => Confined [] memory final ∧
        values = [.scalar (.i64 (arithmeticWord subtract left right))]) := by
  obtain ⟨low, vector, entered, setup⟩ := callerEntry.checked memory left right formed
  have context := setup.frame []
  apply WP.enter (by rfl) (by rfl) setup.setup
  cil_contract_steps [callerEntry.frame]
  apply WP.exists_execution
  apply WP.local_call context
    (arithmetic_holds subtract (program := [callerBody, arithmeticBody subtract])
      (callee := 1) rfl) ⟨left, right, low⟩
    rfl rfl (by cil_checked_step [callerEntry.frame, context.form_home 0 (by rfl)])
    setup.storage0.writable 0 .word64 low rfl rfl
    (fun _ => .i64 (arithmeticWord subtract left right))
    (fun _ => (arithmeticWord subtract left right).toNat) (fun _ => rfl)
    (fun _ _ result => result.2)
  intro final flag result updated
  have loaded := updated.snapshots.load (index := 0)
    (.i64 (arithmeticWord subtract left right)) rfl (body := callerBody) (pc := 5)
    (args := [.scalar (.i64 left), .scalar (.i64 right)]) (stack := [])
  cil_contract_steps [loaded, arithmeticContract, callerEntry.frame]
  exact ⟨(updated.leave setup.setup).1, rfl⟩

#print axioms arithmetic_caller

/-- Replacing carry by borrow cannot satisfy the original helper contract. -/
theorem changed_arithmetic_helper_rejected (memory : Memory) (output : Reference)
    (writable : access memory output 8 1 true = .ok ()) :
    ¬ (arithmeticContract false).Holds [arithmeticBody true] 0 := by
  intro wrong
  obtain ⟨actualMemory, actualFlag, actual⟩ :=
    (arithmetic_holds true (program := [arithmeticBody true]) (callee := 0) rfl).result
      ⟨0, 1, output⟩ writable
  obtain ⟨claimedMemory, claimedFlag, claimed⟩ := wrong.result ⟨0, 1, output⟩ writable
  obtain ⟨actualFuel, ran⟩ := actual.invoked
  obtain ⟨claimedFuel, claimedRun⟩ := claimed.invoked
  have equal := congrArg Prod.snd (invoke_ok_unique ran claimedRun)
  have actualResult := actual.post.1
  have claimedResult := claimed.post.1
  change actualFlag = 1 at actualResult
  change claimedFlag = 0 at claimedResult
  rw [actualResult, claimedResult] at equal
  exact (by decide : ([.scalar (.i32 1)] : List Value) ≠ [.scalar (.i32 0)]) equal

#print axioms changed_arithmetic_helper_rejected

end Tests.LocalCalls
