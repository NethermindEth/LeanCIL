import CIL.Safety.MethodContract
import CIL.Safety.CheckedMemoryFacts
import CIL.SIMD.PackedLanes

/-!
# Checked SIMD carry and borrow composition

Synthetic helpers compute comparison masks, cascade them across four lanes and repair lane
arithmetic. Their contracts reuse the shared lane arithmetic theorems. A caller composes the
checked helpers without unfolding their execution, retaining the runtime profile and memory.
-/

namespace Tests.SimdCarryCalls
open CIL CIL.Vector CIL.Safety

/-- The runtime supplies the SIMD instructions used by both helpers. -/
@[cil_code] def profile : FeatureProfile :=
  { architecture := .x64, sse2 := true, ssse3 := true, sse41 := true, sse42 := true,
    avx := true, avx2 := true, avx512F := true, avx512FVL := true,
    avx512DQ := true, avx512DQVL := true, x86Base64 := true,
    bmi1 := true, bmi2 := true, vector128Accelerated := true }

/-- The chosen runtime profile satisfies the modeled CoreCLR feature prerequisites. -/
theorem profile_valid : profile.Valid := by decide
#print axioms profile_valid

/-- The wrapped lane arithmetic before incoming carries or borrows are applied. -/
def lanes (subtract : Bool) (left right : V256) : V256 :=
  if subtract then zip256 (· - ·) left right else zip256 (· + ·) left right

/-- The four outgoing lane flags before propagation. -/
def generate (subtract : Bool) (left right : V256) : W32 :=
  moveMask64 (zip256 (fun a b => mask64 (a.ult b))
    (if subtract then left else lanes false left right) (if subtract then right else left))

/-- The lanes through which an incoming carry or borrow propagates. -/
def propagate (subtract : Bool) (left right : V256) : W32 :=
  moveMask64 (zip256 (fun a b => mask64 (a == b))
    (if subtract then left else lanes false left right) (if subtract then right else ~~~0))

/-- Bit `i` is the incoming flag for lane `i`; bit four is the outgoing whole-vector flag. -/
def cascade (subtract : Bool) (left right : V256) : W32 :=
  propagate subtract left right ^^^
    (propagate subtract left right + (generate subtract left right <<< 1))

/-- CIL evaluates both by-value operands before applying their lane arithmetic. -/
@[cil_code] def laneCode (subtract : Bool) : List Instruction :=
  [.arg 0, .arg 1,
    .intrinsic (if subtract then .vector (.sub64 256) else .avx2 .add64) 2]

/-- A checked helper computes the packed flag cascade, retaining its outgoing flag bit. -/
@[cil_code] def maskBody (subtract : Bool) : Method :=
  { profile, locals := [], returnsValue := true,
    code :=
      (if subtract then [.arg 0, .arg 1] else
        laneCode false ++ [.const64 (~~~0), .intrinsic (.vector (.create64 256)) 1]) ++
      [.intrinsic (.avx2 .eq64) 2, .intrinsic (.avx512DQ .moveMask64) 1, .dup] ++
      (if subtract then [.arg 0, .arg 1] else laneCode false ++ [.arg 0]) ++
      [.intrinsic (.avx512 .ltu64) 2, .intrinsic (.avx512DQ .moveMask64) 1,
        .const32 1, .shl, .add, .bxor, .ret] }

/-- The mask helper returns the exact cascade and leaves every caller byte unchanged. -/
def maskContract (subtract : Bool) : MethodContract (V256 × V256) W32 where
  args input := [.scalar (.v256 input.1), .scalar (.v256 input.2)]
  results value := [.scalar (.i32 value)]
  pre _ _ := True
  footprint _ := []
  post input before after result := after = before ∧ result = cascade subtract input.1 input.2

/-- The checked CIL body computes the shared carry/borrow expression without memory writes. -/
theorem mask_holds (subtract : Bool) {program : Program} {callee : Nat}
    (found : program[callee]? = some (maskBody subtract)) :
    (maskContract subtract).Holds program callee := by
  rintro ⟨left, right⟩ memory _
  cases subtract <;>
    cil_contract_steps [found, profile, laneCode, generate, propagate, cascade, lanes,
      intrinsic_avx2_add256, intrinsic_avx2_eq256, intrinsic_avx512_ltu256,
      intrinsic_avx512dq_movemask256, pack256_allOnes]
  all_goals
    refine ⟨Confined.refl _ memory, _, rfl, rfl, ?_⟩
    simp only [cascade, propagate, generate, lanes, Bool.false_eq_true, ite_false, ite_true,
      ← pack256_allOnes]
    all_goals rfl

#print axioms mask_holds

/-- A decoded mask bit is widened to a complete 64-bit lane. -/
def flagLane (flags : W32) (index : Nat) : W64 :=
  ((flags >>> index) &&& 1).zeroExtend 64

/-- Scalar extraction of the three incoming flag bits agrees with the arithmetic API. -/
theorem flag_lanes (flags : W32) :
    flagLane flags 1 = (if flags.getLsbD 1 then 1 else 0) ∧
    flagLane flags 2 = (if flags.getLsbD 2 then 1 else 0) ∧
    flagLane flags 3 = (if flags.getLsbD 3 then 1 else 0) := by
  have bit (index : Nat) (bound : index < 32) : flagLane flags index =
      (if flags.getLsbD index then 1 else 0) := by
    apply BitVec.eq_of_getLsbD_eq
    intro position
    by_cases zero : position = 0
    · subst position
      cases selected : flags.getLsbD index <;> simp [flagLane, selected]
      omega
    · cases flags.getLsbD index <;> simp [flagLane, zero]
  exact ⟨bit 1 (by decide), bit 2 (by decide), bit 3 (by decide)⟩
#print axioms flag_lanes

/-- The CIL scalar extraction uses an unsigned shift, masks one bit and widens it. -/
@[cil_code] def flagCode (index : W32) : List Instruction :=
  [.arg 0, .const32 index, .shrUn, .const32 1, .band, .convU8]

/-- The repair helper adds or subtracts all three incoming flags in their own lanes. -/
@[cil_code] def repairBody (subtract : Bool) : Method :=
  { profile, locals := [], returnsValue := true,
    code := [.arg 1, .arg 2,
      .intrinsic (if subtract then .vector (.sub64 256) else .avx2 .add64) 2,
      .const64 0] ++ flagCode 1 ++ flagCode 2 ++ flagCode 3 ++
      [.intrinsic (.vector (.create64 256)) 4,
        .intrinsic (if subtract then .vector (.sub64 256) else .avx2 .add64) 2, .ret] }

/-- The corrected SIMD result before applying the shared whole-vector arithmetic theorem. -/
def repaired (subtract : Bool) (flags : W32) (left right : V256) : V256 :=
  let incoming := pack256 0 (flagLane flags 1) (flagLane flags 2) (flagLane flags 3)
  if subtract then zip256 (· - ·) (lanes subtract left right) incoming
  else zip256 (· + ·) (lanes subtract left right) incoming

/-- Repair has no arithmetic precondition: its result names precisely the supplied mask bits. -/
def repairContract (subtract : Bool) : MethodContract (W32 × V256 × V256) V256 where
  args input := [.scalar (.i32 input.1), .scalar (.v256 input.2.1), .scalar (.v256 input.2.2)]
  results value := [.scalar (.v256 value)]
  pre _ _ := True
  footprint _ := []
  post input before after result := after = before ∧
    result = repaired subtract input.1 input.2.1 input.2.2

/-- Checked scalar shifts and vector construction preserve the exact incoming lane flags. -/
theorem repair_holds (subtract : Bool) {program : Program} {callee : Nat}
    (found : program[callee]? = some (repairBody subtract)) :
    (repairContract subtract).Holds program callee := by
  rintro ⟨flags, left, right⟩ memory _
  cases subtract <;> cil_contract_steps [found, profile, flagCode]
  all_goals exact ⟨Confined.refl _ memory, _, rfl, rfl, rfl⟩
#print axioms repair_holds

/-- The established library arithmetic identifies the checked repair as wrapping addition. -/
theorem repaired_add (left right : V256) :
    repaired false (cascade false left right) left right = left + right := by
  obtain ⟨lane1, lane2, lane3⟩ := flag_lanes (cascade false left right)
  unfold repaired
  simp only [Bool.false_eq_true, ite_false, lane1, lane2, lane3]
  exact (add256_cascade left right).symm
#print axioms repaired_add

/-- The established library arithmetic identifies the checked repair as wrapping subtraction. -/
theorem repaired_subtract (left right : V256) :
    repaired true (cascade true left right) left right = left - right := by
  obtain ⟨lane1, lane2, lane3⟩ := flag_lanes (cascade true left right)
  unfold repaired
  simp only [ite_true, lane1, lane2, lane3]
  exact (sub256_cascade left right).symm
#print axioms repaired_subtract

/-- A checked caller obtains the cascade from one helper and supplies it to the repair helper. -/
@[cil_code] def callerBody : Method :=
  { profile, locals := [], returnsValue := true,
    code := [.arg 0, .arg 1, .call 1 2, .arg 0, .arg 1, .call 2 3, .ret] }

/-- The public contract specifies whole-vector wrapping arithmetic and unchanged memory. -/
def arithmeticContract (subtract : Bool) : MethodContract (V256 × V256) V256 where
  args input := [.scalar (.v256 input.1), .scalar (.v256 input.2)]
  results result := [.scalar (.v256 result)]
  pre _ _ := True
  footprint _ := []
  post input before after result := after = before ∧
    result = if subtract then input.1 - input.2 else input.1 + input.2

/-- The caller composes proved helper contracts, preserving the checked call/return semantics. -/
theorem caller_holds (subtract : Bool) {program : Program}
    (caller : program[0]? = some callerBody)
    (mask : program[1]? = some (maskBody subtract))
    (repair : program[2]? = some (repairBody subtract)) :
    (arithmeticContract subtract).Holds program 0 := by
  rintro ⟨left, right⟩ memory _
  cil_contract_steps [caller]
  cil_contract_call (mask_holds subtract mask) (left, right) [caller]
  case precondition => trivial
  intro masked flags maskResult
  obtain ⟨rfl, rfl⟩ := maskResult.post
  cil_contract_steps [caller]
  cil_contract_call (repair_holds subtract repair)
    (cascade subtract left right, left, right) [caller]
  case precondition => trivial
  intro repairedMemory result repairResult
  obtain ⟨rfl, rfl⟩ := repairResult.post
  cil_contract_steps [caller]
  refine ⟨Confined.refl _ _, _, rfl, rfl, ?_⟩
  cases subtract
  · exact repaired_add left right
  · exact repaired_subtract left right
#print axioms caller_holds

/-- The fourth packed flag bit is exactly the unsigned overflow or borrow of the whole vector. -/
theorem outgoing_flag (subtract : Bool) (left right : V256) :
    (cascade subtract left right).getLsbD 4 =
      if subtract then left.ult right else decide (2 ^ 256 ≤ left.toNat + right.toNat) := by
  cases subtract
  · exact (cascade_add256 left right (i := 4) (by decide)).trans (carry_width left right)
  · exact (cascade_sub256 left right (i := 4) (by decide)).trans (subBorrow_width left right)
#print axioms outgoing_flag

/-- Caller storage and the values saved by its two checked reads. -/
structure StoredInput where
  destination : Reference
  left : Reference
  right : Reference
  leftValue : V256
  rightValue : V256

/-- Both reads precede the helper call and the only store, so any input/output overlap is valid. -/
@[cil_code] def storedBody : Method :=
  { profile, locals := [], returnsValue := false,
    code := [.arg 0, .arg 1, .memory .load256, .arg 2, .memory .load256,
      .call 0 2, .memory .store256, .ret] }

/-- The output becomes the exact arithmetic result, with no separation or initial-output premise. -/
def storedContract (subtract : Bool) : MethodContract StoredInput Unit where
  args input := [.reference (.address input.destination), .reference (.address input.left),
    .reference (.address input.right)]
  results _ := []
  pre input memory :=
    read memory input.left 32 1 = .ok (numberBytes input.leftValue.toNat 32) ∧
    read memory input.right 32 1 = .ok (numberBytes input.rightValue.toNat 32) ∧
    access memory input.destination 32 1 true = .ok ()
  footprint input := [(input.destination, 32)]
  post input _ final _ := read final input.destination 32 1 =
    .ok (numberBytes (if subtract then input.leftValue - input.rightValue
      else input.leftValue + input.rightValue).toNat 32)

/-- Actual reads, helper calls and a vector store satisfy the overlapping contract. -/
theorem stored_holds (subtract : Bool) :
    (storedContract subtract).Holds
      [callerBody, maskBody subtract, repairBody subtract, storedBody] 3 := by
  intro input memory reads
  obtain ⟨leftRead, rightRead, writable⟩ := reads
  have leftFormed := access_reference_valid _ _ _ _ _ (read_access leftRead)
  have rightFormed := access_reference_valid _ _ _ _ _ (read_access rightRead)
  have outputFormed := access_reference_valid _ _ _ _ _ writable
  have leftLoaded := load_vector256_of_read leftRead
  have rightLoaded := load_vector256_of_read rightRead
  cil_contract_steps [leftFormed, rightFormed, outputFormed, leftLoaded, rightLoaded]
  cil_contract_call (caller_holds subtract (by rfl) (by rfl) (by rfl))
    (input.leftValue, input.rightValue) []
  case precondition => trivial
  intro current result called
  obtain ⟨rfl, rfl⟩ := called.post
  obtain ⟨final, written⟩ := write_succeeds
    (bytes := numberBytes (if subtract then input.leftValue - input.rightValue
      else input.leftValue + input.rightValue).toNat 32)
    (by simpa only [numberBytes_length] using writable)
  have readback := write_readback _ _ _ _ _ written
  cil_contract_steps [step_store256_of_write written]
  refine ⟨Confined.write written (by simp [numberBytes_length]), (), rfl, ?_⟩
  simpa only [storedContract, numberBytes_length] using readback
#print axioms stored_holds

/-- A carry from lane zero crosses the full lane one and changes lane two. -/
private def carrying : V256 := pack256 (~~~0) (~~~0) 5 0

/-- This incorrect helper shifts generated flags without cascading them through full lanes. -/
@[cil_code] private def singleHopBody (subtract : Bool) : Method :=
  { maskBody subtract with
    code := (if subtract then [.arg 0, .arg 1] else laneCode false ++ [.arg 0]) ++ [
      .intrinsic (.avx512 .ltu64) 2, .intrinsic (.avx512DQ .moveMask64) 1,
      .const32 1, .shl, .ret] }

/-- This incorrect helper repairs lane two from lane one's incoming flag. -/
@[cil_code] private def wrongLaneBody : Method :=
  { repairBody false with
    code := [.arg 1, .arg 2, .intrinsic (.avx2 .add64) 2, .const64 0] ++
      flagCode 1 ++ flagCode 1 ++ flagCode 3 ++
      [.intrinsic (.vector (.create64 256)) 4, .intrinsic (.avx2 .add64) 2, .ret] }

/-- Checked invocation exposes the returned vector independently of the memory representation. -/
private def observedVector (mask repair : Method) (left right : V256) : Option V256 :=
  (invoke [callerBody, mask, repair] 128 0
    [.scalar (.v256 left), .scalar (.v256 right)] Memory.empty).toOption.bind fun result =>
      match result.2 with
      | [.scalar (.v256 bits)] => some bits
      | _ => none

/-- A single repair hop misses a real cascading carry in the executed helper chain. -/
theorem single_hop_rejected :
    observedVector (singleHopBody false) (repairBody false) carrying 1 =
      some (pack256 0 0 5 0) ∧
    observedVector (singleHopBody false) (repairBody false) carrying 1 ≠
      some (carrying + 1) := by
  constructor
  · rfl
  · decide +kernel
#print axioms single_hop_rejected

/-- A borrow also propagates through equal lanes, which the executed single-hop mutant misses. -/
theorem single_borrow_hop_rejected :
    observedVector (singleHopBody true) (repairBody true) (pack256 0 7 9 1) (pack256 1 7 3 0) =
      some (pack256 (~~~0) (~~~0) 6 1) ∧
    observedVector (singleHopBody true) (repairBody true) (pack256 0 7 9 1) (pack256 1 7 3 0) ≠
      some (pack256 0 7 9 1 - pack256 1 7 3 0) := by
  constructor
  · rfl
  · decide +kernel
#print axioms single_borrow_hop_rejected

/-- Reading another lane's carry bit changes the actual returned vector. -/
theorem wrong_lane_rejected :
    observedVector (maskBody false) wrongLaneBody (pack256 (~~~0) 3 5 0) 1 =
      some (pack256 0 4 6 0) ∧
    observedVector (maskBody false) wrongLaneBody (pack256 (~~~0) 3 5 0) 1 ≠
      some (pack256 0 4 5 0) := by
  constructor
  · rfl
  · decide +kernel
#print axioms wrong_lane_rejected

/-- Substituting a borrow helper for a carry helper cannot preserve the caller's result. -/
theorem changed_helper_rejected :
    observedVector (maskBody true) (repairBody false) carrying 1 =
      some (pack256 0 (~~~0) 5 0) ∧
    observedVector (maskBody true) (repairBody false) carrying 1 ≠
      some (carrying + 1) := by
  constructor
  · rfl
  · decide +kernel
#print axioms changed_helper_rejected

/-- A scalar runtime rejects the first AVX2 operation at its exact checked instruction. -/
theorem missing_profile_rejected :
    invoke [{ maskBody false with profile := FeatureProfile.scalar }] 128 0
      [.scalar (.v256 0), .scalar (.v256 0)] Memory.empty =
      .error ⟨0, 2, .unsupported "Intrinsic unavailable in target profile"⟩ := by
  rfl
#print axioms missing_profile_rejected

/-- Adjacent vectors contain one and zero in caller-owned readable/writable memory. -/
private def overlapMemory : CIL.Safety.Memory where
  allocations identity := if identity = 0 then
    some { kind := .callerStack, layout := ⟨64, 1, []⟩ } else none
  cells _ offset := ⟨if offset = 0 then 1 else 0, true⟩
  views := [⟨0, 0, 64, true, true⟩]
  nextIdentity := 1

/-- The output aliases the first operand exactly. -/
private def overlapArguments : List CIL.Safety.Value :=
  [.reference (.address ⟨0, 0⟩), .reference (.address ⟨0, 0⟩), .reference (.address ⟨0, 32⟩)]

/-- This incorrect caller overwrites the first input before taking its snapshot. -/
@[cil_code] private def earlyStoreBody : Method :=
  { storedBody with code := [.arg 0, .const64 0, .intrinsic (.vector (.create64 256)) 1,
      .memory .store256] ++ storedBody.code }

/-- Observe the output bytes only after the real checked invocation returns. -/
private def observedStore (body : Method) :=
  (invoke [callerBody, maskBody false, repairBody false, body] 128 3
    overlapArguments overlapMemory).toOption.bind fun result =>
      (read result.1 ⟨0, 0⟩ 32 1).toOption

/-- Saved reads permit exact overlap; moving the store before them destroys the promised input. -/
theorem early_overlapping_store_rejected :
    observedStore storedBody = some (numberBytes 1 32) ∧
    observedStore earlyStoreBody = some (numberBytes 0 32) ∧
    observedStore earlyStoreBody ≠ some (numberBytes 1 32) := by
  constructor
  · rfl
  constructor
  · rfl
  · decide +kernel
#print axioms early_overlapping_store_rejected

end Tests.SimdCarryCalls
