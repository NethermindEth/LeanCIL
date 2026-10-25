import CIL.Safety.SymbolicExecution
import CIL.SIMD.Evaluation256Lemmas

/-!
# Reusable intrinsic executions

Execution facts for broadcast arithmetic separate instruction dispatch from vector evaluation.
Concrete runtime comparisons instantiate these facts without reducing the interpreter again.
-/

namespace CIL.Safety

set_option maxRecDepth 4096

/-- A binary operation applied to broadcast operands, followed by a lane extraction. -/
@[cil_code] def broadcastBinaryMethod (profile : FeatureProfile) (operation : AVX2Intrinsic)
    (lane : W32) : Method := {
  profile := profile, returnsValue := true, locals := []
  code := [.arg 0, .intrinsic (.vector (.create64 256)) 1,
    .arg 1, .intrinsic (.vector (.create64 256)) 1, .intrinsic (.avx2 operation) 2,
    .const32 lane, .intrinsic (.vector (.extract64 256)) 2, .ret] }

/-- Broadcasting a word does not observe any unspecified bits. -/
theorem checked_broadcast256 (word : W64) :
    checkedIntrinsic (.vector (.create64 256)) [.i64 word] =
      .ok (.v256 (Vector.pack256 word word word word)) := rfl

#print axioms checked_broadcast256

/-- Extracting a valid lane reads the corresponding 64 bits. -/
theorem checked_extract256 (bits : BitVec 256) (lane : W32) (bound : lane.toNat < 4) :
    checkedIntrinsic (.vector (.extract64 256)) [.v256 bits, .i32 lane] =
      .ok (.i64 (Vector.lane64 bits lane.toNat)) := by
  change (match (if lane.toNat < 4 then some (CIL.Value.i64
    (Vector.lane64 bits lane.toNat)) else none) with
    | some value => .ok value | none => .error .invalidState : ExecutionResult CIL.Value) = _
  simp only [if_pos bound]

#print axioms checked_extract256

/-- A broadcast binary method returns the selected lane of its checked intrinsic result. -/
theorem invoke_broadcastBinary (profile : FeatureProfile) (operation : AVX2Intrinsic)
    (lane : W32) (left right : W64) (bits : BitVec 256) (memory : Memory)
    (available : profile.avx2 = true) (bound : lane.toNat < 4)
    (evaluated : checkedIntrinsic (.avx2 operation)
      [.v256 (Vector.pack256 left left left left),
        .v256 (Vector.pack256 right right right right)] = .ok (.v256 bits)) :
    invoke [broadcastBinaryMethod profile operation lane] 256 0
      [.scalar (.i64 left), .scalar (.i64 right)] memory =
      .ok (memory, [.scalar (.i64 (Vector.lane64 bits lane.toNat))]) := by
  cil_checked_steps [available, evaluated, checked_broadcast256,
    checked_extract256 bits lane bound]

#print axioms invoke_broadcastBinary

/-- Every in-range lane of a broadcast holds the original word. -/
theorem lane_broadcast256 (word : W64) (lane : Nat) (bound : lane < 4) :
    Vector.lane64 (Vector.pack256 word word word word) lane = word := by
  have cases : lane = 0 ∨ lane = 1 ∨ lane = 2 ∨ lane = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> simp

#print axioms lane_broadcast256

/-- A broadcast result permits every valid lane selection without vector computation. -/
theorem invoke_broadcastBinary_word (profile : FeatureProfile) (operation : AVX2Intrinsic)
    (lane : W32) (left right word : W64) (memory : Memory)
    (available : profile.avx2 = true) (bound : lane.toNat < 4)
    (evaluated : checkedIntrinsic (.avx2 operation)
      [.v256 (Vector.pack256 left left left left),
        .v256 (Vector.pack256 right right right right)] =
        .ok (.v256 (Vector.pack256 word word word word))) :
    invoke [broadcastBinaryMethod profile operation lane] 256 0
      [.scalar (.i64 left), .scalar (.i64 right)] memory =
      .ok (memory, [.scalar (.i64 word)]) := by
  simpa only [lane_broadcast256 word lane.toNat bound] using
    invoke_broadcastBinary profile operation lane left right _ memory available bound evaluated

#print axioms invoke_broadcastBinary_word

/-- AVX2 AND distributes over broadcast lanes. -/
theorem checked_broadcast_and (left right : W64) :
    checkedIntrinsic (.avx2 .band)
      [.v256 (Vector.pack256 left left left left),
        .v256 (Vector.pack256 right right right right)] =
      .ok (.v256 (Vector.pack256 (left &&& right) (left &&& right)
        (left &&& right) (left &&& right))) := by
  change Except.ok (CIL.Value.v256 (_ &&& _)) = _
  rw [Vector.pack256_and]

#print axioms checked_broadcast_and

/-- AVX2 OR distributes over broadcast lanes. -/
theorem checked_broadcast_or (left right : W64) :
    checkedIntrinsic (.avx2 .bor)
      [.v256 (Vector.pack256 left left left left),
        .v256 (Vector.pack256 right right right right)] =
      .ok (.v256 (Vector.pack256 (left ||| right) (left ||| right)
        (left ||| right) (left ||| right))) := by
  change Except.ok (CIL.Value.v256 (_ ||| _)) = _
  rw [Vector.pack256_or]

#print axioms checked_broadcast_or

/-- AVX2 XOR distributes over broadcast lanes. -/
theorem checked_broadcast_xor (left right : W64) :
    checkedIntrinsic (.avx2 .bxor)
      [.v256 (Vector.pack256 left left left left),
        .v256 (Vector.pack256 right right right right)] =
      .ok (.v256 (Vector.pack256 (left ^^^ right) (left ^^^ right)
        (left ^^^ right) (left ^^^ right))) := by
  change Except.ok (CIL.Value.v256 (_ ^^^ _)) = _
  rw [Vector.pack256_xor]

#print axioms checked_broadcast_xor

/-- AVX2 AND-NOT complements the left broadcast operand before intersecting lanes. -/
theorem checked_broadcast_andNot (left right : W64) :
    checkedIntrinsic (.avx2 .andNot)
      [.v256 (Vector.pack256 left left left left),
        .v256 (Vector.pack256 right right right right)] =
      .ok (.v256 (Vector.pack256 ((~~~left) &&& right) ((~~~left) &&& right)
        ((~~~left) &&& right) ((~~~left) &&& right))) := by
  change Except.ok (CIL.Value.v256 ((~~~_) &&& _)) = _
  rw [Vector.pack256_not, Vector.pack256_and]

#print axioms checked_broadcast_andNot

/-- A full-width shift count is held in an opaque local so its high bits stay unspecified. -/
@[cil_code] def broadcastShiftMethod (profile : FeatureProfile) (operation : AVX2Intrinsic)
    (lane : W32) : Method := {
  profile := profile, returnsValue := true, locals := [.v128 0]
  localKinds := [.vector128], opaqueVectorLocals := [0]
  code := [.arg 1, .intrinsic (.vector .createScalarUnsafe64) 1, .setLocal 0,
    .arg 0, .intrinsic (.vector (.create64 256)) 1, .local 0,
    .intrinsic (.avx2 operation) 2, .const32 lane,
    .intrinsic (.vector (.extract64 256)) 2, .ret] }

/-- Creating an unsafe scalar vector records only the low lane. -/
theorem checked_scalarUnsafe (word : W64) :
    checkedIntrinsic (.vector .createScalarUnsafe64) [.i64 word] =
      .ok (.v128Low64 word) := rfl

#print axioms checked_scalarUnsafe

/-- Shifting a broadcast returns the selected lane of the checked shift result. -/
theorem invoke_broadcastShift (profile : FeatureProfile) (operation : AVX2Intrinsic)
    (lane : W32) (value count word : W64) (memory : Memory)
    (available : profile.avx2 = true) (bound : lane.toNat < 4)
    (evaluated : checkedIntrinsic (.avx2 operation)
      [.v256 (Vector.pack256 value value value value), .v128Low64 count] =
        .ok (.v256 (Vector.pack256 word word word word))) :
    invoke [broadcastShiftMethod profile operation lane] 256 0
      [.scalar (.i64 value), .scalar (.i64 count)] memory =
      .ok (memory, [.scalar (.i64 word)]) := by
  cil_checked_steps [available, evaluated, checked_broadcast256, checked_scalarUnsafe,
    checked_extract256, lane_broadcast256, bound, Opaque128Value.value]

#print axioms invoke_broadcastShift

/-- A full-width left shift clears all lanes when the count is at least 64. -/
theorem checked_broadcast_shiftLeft (value count : W64) :
    checkedIntrinsic (.avx2 .shl64Count)
      [.v256 (Vector.pack256 value value value value), .v128Low64 count] =
      .ok (.v256 (let word := if count.toNat >= 64 then 0 else value <<< count.toNat
        Vector.pack256 word word word word)) := by
  change Except.ok (CIL.Value.v256 (Vector.shiftLeftCount64 _ _)) = _
  by_cases large : count.toNat >= 64 <;>
    simp [Vector.shiftLeftCount64, Vector.map256, large] <;> rfl

#print axioms checked_broadcast_shiftLeft

/-- A full-width right shift clears all lanes when the count is at least 64. -/
theorem checked_broadcast_shiftRight (value count : W64) :
    checkedIntrinsic (.avx2 .shr64Count)
      [.v256 (Vector.pack256 value value value value), .v128Low64 count] =
      .ok (.v256 (let word := if count.toNat >= 64 then 0 else value >>> count.toNat
        Vector.pack256 word word word word)) := by
  change Except.ok (CIL.Value.v256 (Vector.shiftRightCount64 _ _)) = _
  by_cases large : count.toNat >= 64 <;>
    simp [Vector.shiftRightCount64, Vector.map256, large] <;> rfl

#print axioms checked_broadcast_shiftRight

end CIL.Safety
