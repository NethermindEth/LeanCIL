import CIL.SIMD.VectorLemmas
import CIL.SIMD.Intrinsics

/-!
# 128-bit intrinsic evaluation lemmas

`evalIntrinsic` on concrete 128-bit operations, as `rfl` simp lemmas, plus the BMI1 flag
extraction facts. Stepping proofs rewrite with these instead of unfolding `evalIntrinsic`.
-/

open CIL

namespace CIL.Vector

@[simp] theorem intrinsic_create256 (a b c d : W64) :
    evalIntrinsic (.vector (.create64 256)) [.i64 a, .i64 b, .i64 c, .i64 d] =
      some (.v256 (pack256 a b c d)) := rfl

@[simp] theorem intrinsic_bextr_flag (a : W32) :
    evalIntrinsic (.bmi1 .bextr32)
      [.i32 a, .i32 (BitVec.ofNat 32 4), .i32 (BitVec.ofNat 32 1)] =
      some (.i32 (bextr32 a 4 1)) := rfl

@[simp] theorem intrinsic_sub128 (a b : V128) :
    evalIntrinsic (.vector (.sub64 128)) [.v128 a, .v128 b] =
      some (.v128 (zip128 (· - ·) a b)) := rfl
@[simp] theorem intrinsic_add128 (a b : V128) :
    evalIntrinsic (.vector (.add64 128)) [.v128 a, .v128 b] =
      some (.v128 (zip128 (· + ·) a b)) := rfl
@[simp] theorem intrinsic_lt128 (a b : V128) :
    evalIntrinsic (.vector (.ltu64 128)) [.v128 a, .v128 b] =
      some (.v128 (zip128 (fun x y => mask64 (x.ult y)) a b)) := rfl
@[simp] theorem intrinsic_eq128 (a b : V128) :
    evalIntrinsic (.vector (.eq64 128)) [.v128 a, .v128 b] =
      some (.v128 (zip128 (fun x y => mask64 (x == y)) a b)) := rfl
@[simp] theorem intrinsic_and128 (a b : V128) :
    evalIntrinsic (.vector (.band 128)) [.v128 a, .v128 b] = some (.v128 (a &&& b)) := rfl
@[simp] theorem intrinsic_or128 (a b : V128) :
    evalIntrinsic (.vector (.bor 128)) [.v128 a, .v128 b] = some (.v128 (a ||| b)) := rfl
@[simp] theorem intrinsic_zero128 :
    evalIntrinsic (.vector (.zero 128)) [] = some (.v128 0) := rfl
@[simp] theorem intrinsic_equal_all128 (a b : V128) :
    evalIntrinsic (.vector (.equalsAll 128)) [.v128 a, .v128 b] =
      some (.i32 (if a == b then 1 else 0)) := rfl
@[simp] theorem intrinsic_adv_extract (a b : V128) :
    evalIntrinsic (.advSimd .extract64) [.v128 a, .v128 b, .i32 (BitVec.ofNat 32 1)] =
      some (.v128 (advExtract64 a b 1)) := rfl
@[simp] theorem intrinsic_sse_shift (a : V128) :
    evalIntrinsic (.sse .shiftLeftBytes) [.v128 a, .i32 (BitVec.ofNat 32 8)] =
      some (.v128 (sseShiftLeftBytes a 8)) := rfl
@[simp] theorem intrinsic_sse_align (a b : V128) :
    evalIntrinsic (.sse .alignBytes) [.v128 a, .v128 b, .i32 (BitVec.ofNat 32 8)] =
      some (.v128 (ssseAlignBytes a b 8)) := rfl
@[simp] theorem intrinsic_reinterpret128 (a : V128) :
    evalIntrinsic (.vector (.reinterpret 128)) [.v128 a] = some (.v128 a) := rfl
@[simp] theorem intrinsic_extract128 (a : V128) :
    evalIntrinsic (.vector (.extract64 128)) [.v128 a, .i32 (BitVec.ofNat 32 1)] =
      some (.i64 (lane64 a 1)) := rfl

@[simp] theorem lane128_zero (i : Nat) : lane64 (BitVec.ofNat 128 0) i = 0 := by
  simp [lane64]

@[simp] theorem adv_incoming_zero (a b : W64) :
    advExtract64 (BitVec.ofNat 128 0) (pack128 a b) 1 = pack128 0 a := by
  change advExtract64 (pack128 0 0) (pack128 a b) 1 = pack128 0 a
  exact adv_incoming 0 0 a b

end CIL.Vector
