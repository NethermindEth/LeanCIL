import CIL.Safety.SymbolicExecution

/-!
# Reviewed integer binding families

These small shared execution proofs are independent of extraction. Generated bindings must
prove the complete method equality and the exact managed signature before instantiation.
-/

namespace BindingSupport
open CIL CIL.Safety

/-- The fixed body of an equality or inequality method, including boolean return narrowing. -/
@[cil_code] def equalityBody (profile : FeatureProfile) (environment : LayoutEnvironment)
    (declared : DeclaredSignature) (positive : Bool) : Method := {
  profile, environment, declared, locals := [], returnsValue := true,
  code := [.arg 0, .arg 1, .ceq] ++
    (if positive then [] else [.ldc_i4 0, .ceq]) ++ [.ret (some .unsigned8)] }

/-- The fixed body of one binary bitwise method. -/
@[cil_code] def bitwiseBody (profile : FeatureProfile) (environment : LayoutEnvironment)
    (declared : DeclaredSignature) (operation : Instruction) : Method := {
  profile, environment, declared, locals := [], returnsValue := true,
  code := [.arg 0, .arg 1, operation, .ret] }

/-- The equality family computes its boolean in arbitrary caller memory. -/
theorem equal32 (program : Program) (profile : FeatureProfile)
    (environment : LayoutEnvironment)
    (declared : DeclaredSignature)
    (found : program[0]? = some (equalityBody profile environment declared true))
    (left right : W32) (memory : Safety.Memory) :
    invoke program 5 0 [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 (if left = right then 1 else 0))]) := by
  cil_checked_steps [found]
#print axioms equal32

/-- The opposite polarity computes inequality rather than weakening the equality contract. -/
theorem different64 (program : Program) (profile : FeatureProfile)
    (environment : LayoutEnvironment)
    (declared : DeclaredSignature)
    (found : program[0]? = some (equalityBody profile environment declared false))
    (left right : W64) (memory : Safety.Memory) :
    invoke program 7 0 [.scalar (.i64 left), .scalar (.i64 right)] memory =
      .ok (memory, [.scalar (.i32 (if left ≠ right then 1 else 0))]) := by
  cil_checked_steps [found]
  all_goals (by_cases same : left = right <;> simp [same])
#print axioms different64

/-- The conjunction family computes the complete 32-bit result. -/
theorem and32 (program : Program) (profile : FeatureProfile)
    (environment : LayoutEnvironment)
    (declared : DeclaredSignature)
    (found : program[0]? = some (bitwiseBody profile environment declared .and))
    (left right : W32) (memory : Safety.Memory) :
    invoke program 5 0 [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 (left &&& right))]) := by
  cil_checked_steps [found]
#print axioms and32

/-- The exclusive-or family computes the complete 64-bit result. -/
theorem xor64 (program : Program) (profile : FeatureProfile)
    (environment : LayoutEnvironment)
    (declared : DeclaredSignature)
    (found : program[0]? = some (bitwiseBody profile environment declared .xor))
    (left right : W64) (memory : Safety.Memory) :
    invoke program 5 0 [.scalar (.i64 left), .scalar (.i64 right)] memory =
      .ok (memory, [.scalar (.i64 (left ^^^ right))]) := by
  cil_checked_steps [found]
#print axioms xor64

end BindingSupport
