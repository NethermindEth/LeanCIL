import Templates
import CIL.Safety.SymbolicExecution

/-! One proof over the generated template, independent of concrete extracted bodies. -/
namespace TemplateProof
open CIL CIL.Safety

/-- The generated helper returns its argument for any profile. -/
theorem helper_returns (program : Program) (index : Nat) (profile : FeatureProfile)
    (found : program[index]? = some (Templates.method1 profile))
    (memory : Safety.Memory) (value : W32) :
    invoke program 10 index [.scalar (.i32 value)] memory =
      .ok (memory, [.scalar (.i32 value)]) := by
  cil_checked_steps
#print axioms helper_returns

/-- All selected dispatch combinations share this proof and the generated body. -/
theorem choose_returns (program : Program) (index callee : Nat) (profile : FeatureProfile)
    (sse42 avx2 : Bool) (sse : profile.sse42 = sse42) (avx : profile.avx2 = avx2)
    (covered : avx2 = true → sse42 = true)
    (found : program[index]? = some (Templates.method0 profile sse42 avx2 callee))
    (helper : avx2 = true → program[callee]? = some (Templates.method1 profile))
    (memory : Safety.Memory) (left right : W32) :
    invoke program 30 index [.scalar (.i32 left), .scalar (.i32 right)] memory =
      .ok (memory, [.scalar (.i32 (if avx2 then left else if sse42 then right else left))]) := by
  cases sse42 <;> cases avx2
  · cil_checked_steps [sse, avx]
  · cases covered rfl
  · cil_checked_steps [sse, avx]
  · have called := helper rfl
    cil_checked_steps [sse, avx, called]
#print axioms choose_returns

/-- An unselected combination cannot start executing the generated dispatch template. -/
theorem unselected_flags (profile : FeatureProfile) (callee : Nat) :
    (Templates.method0 profile false true callee).code[0]? =
      some (.unsupported "Profile combination not selected for template") := rfl
#print axioms unselected_flags
end TemplateProof
