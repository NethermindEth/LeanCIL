import CIL.Safety.SymbolicExecution
/-! Feature facts for checked execution through the shared value evaluator. -/

namespace Tests.FeatureExecution
/-- A method returning a single profile feature test. -/
@[cil_code] def featureMethod (profile : CIL.FeatureProfile) (feature : CIL.Feature) :
    CIL.Method := { profile, code := [.feature feature, .ret], locals := [], returnsValue := true }
/-- A caller fact decides an unknown feature without unfolding its dispatcher. -/
theorem symbolic_feature (profile : CIL.FeatureProfile) (feature : CIL.Feature)
    (enabled : profile.evaluate feature = true) (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke [featureMethod profile feature] 3 0 [] memory =
      .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps [enabled]
#print axioms symbolic_feature
/-- A disabled symbolic feature returns zero without splitting on its constructors. -/
theorem symbolic_feature_disabled (profile : CIL.FeatureProfile) (feature : CIL.Feature)
    (disabled : profile.evaluate feature = false) (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke [featureMethod profile feature] 3 0 [] memory =
      .ok (memory, [.scalar (.i32 0)]) := by
  cil_checked_steps [disabled]
#print axioms symbolic_feature_disabled

/-- A concrete feature is reduced to the profile field named by the caller. -/
theorem concrete_feature (profile : CIL.FeatureProfile)
    (enabled : profile.avx2 = true) (memory : CIL.Safety.Memory) :
    CIL.Safety.invoke [featureMethod profile .avx2] 3 0 [] memory =
      .ok (memory, [.scalar (.i32 1)]) := by
  cil_checked_steps [enabled]
#print axioms concrete_feature

end Tests.FeatureExecution


