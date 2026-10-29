import CIL.Extraction.Scalars

/-! Fixed straight-line certificate workload for checking and kernel replay measurements. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace CertificateFlowScaling
open CIL CIL.Extraction

/-- A void method whose only successor at each ordinary site is fallthrough. -/
def raw (count : Nat) : RawMethod := {
  token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := true, maxStack := 1,
  genericParameters := [], code := List.replicate count ⟨0, 0, .none⟩ ++ [⟨0, 42, .none⟩] }

/-- The feature certificate contains an empty stack at every site. -/
def features (count : Nat) : FeatureCertificate :=
  List.replicate (count + 1) (some ⟨[], []⟩)

/-- The scalar certificate contains an empty stack at every site. -/
def scalars (count : Nat) : ScalarCertificate := List.replicate (count + 1) (some [])

/-- Every nop falls through to the final void return. -/
def code (count : Nat) : List Op := List.replicate count .nop ++ [.ret]

set_option profiler true in
/-- Fixed feature validation workload, reduced by the kernel. -/
theorem feature_valid : FeatureFlowValid #[] (raw 512) .scalar (features 512)
    (List.replicate 513 true) (code 512) := by decide
#print axioms feature_valid

set_option profiler true in
/-- Fixed scalar validation workload, reduced by the kernel. -/
theorem scalar_valid : ScalarFlowValid #[] (raw 512) (features 512) (scalars 512) (code 512) := by
  decide
#print axioms scalar_valid

end CertificateFlowScaling
