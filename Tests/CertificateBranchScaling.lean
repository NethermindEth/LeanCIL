import CIL.Extraction.Scalars

/-!
Fixed mixed forward/backward branch workload for checking and kernel replay measurements.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace CertificateBranchScaling
open CIL CIL.Extraction

/-- A void method with distinct branch targets in reverse order. -/
def raw (count : Nat) : RawMethod := {
  token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := true, maxStack := 1,
  genericParameters := [],
  code := (List.range count).map (fun pc => ⟨pc, 43, .target (count - pc)⟩) ++ [⟨0, 42, .none⟩] }

/-- The feature certificate contains an empty stack at every site. -/
def features (count : Nat) : FeatureCertificate :=
  List.replicate (count + 1) (some ⟨[], []⟩)

/-- The scalar certificate contains an empty stack at every site. -/
def scalars (count : Nat) : ScalarCertificate := List.replicate (count + 1) (some [])

/-- Forward edges, a self edge and backedges retain their exact destinations. -/
def code (count : Nat) : List Op :=
  (List.range count).map (fun pc => .branch (count - pc)) ++ [.ret]

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

end CertificateBranchScaling
