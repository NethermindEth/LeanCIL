import CIL.Extraction.Scalars

/-!
# Certificate lookup regressions

Forward edges, backedges, empty certificates, unreachable targets and bounds exercise the
same feature/scalar validators used by extracted methods, including the streaming endpoint.
-/

namespace Tests.CertificateFlow
open CIL CIL.Extraction

/-- Small void methods isolate successor-state validation. -/
private def raw (code : List RawInstruction) : RawMethod := {
  token := 1, owner := "Flow", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := true, maxStack := 1,
  genericParameters := [], code }

/-- The only reachable stack in these fixtures is empty. -/
private def emptyState : Option FeatureState := some ⟨[], []⟩

/-- An unconditional forward edge reaches the final certificate entry. -/
private def forward : RawMethod := raw
  [⟨0, 43, .target 3⟩, ⟨1, 0, .none⟩, ⟨2, 0, .none⟩, ⟨3, 42, .none⟩]

/-- Pruned sites retain explicit holes. -/
private def forwardCode : List Op := [.branch 3, .unsupported "hole", .unsupported "hole", .ret]

/-- Only the branch and its destination are reachable. -/
private def forwardFeatures : FeatureCertificate := [emptyState, none, none, emptyState]

/-- Scalar reachability agrees exactly with feature reachability. -/
private def forwardScalars : ScalarCertificate := [some [], none, none, some []]

/-- Forward lookup accepts the final in-bounds entry in both certificates. -/
theorem forward_valid :
    FeatureFlowValid #[] forward .scalar forwardFeatures [true, false, false, true] forwardCode ∧
    ScalarFlowValid #[] forward forwardFeatures forwardScalars forwardCode := by decide
#print axioms forward_valid

/-- A target absent from either certificate cannot be accepted as an empty stack. -/
theorem missing_target_rejected :
    ¬ FeatureFlowValid #[] forward .scalar [emptyState, none, none, none]
      [true, false, false, false] forwardCode ∧
    ¬ ScalarFlowValid #[] forward forwardFeatures [some [], none, none, none] forwardCode ∧
    ¬ ScalarFlowValid #[] forward [emptyState, none, none, none] forwardScalars forwardCode := by
  decide
#print axioms missing_target_rejected

/-- One-past-end and very large branch targets remain invalid. -/
theorem bounds_rejected :
    ([4, 1000000] : List Nat).all (fun target =>
      let body := { forward with code := forward.code.set 0 ⟨0, 43, .target target⟩ }
      let emitted := forwardCode.set 0 (.branch target)
      !decide (FeatureFlowValid #[] body .scalar forwardFeatures [true, false, false, true] emitted) &&
      !decide (ScalarFlowValid #[] body forwardFeatures forwardScalars emitted)) = true := by decide
#print axioms bounds_rejected

/-- A backward branch can target entry after streaming through several fallthroughs. -/
theorem backedge_valid :
    let body := raw [⟨0, 0, .none⟩, ⟨1, 0, .none⟩, ⟨2, 43, .target 0⟩]
    let features := List.replicate 3 emptyState
    let emitted := [.nop, .nop, .branch 0]
    FeatureFlowValid #[] body .scalar features [true, true, true] emitted ∧
    ScalarFlowValid #[] body features (List.replicate 3 (some [])) emitted := by decide
#print axioms backedge_valid

/-- The end of a certificate is not an implicit successor for a final nop. -/
theorem missing_fallthrough_rejected :
    ¬ FeatureFlowValid #[] (raw [⟨0, 0, .none⟩]) .scalar [emptyState] [true] [.nop] ∧
    ¬ ScalarFlowValid #[] (raw [⟨0, 0, .none⟩]) [emptyState] [some []] [.nop] := by decide
#print axioms missing_fallthrough_rejected

/-- Empty certificates still fail the mandatory entry check. -/
theorem empty_rejected :
    ¬ FeatureFlowValid #[] (raw []) .scalar [] [] [] ∧
    ¬ ScalarFlowValid #[] (raw []) [] [] [] := by decide
#print axioms empty_rejected

/-- Pairing certificates cannot hide a missing or extra entry. -/
theorem lengths_rejected :
    ¬ ScalarFlowValid #[] forward (forwardFeatures ++ [none]) forwardScalars forwardCode ∧
    ¬ ScalarFlowValid #[] forward forwardFeatures (forwardScalars ++ [none]) forwardCode ∧
    ¬ FeatureFlowValid #[] forward .scalar (forwardFeatures ++ [none])
      [true, false, false, true, false] forwardCode := by decide
#print axioms lengths_rejected

end Tests.CertificateFlow
