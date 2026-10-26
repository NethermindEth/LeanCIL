import CIL.Extraction.Folds
/-! Kernel benchmark for complete span-receiver role discovery, including count construction. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CIL CIL.Extraction
/-- A supported byte span. -/
def span : TypeExpr := .apply (.constructor runtimeScope "System.Span`1")
  (.atom runtimeScope "System.Byte")
/-- A receiver call that completes a span fold. -/
def spanLength : RawInstruction := ⟨0, 40, .call {
  declaringType := span,
  name := "get_Length", target := .external "", typeArguments := [], parameterCount := 0,
  hasThis := true, returnsValue := true}⟩
/-- Each local has exactly one store and one address load. -/
def code (size : Nat) : List RawInstruction := (List.range size).flatMap fun index =>
  [⟨0, 19, .local index⟩, ⟨0, 18, .local index⟩, spanLength]
/-- Every receiver pair folds and each following call retains its ordinary role. -/
def expected (size : Nat) : List (Option FoldRole) :=
  (List.replicate size [some .head, some .interior, none]).flatten
/-- Full role discovery includes constructing and querying the local-use index. -/
theorem countedReceivers :
    foldRoles (List.replicate 256 span) (code 256) = expected 256 := by decide +kernel
#print axioms countedReceivers
