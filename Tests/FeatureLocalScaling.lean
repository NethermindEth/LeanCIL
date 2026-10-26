import CIL.Extraction.FeatureLocals

/-! Isolated kernel workload for local eligibility; every state contains known facts. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace FeatureLocalScaling
open CIL CIL.Extraction

/-- A raw body with independent instruction and local counts and no address-taking. -/
def raw (instructions locals : Nat) : RawMethod := {
  token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [],
  locals := List.replicate locals (.atom runtimeScope "System.Int32"),
  initLocals := true, maxStack := 1, genericParameters := [],
  code := List.replicate instructions ⟨0, 0, .none⟩ }

/-- Each certificate state checks a known word in every local, exercising the slow path. -/
def allStates (instructions locals : Nat) (eligible : Nat → Option W32 → Bool) : Bool :=
  (List.range instructions).all fun pc =>
    (List.range locals).all fun index => eligible index (some (BitVec.ofNat 32 pc))

/-- Raw scanning repeats address and type checks for every known fact at every pc. -/
def scanned (instructions locals : Nat) : Bool :=
  allStates instructions locals (featureLocalEligible (raw instructions locals))

/-- The same workload shares the checked local index across all states. -/
def indexed (instructions locals : Nat) : Bool :=
  allStates instructions locals (FeatureLocalIndex.ofRaw (raw instructions locals)).eligible

set_option profiler true in
/-- The original known-fact workload with 128 instructions and 128 locals. -/
theorem scanned128 : scanned 128 128 = true := by decide +kernel
#print axioms scanned128

set_option profiler true in
/-- The indexed version checks exactly the same known facts. -/
theorem indexed128 : indexed 128 128 = true := by decide +kernel
#print axioms indexed128

end FeatureLocalScaling
