import CIL.Safety.DecodedSummary
import CIL.Safety.SegmentContract

/-!
# Contracts for decoded instruction regions

A region summary binds a nonempty instruction sequence at a program counter to the decoded
method that contains it. Reuse in another extraction requires a binding for the destination
and agreement on a closed region covering the sequence and its possible continuations.
-/

namespace CIL.Safety

open CIL.Extraction

/-- A segment contract retains its exits and footprint in a program that agrees on a closed
    region containing the entry and every continuation permitted by the contract. -/
theorem SegmentContract.Holds.congr_region {contract : SegmentContract} {program other : Program}
    {region : Nat → Nat → Prop} {method start : Nat} (holds : contract.Holds program method start)
    (closed : RegionClosed program region) (agrees : AgreesOn program other region)
    (entry : region method start)
    (continues : ∀ args before pc after, contract.pre args before →
      contract.post args before (.reaches pc after) → region method pc) :
    contract.Holds other method start := by
  intro args before permitted
  obtain ⟨exit, ran, framed, post⟩ := holds args before permitted
  refine ⟨exit, ?_, framed, post⟩
  have same := fun fuel => run_congr_region closed agrees fuel method start args before.frame
    before.stack before.memory entry
  cases exit with
  | reaches pc after =>
    obtain ⟨cost, positive, reached⟩ := ran
    exact ⟨cost, positive, reached.congr_region closed agrees entry
      (continues args before pc after permitted post)⟩
  | returns memory values =>
    obtain ⟨fuel, returned⟩ := ran
    exact ⟨fuel, (same fuel).trans returned⟩
  | faults fault =>
    obtain ⟨definite, fuel, faulted⟩ := ran
    exact ⟨definite, fuel, (same fuel).trans faulted⟩
  | diverges =>
    intro fuel
    obtain ⟨fault, exhausted, faulted⟩ := ran fuel
    exact ⟨fault, exhausted, (same fuel).trans faulted⟩

#print axioms SegmentContract.Holds.congr_region

/-- A checked contract for the instructions starting with `first` at `start` in the named
    method. The evidence fixes its defining assembly, type arguments, body bytes and layout. -/
structure DecodedSegmentSummary (program : Program) (evidence : List MethodEvidence)
    (profile : FeatureProfile) (environment : LayoutEnvironment) (method start : Nat)
    (pin : AssemblyPin) (token : Nat) (arguments : List TypeExpr)
    (first : Instruction) (rest : List Instruction) (contract : SegmentContract) : Prop where
  bound : DecodedAt program evidence profile environment method pin token arguments
  placed : ∃ body, program[method]? = some body ∧ CodeAt body start (first :: rest)
  holds : contract.Holds program method start

/-- An independently bound destination can reuse the proof when the sequence, the reachable
    instructions and their method metadata agree, including any callees in the region. -/
theorem DecodedSegmentSummary.congr_region {program other : Program} {method start : Nat}
    {evidence otherEvidence : List MethodEvidence} {profile otherProfile : FeatureProfile}
    {environment otherEnvironment : LayoutEnvironment} {pin otherPin : AssemblyPin}
    {token otherToken : Nat} {arguments otherArguments : List TypeExpr} {first : Instruction}
    {rest : List Instruction} {contract : SegmentContract} {region : Nat → Nat → Prop}
    (summary : DecodedSegmentSummary program evidence profile environment method start
      pin token arguments first rest contract)
    (target : DecodedAt other otherEvidence otherProfile otherEnvironment method
      otherPin otherToken otherArguments)
    (closed : RegionClosed program region) (agrees : AgreesOn program other region)
    (inside : ∀ i, i < (first :: rest).length → region method (start + i))
    (continues : ∀ args before pc after, contract.pre args before →
      contract.post args before (.reaches pc after) → region method pc) :
    DecodedSegmentSummary other otherEvidence otherProfile otherEnvironment method start
      otherPin otherToken otherArguments first rest contract := by
  have entry : region method start := by simpa using inside 0 (by simp)
  obtain ⟨body, found, placed⟩ := summary.placed
  obtain ⟨destination, present, _, _⟩ := agrees.2 method start body entry found
  refine ⟨target, ⟨destination, present, CodeAt.iff_lookup.mpr ?_⟩,
    summary.holds.congr_region closed agrees entry continues⟩
  intro i bound
  obtain ⟨same, lookup, _, instruction⟩ := agrees.2 method (start + i) body (inside i bound) found
  cases present.symm.trans lookup
  exact instruction.trans (CodeAt.iff_lookup.mp placed i bound)

#print axioms DecodedSegmentSummary.congr_region

/-- Adjacent decoded regions compose when the first reaches the second's precondition and
    their permitted writes fit the combined footprint. The final state satisfies both
    postconditions through the same intermediate state. -/
theorem DecodedSegmentSummary.then {program : Program} {evidence : List MethodEvidence}
    {profile : FeatureProfile} {environment : LayoutEnvironment} {method start finish : Nat}
    {pin : AssemblyPin} {token : Nat} {arguments : List TypeExpr}
    {first second : Instruction} {left right : List Instruction}
    {firstPre secondPre : List Value → SegmentState → Prop}
    {firstPost secondPost : List Value → SegmentState → SegmentState → Prop}
    {firstFoot secondFoot footprint : List Value → SegmentState → List (Reference × Nat)}
    (head : DecodedSegmentSummary program evidence profile environment method start pin token
      arguments first left (.continuing (start + (first :: left).length) firstPre firstPost
        firstFoot))
    (tail : DecodedSegmentSummary program evidence profile environment method
      (start + (first :: left).length) pin token arguments second right
      (.continuing finish secondPre secondPost secondFoot))
    (links : ∀ args before after, firstPre args before → firstPost args before after →
      secondPre args after)
    (covers : ∀ args before after, firstPre args before → firstPost args before after →
      (∀ entry ∈ firstFoot args before, entry ∈ footprint args before) ∧
      (∀ entry ∈ secondFoot args after, entry ∈ footprint args before)) :
    DecodedSegmentSummary program evidence profile environment method start pin token arguments
      first (left ++ second :: right) (.continuing finish firstPre
        (fun args before final =>
          ∃ after, firstPost args before after ∧ secondPost args after final)
        footprint) := by
  obtain ⟨body, found, leftPlaced⟩ := head.placed
  obtain ⟨other, same, rightPlaced⟩ := tail.placed
  cases found.symm.trans same
  exact ⟨head.bound, ⟨body, found, leftPlaced.append rightPlaced⟩,
    head.holds.then tail.holds links covers⟩

#print axioms DecodedSegmentSummary.then

end CIL.Safety
