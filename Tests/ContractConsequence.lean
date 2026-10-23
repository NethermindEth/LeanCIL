import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.OutcomeContract
import CIL.Safety.WordMemory
import CIL.Safety.WordFootprint
import CIL.Safety.ReturnMemory

/-! Synthetic extraction: `Root(v) => Percent(v) + 1`, a throwing `Percent`, `AddTo(in a, in b, out res)` and `Sum` calling it. -/
namespace Extracted

open CIL

def method0Signature : String := "System.UInt64 Consequence.Calls::Root(System.UInt64)"
def method1Signature : String := "System.UInt64 Consequence.Calls::Percent(System.UInt64)"
def method2Signature : String := "System.Void Consequence.Calls::AddTo(System.UInt64&,System.UInt64&,System.UInt64&)"
def method3Signature : String := "System.Void Consequence.Calls::Sum(System.UInt64&,System.UInt64&,System.UInt64&)"
@[cil_code] def method0 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .call 1 1, .const32 1, .convI8, .add, .ret] }
@[cil_code] def method1 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .const32 (BitVec.ofInt 32 100), .convI8, .bleu 7, .nop, .nop,
    .throw "System.ArgumentOutOfRangeException", .arg 0, .ret] }
@[cil_code] def method2 : Method := { returnsValue := false, locals := [], code :=
  [.arg 2, .arg 0, .load64, .arg 1, .load64, .add, .store64, .ret] }
@[cil_code] def method3 : Method := { returnsValue := false, locals := [], code :=
  [.arg 0, .arg 1, .arg 2, .call 2 3, .ret] }
@[cil_code] def program : Program := [method0, method1, method2, method3]
def signatures : List String := [method0Signature, method1Signature, method2Signature, method3Signature]

end Extracted

namespace Tests.ContractConsequence

open CIL.Safety

bind_method root rootBody := "System.UInt64 Consequence.Calls::Root(System.UInt64)"
bind_callee percent percentBody := "System.UInt64 Consequence.Calls::Percent(System.UInt64)" from rootBody
bind_call percentSite := percent from rootBody
bind_method sum sumBody := "System.Void Consequence.Calls::Sum(System.UInt64&,System.UInt64&,System.UInt64&)"
bind_callee addTo addBody := "System.Void Consequence.Calls::AddTo(System.UInt64&,System.UInt64&,System.UInt64&)" from sumBody
bind_call addSite := addTo from sumBody

/-! Outcome contracts: the exact internal contract and a public one that only bounds the result. -/

def percentExact : OutcomeContract CIL.W64 CIL.W64 where
  args v := [.scalar (.i64 v)]
  results out := [.scalar (.i64 out)]
  pre _ _ := True
  footprint _ := []
  post v _ _ out := out = v
  raises v _ := if v ≤ 100 then none else some "System.ArgumentOutOfRangeException"

def percentBounded : OutcomeContract CIL.W64 CIL.W64 :=
  { percentExact with post := fun _ _ _ out => out ≤ 100 }

theorem percent_exact : percentExact.Holds Extracted.program percent := by
  rintro v m -
  by_cases within : v ≤ 100
  · have bound : v ≤ 100#64 := within
    simp only [percentExact, within, ite_true]
    refine ⟨10, m, _, ?_, Confined.refl _ m, _, rfl, rfl⟩
    cil_checked_steps [bound]
  · have bound : ¬ v ≤ 100#64 := within
    simp only [percentExact, within, ite_false]
    cil_raise_steps [bound]

/-- The bound follows from the exact result on the inputs that return. -/
theorem percent_bounded_refines : percentExact.Refines percentBounded where
  args _ := rfl
  results _ := rfl
  pre _ _ permitted := permitted
  raises _ _ _ := rfl
  footprint _ _ _ _ entry member := nomatch member
  post v _ _ out _ normal _ same := by
    dsimp only [percentBounded, percentExact] at normal
    split at normal
    · exact same ▸ ‹v ≤ 100›
    · cases normal

/-- The exported form: no step of `Percent` is replayed. -/
theorem percent_bounded : percentBounded.Holds Extracted.program percent :=
  percent_exact.weaken percent_bounded_refines

def rootContract : OutcomeContract CIL.W64 CIL.W64 :=
  { percentExact with post := fun _ _ _ out => out ≤ 101 }

/-- `Root` uses only the derived bound, in both its returning and its raising outcome. -/
theorem root_holds (percentHolds : percentBounded.Holds Extracted.program percent) :
    rootContract.Holds Extracted.program root := by
  rintro v m -
  dsimp only [rootContract]
  cases raised : percentExact.raises v m with
  | some exception =>
    cil_raise_steps []
    cil_outcome_raise percentHolds v at percentSite []
    · trivial
    · exact raised
  | none =>
    cil_contract_steps []
    cil_outcome_call percentHolds v at percentSite []
    · trivial
    · exact raised
    rintro m1 _ - confined ⟨out, rfl, bound⟩
    dsimp only [percentBounded, percentExact]
    cil_contract_steps []
    refine ⟨confined, _, rfl, ?_⟩
    dsimp only [percentBounded] at bound ⊢
    bv_omega

theorem root_correct : rootContract.Holds Extracted.program root := root_holds percent_bounded

/-- A stronger pre removes the exception, so the contract is normal-only. -/
def percentInRangeOutcome : OutcomeContract CIL.W64 CIL.W64 :=
  { percentExact with pre := fun v _ => v ≤ 100, raises := fun _ _ => none }

def percentInRange : MethodContract CIL.W64 CIL.W64 := percentInRangeOutcome.toMethodContract

theorem percent_in_range_refines : percentExact.Refines percentInRangeOutcome :=
  .of_method ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => trivial, fun _ _ _ _ member => (nomatch member),
    fun _ _ _ _ _ _ same => same⟩
    fun v _ within => by
      have bound : v ≤ 100#64 := within
      simp [percentInRangeOutcome, percentExact, bound]

theorem percent_in_range : percentInRange.Holds Extracted.program percent :=
  (percent_exact.weaken percent_in_range_refines).normal fun _ _ _ => rfl

/-- Refinements compose: the bound also follows from the in-range contract. -/
theorem percent_in_range_bounded : percentInRange.Refines { percentInRange with post := fun _ _ _ out => out ≤ 100 } :=
  (MethodContract.Refines.refl percentInRange).trans
    ⟨fun _ => rfl, fun _ => rfl, fun _ _ within => within, fun _ _ _ entry member => ⟨entry, member, Within.refl _⟩,
      fun _ _ _ _ within _ same => same ▸ within⟩

#print axioms percent_bounded
#print axioms root_correct
#print axioms percent_in_range
#print axioms percent_in_range_bounded

/-! A memory contract: the public one declares the enclosing 32-byte region and exports a frame fact. -/

structure AddInput where
  a : Reference
  b : Reference
  res : Reference
  region : Reference
  x : CIL.W64
  y : CIL.W64

def addArgs (input : AddInput) : List Value :=
  [.reference (.address input.a), .reference (.address input.b), .reference (.address input.res)]

def addPre (input : AddInput) (m : Memory) : Prop :=
  read m input.a 8 1 = .ok (numberBytes input.x.toNat 8) ∧
    read m input.b 8 1 = .ok (numberBytes input.y.toNat 8) ∧ access m input.res 8 1 true = .ok ()

def addInternal : MethodContract AddInput where
  args := addArgs
  pre := addPre
  footprint input := [(input.res, 8)]
  post input _ final values := values = [] ∧ read final input.res 8 1 = .ok (numberBytes (input.x + input.y).toNat 8)

/-- `a` lies apart from `res`, so its readback survives; `res` lies inside `region`. -/
def addPublic : MethodContract AddInput where
  args := addArgs
  pre input m := m.WellFormed ∧ addPre input m ∧ Apart input.a 8 (input.res, 8) ∧ Within (input.res, 8) (input.region, 32)
  footprint input := [(input.region, 32)]
  post input _ final values := values = [] ∧
    read final input.res 8 1 = .ok (numberBytes (input.x + input.y).toNat 8) ∧
    read final input.a 8 1 = .ok (numberBytes input.x.toNat 8)

theorem add_internal : addInternal.Holds Extracted.program addTo := by
  rintro ⟨a, b, res, region, x, y⟩ m ⟨readA, readB, writable⟩
  dsimp only [addInternal, addArgs] at *
  have length : (numberBytes (x + y).toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨stored, wrote⟩ := write_succeeds (bytes := numberBytes (x + y).toNat 8) (by simpa only [length] using writable)
  have readback := write_readback _ _ _ _ _ wrote
  rw [length] at readback
  have store : storeValue m (.address res) (.i64 (x + y)) = .ok stored := by
    simp only [storeValue, CIL.Value.hasUnspecified, Bool.false_eq_true, ↓reduceIte,
      referenceAt, checkedAt, wrote, Except.mapError, Bind.bind, Except.bind]
  have fa := access_reference_valid _ _ _ _ _ (read_access readA)
  have fb := access_reference_valid _ _ _ _ _ (read_access readB)
  have fr := access_reference_valid _ _ _ _ _ writable
  have la := load_word64_of_read readA
  have lb := load_word64_of_read readB
  refine ⟨9, stored, [], ?_, Confined.write wrote (by simp [numberBytes]), _, rfl, rfl, readback⟩
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, instruction, memoryInstruction,
    observerCount, unspecifiedOperands, Value.hasUnspecified, CIL.Value.hasUnspecified,
    fa, fb, fr, la, lb, store, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The frame fact comes from the internal footprint, not from re-executing `AddTo`. -/
theorem add_public_refines : addInternal.Refines addPublic where
  args _ := rfl
  results _ := rfl
  pre _ _ permitted := permitted.2.1
  footprint _ _ permitted _ member :=
    ⟨_, List.mem_singleton_self _, List.mem_singleton.mp member ▸ permitted.2.2.2⟩
  post _ _ _ _ permitted framed satisfied :=
    ⟨satisfied.1, satisfied.2, framed.read_apart permitted.1 permitted.2.1.1 fun _ member => List.mem_singleton.mp member ▸ permitted.2.2.1⟩

theorem add_public : addPublic.Holds Extracted.program addTo := add_internal.weaken add_public_refines

def sumContract : MethodContract AddInput := { addPublic with }

/-- `Sum` composes through the derived contract at its call site; `AddTo` is not unfolded. -/
theorem sum_holds (addHolds : addPublic.Holds Extracted.program addTo) : sumContract.Holds Extracted.program sum := by
  rintro ⟨a, b, res, region, x, y⟩ m permitted
  obtain ⟨formed, ⟨readA, readB, writable⟩, apart, within⟩ := permitted
  dsimp only [sumContract, addPublic, addArgs, MethodContract.Returns] at *
  have fa := access_reference_valid _ _ _ _ _ (read_access readA)
  have fb := access_reference_valid _ _ _ _ _ (read_access readB)
  have fr := access_reference_valid _ _ _ _ _ writable
  cil_contract_steps [checkedValue, formValue, checkedAt, fa, fb, fr,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cil_contract_call addHolds ⟨a, b, res, region, x, y⟩ at addSite [checkedValue, formValue, checkedAt, fa, fb, fr,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · exact ⟨formed, ⟨readA, readB, writable⟩, apart, within⟩
  rintro m1 _ - framed ⟨_, rfl, rfl, readRes, readA1⟩
  cil_contract_steps [checkedValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp only [leaveFrame, List.foldl_nil]
  exact ⟨framed, _, rfl, rfl, readRes, readA1⟩

theorem sum_correct : sumContract.Holds Extracted.program sum := sum_holds add_public

#print axioms add_public
#print axioms sum_correct

/-! Rejected derivations: each premise fails on a concrete input, and the derived contract is false. -/
namespace Rejected

/-- One 24-byte writable allocation holding the words 1, 1 and 0. -/
def sample : Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨24, 1, []⟩, true, [24]⟩ else none
  cells := fun _ offset => ⟨if offset = 0 ∨ offset = 8 then 1 else 0, true⟩
  views := [⟨0, 0, 24, true, true⟩]
  nextIdentity := 1 }

def sampleInput : AddInput := ⟨⟨0, 0⟩, ⟨0, 8⟩, ⟨0, 16⟩, ⟨0, 0⟩, 1, 1⟩

theorem sample_pre : addPre sampleInput sample := ⟨rfl, rfl, rfl⟩

theorem raises_unique {program : CIL.Program} {method : Nat} {args : List Value} {memory : Memory}
    {one other : String} (first : Raises program method args memory one)
    (second : Raises program method args memory other) : one = other := by
  obtain ⟨_, fault, ran, thrown⟩ := first
  obtain ⟨_, fault', ran', thrown'⟩ := second
  cases invoke_unique (by simp [Settled, thrown]) (by simp [Settled, thrown']) ran ran'
  rw [thrown] at thrown'
  cases thrown'
  rfl

theorem raises_not_returns {program : CIL.Program} {method fuel : Nat} {args : List Value} {memory : Memory}
    {exception : String} {result : Memory × List Value} (raised : Raises program method args memory exception)
    (returned : invoke program fuel method args memory = .ok result) : False := by
  obtain ⟨_, fault, ran, thrown⟩ := raised
  cases invoke_unique (second := .ok result) (by simp [Settled, thrown]) trivial ran returned

theorem percent_returns {v : CIL.W64} (within : v ≤ 100) (m : Memory) :
    ∃ fuel final, invoke Extracted.program fuel percent [.scalar (.i64 v)] m = .ok (final, [.scalar (.i64 v)]) := by
  obtain ⟨fuel, final, values, invoked, -, out, encoded, same⟩ :=
    percent_exact.returning (input := v) (initial := m) trivial (by
      have bound : v ≤ 100#64 := within
      simp [percentExact, bound])
  dsimp only [percentExact] at encoded same
  subst same encoded
  exact ⟨fuel, final, invoked⟩

/-- An unjustified stronger post: `Percent(100)` returns 100. -/
def percentTooStrong : OutcomeContract CIL.W64 CIL.W64 :=
  { percentExact with post := fun _ _ _ out => out < 100 }

theorem stronger_post_not_refines : ¬ percentExact.Refines percentTooStrong := fun refines => by
  have bound : (100 : CIL.W64) < 100 := refines.post 100 sample sample 100 trivial (by decide) (Confined.refl _ _) rfl
  exact absurd bound (by decide)

theorem stronger_post_rejected : ¬ percentTooStrong.Holds Extracted.program percent := fun holds => by
  have outcome := holds 100 sample trivial
  simp only [percentTooStrong, percentExact, show (100 : CIL.W64) ≤ 100 by decide, ite_true] at outcome
  obtain ⟨fuel, final, values, invoked, -, out, rfl, bound⟩ := outcome
  obtain ⟨fuel', final', invoked'⟩ := percent_returns (v := 100) (by decide) sample
  have same := invoke_ok_unique invoked invoked'
  simp only [Prod.mk.injEq, List.cons.injEq, Value.scalar.injEq, CIL.Value.i64.injEq, and_true] at same
  rw [same.2] at bound
  exact absurd (show (100 : CIL.W64) < 100 from bound) (by decide)

/-- A weaker pre: `Percent(101)` raises, so it cannot be promised to return. -/
def percentUnguarded : MethodContract CIL.W64 CIL.W64 := { percentInRange with pre := fun _ _ => True }

theorem weaker_pre_not_refines : ¬ percentInRange.Refines percentUnguarded := fun refines => by
  have bound : (101 : CIL.W64) ≤ 100 := refines.pre 101 sample trivial
  exact absurd bound (by decide)

theorem weaker_pre_rejected : ¬ percentUnguarded.Holds Extracted.program percent := fun holds => by
  obtain ⟨fuel, final, values, invoked, -⟩ := holds 101 sample trivial
  exact raises_not_returns (percent_exact.raising (input := 101) (exception := "System.ArgumentOutOfRangeException") trivial (by decide)) invoked

/-- A smaller footprint: `AddTo` changes `res`, which an empty footprint keeps. -/
def addUnframed : MethodContract AddInput := { addInternal with footprint := fun _ => [] }

theorem smaller_footprint_not_refines : ¬ addInternal.Refines addUnframed := fun refines => by
  obtain ⟨_, member, _⟩ := refines.footprint sampleInput sample sample_pre _ (List.mem_singleton_self _)
  exact nomatch member

theorem smaller_footprint_rejected : ¬ addUnframed.Holds Extracted.program addTo := fun holds => by
  obtain ⟨_, final, values, invoked, framed, -⟩ := holds sampleInput sample sample_pre
  obtain ⟨_, final', values', invoked', -, _, rfl, -, readback⟩ := add_internal sampleInput sample sample_pre
  have same := congrArg Prod.fst (invoke_ok_unique invoked invoked')
  dsimp only at same
  subst same
  have kept := framed.read_eq sampleInput.res (by decide) 8 1 fun _ _ => Outside.nil _ _
  have zero : read sample sampleInput.res 8 1 = .ok (numberBytes 0 8) := rfl
  rw [readback, zero] at kept
  exact absurd (Except.ok.inj kept) (by decide)

/-- A changed exception type: `Percent(101)` throws `ArgumentOutOfRangeException`. -/
def percentRenamed : OutcomeContract CIL.W64 CIL.W64 :=
  { percentBounded with raises := fun v _ => if v ≤ 100 then none else some "System.ArgumentException" }

theorem changed_exception_not_refines : ¬ percentExact.Refines percentRenamed := fun refines =>
  absurd (refines.raises 101 sample trivial) (by decide)

theorem changed_exception_rejected : ¬ percentRenamed.Holds Extracted.program percent := fun holds => by
  have renamed : Raises Extracted.program percent [.scalar (.i64 101)] sample "System.ArgumentException" :=
    holds.raising (input := 101) trivial (by decide)
  exact absurd (raises_unique renamed (percent_exact.raising (input := 101) (exception := "System.ArgumentOutOfRangeException") trivial (by decide))) (by decide)

#print axioms stronger_post_not_refines
#print axioms stronger_post_rejected
#print axioms weaker_pre_not_refines
#print axioms weaker_pre_rejected
#print axioms smaller_footprint_not_refines
#print axioms smaller_footprint_rejected
#print axioms changed_exception_not_refines
#print axioms changed_exception_rejected

end Rejected

end Tests.ContractConsequence
