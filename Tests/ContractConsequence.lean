import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.OutcomeContract
import CIL.Safety.WordMemory
import CIL.Safety.WordFootprint
import CIL.Safety.ReturnMemory
import CIL.Safety.Forwarders

/-! Synthetic extraction: `Root(v) => Percent(v) + 1`, a throwing `Percent`,
    `AddTo(in a, in b, out res)`, `Sum` and `SumSwapped(in b, in a, out res)` forwarding to it,
    `SumDiscard(in a, in b)` forwarding with a discarded out local, and `IsZero(v)` with its
    forwarder `IsZeroForward(v)`. -/
namespace Extracted

open CIL

def method0Signature : String := "System.UInt64 Consequence.Calls::Root(System.UInt64)"
def method1Signature : String := "System.UInt64 Consequence.Calls::Percent(System.UInt64)"
def method2Signature : String := "System.Void Consequence.Calls::AddTo(System.UInt64&,System.UInt64&,System.UInt64&)"
def method3Signature : String := "System.Void Consequence.Calls::Sum(System.UInt64&,System.UInt64&,System.UInt64&)"
def method4Signature : String :=
  "System.Void Consequence.Calls::SumSwapped(System.UInt64&,System.UInt64&,System.UInt64&)"
def method5Signature : String :=
  "System.Void Consequence.Calls::SumDiscard(System.UInt64&,System.UInt64&)"
def method6Signature : String := "System.Boolean Consequence.Calls::IsZero(System.UInt64)"
def method7Signature : String := "System.Boolean Consequence.Calls::IsZeroForward(System.UInt64)"
@[cil_code] def method0 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .call 1 1, .const32 1, .convI8, .add, .ret] }
@[cil_code] def method1 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .const32 (BitVec.ofInt 32 100), .convI8, .bleu 7, .nop, .nop,
    .throw "System.ArgumentOutOfRangeException", .arg 0, .ret] }
@[cil_code] def method2 : Method := { returnsValue := false, locals := [], code :=
  [.arg 2, .arg 0, .load64, .arg 1, .load64, .add, .store64, .ret] }
@[cil_code] def method3 : Method := { returnsValue := false, locals := [], code :=
  [.arg 0, .arg 1, .arg 2, .call 2 3, .ret] }
@[cil_code] def method4 : Method := { returnsValue := false, locals := [], code :=
  [.arg 1, .arg 0, .arg 2, .call 2 3, .ret] }
@[cil_code] def method5 : Method :=
  { returnsValue := false, locals := [.unmodeled], localKinds := [.word64], code :=
    [.arg 0, .arg 1, .localAddr 0, .call 2 3, .ret] }
@[cil_code] def method6 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .const32 0, .convI8, .eq, .ret (some .unsigned8)] }
@[cil_code] def method7 : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .call 6 1, .ret (some .unsigned8)] }
@[cil_code] def program : Program :=
  [method0, method1, method2, method3, method4, method5, method6, method7]
def signatures : List String :=
  [method0Signature, method1Signature, method2Signature, method3Signature, method4Signature,
    method5Signature, method6Signature, method7Signature]

end Extracted

namespace Tests.ContractConsequence

open CIL.Safety

bind_method root rootBody := "System.UInt64 Consequence.Calls::Root(System.UInt64)"
bind_callee percent percentBody := "System.UInt64 Consequence.Calls::Percent(System.UInt64)" from rootBody
bind_call percentSite := percent from rootBody
bind_method sum sumBody := "System.Void Consequence.Calls::Sum(System.UInt64&,System.UInt64&,System.UInt64&)"
bind_callee addTo addBody := "System.Void Consequence.Calls::AddTo(System.UInt64&,System.UInt64&,System.UInt64&)" from sumBody
bind_call addSite := addTo from sumBody
bind_method swapped swappedBody :=
  "System.Void Consequence.Calls::SumSwapped(System.UInt64&,System.UInt64&,System.UInt64&)"
bind_method discard discardBody :=
  "System.Void Consequence.Calls::SumDiscard(System.UInt64&,System.UInt64&)"
bind_method isZero isZeroBody := "System.Boolean Consequence.Calls::IsZero(System.UInt64)"
bind_method isZeroForward isZeroForwardBody :=
  "System.Boolean Consequence.Calls::IsZeroForward(System.UInt64)"

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

/-! Forwarders: each inherits its callee's contract without stepping either body, the
    argument order given by the indices the forwarder loads. -/

/-- `Sum` passes its arguments through in order, so it meets `addPublic` itself. -/
theorem sum_forwards : sumContract.Holds Extracted.program sum :=
  add_public.forward (indices := [0, 1, 2]) (narrow := none) sum.found addTo.found
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun _ _ member => member) (fun _ _ _ => rfl)
    (fun _ _ _ _ _ => trivial)

#print axioms sum_forwards

/-- `SumSwapped(b, a, res)` encodes the same input with its first two arguments swapped. -/
def swappedArgs (input : AddInput) : List Value :=
  [.reference (.address input.b), .reference (.address input.a),
    .reference (.address input.res)]

/-- The swapped forwarder meets `addPublic` over its own argument order: the frame fact
    about `a` follows from `AddTo`'s footprint although `a` is now the second argument. -/
theorem swapped_forwards : (addPublic.forward swappedArgs).Holds Extracted.program swapped :=
  add_public.forward (indices := [1, 0, 2]) (narrow := none) (forwarded := swappedArgs)
    swapped.found addTo.found ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl)
    (fun _ _ member => by
      simp only [swappedArgs, addPublic, addArgs, List.mem_cons, List.not_mem_nil, or_false]
        at member ⊢
      rcases member with same | same | same <;> simp [same])
    (fun _ _ _ => rfl) (fun _ _ _ _ _ => trivial)

#print axioms swapped_forwards

/-- The indices are checked against the body: `SumSwapped` is not an in-order forwarder. -/
theorem swapped_not_in_order :
    ¬ Forwards swappedBody addBody [0, 1, 2] addTo none := fun forwards => by
  have code := forwards.code
  simp [swappedBody, Extracted.method4, forwarderCode] at code

#print axioms swapped_not_in_order

/-- Each argument must reach `AddTo`: one passing `b` twice would not supply `a`. -/
theorem duplicated_not_selected :
    ¬ ∀ input : AddInput, [0, 0, 2].map (fun index => (swappedArgs input)[index]?) =
      (addPublic.args input).map some := fun selected => by
  have same := selected ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, 0, 0⟩
  simp [swappedArgs, addPublic, addArgs] at same

#print axioms duplicated_not_selected

/-- `SumDiscard(a, b)` reads the words at `a` and `b`, which hold `x` and `y`. -/
structure DiscardInput where
  a : Reference
  b : Reference
  x : CIL.W64
  y : CIL.W64

/-- `SumDiscard`'s contract: `AddTo`'s write lands in the forwarder's own local, so callers
    see an empty footprint and `a` unchanged. -/
def discardContract : MethodContract DiscardInput where
  args input := [.reference (.address input.a), .reference (.address input.b)]
  pre input m := m.WellFormed ∧ read m input.a 8 1 = .ok (numberBytes input.x.toNat 8) ∧
    read m input.b 8 1 = .ok (numberBytes input.y.toNat 8)
  footprint _ := []
  post input _ final values := values = [] ∧
    read final input.a 8 1 = .ok (numberBytes input.x.toNat 8)

/-- The out local is fresh, so `AddTo`'s footprint drops out and `a` keeps its bytes; the
    forwarder's frame is never stepped by hand. -/
theorem discard_forwards : discardContract.Holds Extracted.program discard :=
  add_internal.forward_out (indices := [0, 1]) (narrow := none) (kind := .word64)
    (fun input home => ⟨input.a, input.b, home, home, input.x, input.y⟩)
    discard.found addTo.found ⟨rfl, rfl, rfl, nofun, rfl, rfl, rfl, rfl⟩ (fun _ _ => rfl)
    (fun _ _ ⟨formed, readA, readB⟩ => ⟨formed, fun value member => by
      simp only [discardContract, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same <;> subst same
      · exact access_reference_valid _ _ _ _ _ (read_access readA)
      · exact access_reference_valid _ _ _ _ _ (read_access readB)⟩)
    (fun _ _ => rfl) (fun _ _ _ _ _ => trivial) (fun _ => rfl)
    (fun _ _ _ _ ⟨empty, _⟩ value member => by
      dsimp only [addInternal] at empty member
      subst empty; cases member)
    (fun _ _ _ _ ⟨formed, readA, readB⟩ below _ _ writable => ⟨
      (below.read _ (formed.access_bound (read_access readA)) 8 1).trans readA,
      (below.read _ (formed.access_bound (read_access readB)) 8 1).trans readB, writable⟩)
    (fun _ _ _ _ fresh _ member => Or.inl (List.mem_singleton.mp member ▸ fresh))
    (fun _ _ _ _ _ _ _ ⟨formed, readA, _⟩ _ _ _ _ confined ⟨empty, _⟩ =>
      ⟨empty, confined.read_apart formed readA nofun⟩)

#print axioms discard_forwards

/-- `IsZero(v)` returns `v == 0` as a narrowed boolean. -/
def isZeroContract : MethodContract CIL.W64 Bool where
  args v := [.scalar (.i64 v)]
  results zero := [.scalar (.i32 (if zero then 1 else 0))]
  pre _ _ := True
  footprint _ := []
  post v _ _ zero := zero = decide (v = 0)

theorem is_zero_holds : isZeroContract.Holds Extracted.program isZero := by
  intro v m _
  refine ⟨6, m, isZeroContract.results (decide (v = 0)), ?_, Confined.refl _ m,
    decide (v = 0), rfl, rfl⟩
  simp only [isZeroContract, decide_eq_true_eq]
  cil_checked_steps [NarrowKind.extend_ite_ofNat_one_zero]

#print axioms is_zero_holds

/-- `IsZeroForward` re-narrows `IsZero`'s boolean through its own `ret`, which is the
    identity on 0 and 1, so it inherits the contract. -/
theorem is_zero_forwards :
    (isZeroContract.forward isZeroContract.args).Holds Extracted.program isZeroForward :=
  is_zero_holds.forward (indices := [0]) (narrow := some .unsigned8) isZeroForward.found
    isZero.found ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ => rfl) (fun _ _ member => member)
    (fun _ _ _ => rfl) (fun _ _ _ zero _ => ⟨_, rfl, by cases zero <;> decide⟩)

#print axioms is_zero_forwards

/-- A narrowed return of a value outside the narrow range would change it, so such a callee
    result is not accepted as unchanged. -/
theorem wide_result_changes : ¬ ReturnsUnchanged (some .unsigned8) [.scalar (.i32 256)] := by
  rintro ⟨bits, same, extended⟩
  simp only [List.cons.injEq, Value.scalar.injEq, CIL.Value.i32.injEq, and_true] at same
  subst same
  exact absurd extended (by decide)

#print axioms wide_result_changes

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
