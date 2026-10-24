import CIL.Embedding.Tactic
import CIL.Safety.Embedding.Outcomes
import CIL.Safety.SymbolicExecution

/-! Outcome contracts proved over literal bodies transfer to an extraction that inserts an
    excluded dead block in the throwing helper and renumbers its throw. -/
namespace Tests.OutcomeEmbedding

open CIL CIL.Safety

def outOfRange : String := "System.ArgumentOutOfRangeException"

/-- `Outer(v) => Check(v)`: any exception comes from the helper. -/
@[cil_code] def outer : Method := { returnsValue := true, locals := [], code := [.arg 0, .call 1 1, .ret] }

/-- `Check(v) => v > 100 ? throw new ArgumentOutOfRangeException() : v`, as the proof states it. -/
@[cil_code] def check : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .const32 100, .convI8, .bgtu 6, .arg 0, .ret, .throw outOfRange] }

/-- `check` as the profile-specific extraction emits it: a dead block moves the throw to pc 7. -/
@[cil_code] def extractedCheck : Method := { returnsValue := true, locals := [], code :=
  [.arg 0, .const32 100, .convI8, .bgtu 7, .arg 0, .ret, .unsupported "Unreachable under selected profile",
    .throw outOfRange] }

@[cil_code] def literal : Program := [outer, check]
@[cil_code] def extracted : Program := [outer, extractedCheck]

theorem literal_set : literal = extracted.set 1 check := rfl

theorem check_embeds : MethodEmbeds extracted 1 check := by cil_embed

def raisesAbove (v : W64) : Option String := if v ≤ 100 then none else some outOfRange

def checkContract : OutcomeContract W64 W64 where
  args v := [.scalar (.i64 v)]
  results out := [.scalar (.i64 out)]
  pre _ _ := True
  footprint _ := []
  post v _ _ out := out = v
  raises v _ := raisesAbove v

def outerContract : OutcomeContract W64 W64 := checkContract

theorem check_holds : checkContract.Holds literal 1 := by
  rintro v m -
  by_cases within : v ≤ 100
  · have bound : ¬ 100#64 < v := by simpa using within
    simp only [checkContract, raisesAbove, within, ite_true]
    refine ⟨10, m, _, ?_, Confined.refl _ m, _, rfl, rfl⟩
    cil_checked_steps [bound]
  · have bound : 100#64 < v := by simpa using within
    simp only [checkContract, raisesAbove, within, ite_false]
    cil_raise_steps [bound]

/-- The in-range half of `Check` as a plain method contract: no throw is named, so `pre` excludes it. -/
def checkInRange : MethodContract W64 W64 where
  args v := [.scalar (.i64 v)]
  results out := [.scalar (.i64 out)]
  pre v _ := v ≤ 100
  footprint _ := []
  post v _ _ out := out = v

theorem check_in_range : checkInRange.Holds literal 1 := by
  rintro v m (within : v ≤ 100)
  have bound : ¬ 100#64 < v := by simpa using within
  dsimp only [checkInRange]
  refine ⟨10, m, _, ?_, Confined.refl _ m, _, rfl, rfl⟩
  cil_checked_steps [bound]

-- The method contract transfers to the extraction without reading `extractedCheck`.
theorem extracted_in_range : checkInRange.Holds extracted 1 := check_embeds.method_holds (literal_set ▸ check_in_range)

theorem outer_call : outer.code[1]? = some (.call 1 1) := rfl

/-- `Outer` propagates the helper's exception and returns its result, read off the helper's contract. -/
theorem outer_holds (checkHolds : checkContract.Holds literal 1) : outerContract.Holds literal 0 := by
  rintro v m -
  dsimp only [outerContract, checkContract]
  cases raised : raisesAbove v with
  | some exception =>
    cil_raise_steps []
    exact run_call_raises_of_contract checkHolds v rfl outer_call (by cil_checked_step []) rfl
      rfl trivial raised
  | none =>
    cil_contract_steps []
    refine run_call_of_outcome checkHolds v rfl outer_call (by cil_checked_step []) rfl trivial raised ?_
    rintro m1 _ - confined ⟨out, rfl, same⟩
    subst out
    dsimp only [checkContract]
    cil_contract_steps []
    exact ⟨confined, _, rfl, rfl⟩

-- Both contracts transfer to the extraction; neither proof reads `extractedCheck`.
theorem extracted_check : checkContract.Holds extracted 1 := check_embeds.holds (literal_set ▸ check_holds)

theorem extracted_outer : outerContract.Holds extracted 0 :=
  check_embeds.holds (literal_set ▸ outer_holds check_holds)

-- Each branch of the transferred contract is available on the extraction.
example (m : Safety.Memory) : Raises extracted 1 [.scalar (.i64 101)] m outOfRange :=
  extracted_check.raising (input := 101) trivial (by show raisesAbove 101 = _; decide)

example (m : Safety.Memory) : Raises extracted 0 [.scalar (.i64 101)] m outOfRange :=
  extracted_outer.raising (input := 101) trivial (by show raisesAbove 101 = _; decide)

example (m : Safety.Memory) : ∃ fuel final, Safety.invoke extracted fuel 0 [.scalar (.i64 100)] m = .ok (final, [.scalar (.i64 100)]) := by
  obtain ⟨fuel, final, _, invoked, -, out, rfl, rfl⟩ :=
    extracted_outer.returning (input := 100) (initial := m) trivial (by show raisesAbove 100 = _; decide)
  exact ⟨fuel, final, invoked⟩

/-! The relocated fault location: the literal body throws at pc 6 of method 1, the extraction at pc 7. -/

def empty : Safety.Memory := { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }

/-- The pc map `cil_embed` finds, stated so the relocation can be computed. -/
theorem check_embeds_at : Embeds check extractedCheck [0, 1, 2, 3, 4, 5, 7] := by
  constructor <;> rfl

theorem literal_direct : Safety.invoke literal 10 1 [.scalar (.i64 101)] empty = .error ⟨1, 6, .thrown outOfRange⟩ := rfl

theorem literal_propagated : Safety.invoke literal 10 0 [.scalar (.i64 101)] empty = .error ⟨1, 6, .thrown outOfRange⟩ := rfl

theorem extracted_direct : Safety.invoke extracted 10 1 [.scalar (.i64 101)] empty = .error ⟨1, 7, .thrown outOfRange⟩ :=
  Embeds.invoke_raise (program := extracted) (index := 1) rfl check_embeds_at literal_direct rfl

-- The helper's location is relocated by the helper's map; the caller's method is never blamed.
theorem extracted_propagated : Safety.invoke extracted 10 0 [.scalar (.i64 101)] empty = .error ⟨1, 7, .thrown outOfRange⟩ :=
  Embeds.invoke_raise (program := extracted) (index := 1) rfl check_embeds_at literal_propagated rfl

-- The relocation is the embedding's map, not the identity.
example : (⟨1, 6, .thrown outOfRange⟩ : LocatedFault).relocate
    (fun j => if j = 1 then Embedding.rename [0, 1, 2, 3, 4, 5, 7] extractedCheck.code.length else id) =
    ⟨1, 7, .thrown outOfRange⟩ := rfl

/-! A changed reachable throw condition or exception type neither embeds nor satisfies the contract. -/

def renamedException : Method := { extractedCheck with code := extractedCheck.code.set 7 (.throw "System.ArgumentException") }
def lowerBound : Method := { extractedCheck with code := extractedCheck.code.set 1 (.const32 50) }

/--
error: cil_embed: the expected body does not embed into the extracted method
method index 1
expected pc 6 maps to actual pc 7
  expected: CIL.Op.throw "System.ArgumentOutOfRangeException"
  actual:   CIL.Op.throw "System.ArgumentException"
  the instructions differ
-/
#guard_msgs (substring := true) in
example : MethodEmbeds [outer, renamedException] 1 check := by cil_embed

/--
error: cil_embed: the expected body does not embed into the extracted method
method index 1
expected pc 1 maps to actual pc 1
  expected: CIL.Op.const32 0x00000064#32
  actual:   CIL.Op.const32 0x00000032#32
  the instructions differ
-/
#guard_msgs (substring := true) in
example : MethodEmbeds [outer, lowerBound] 1 check := by cil_embed

/-- The renamed build throws `ArgumentException` for 101, so the transferred contract cannot hold for it. -/
example : ¬ checkContract.Holds [outer, renamedException] 1 := by
  intro holds
  obtain ⟨_, fault, ran, named⟩ := holds.raising (input := 101) (initial := empty) (exception := outOfRange) trivial
    (by decide)
  have thrown : Safety.invoke [outer, renamedException] 10 1 (checkContract.args 101) empty =
      .error ⟨1, 7, .thrown "System.ArgumentException"⟩ := rfl
  cases invoke_unique (by simp [Settled, named]) (by simp [Settled]) ran thrown
  simp [outOfRange] at named

/-- The lowered bound throws for 60, which the contract says returns. -/
example : ¬ checkContract.Holds [outer, lowerBound] 1 := by
  intro holds
  obtain ⟨_, _, _, ran, -⟩ := holds.returning (input := 60) (initial := empty) trivial (by decide)
  have thrown : Safety.invoke [outer, lowerBound] 10 1 (checkContract.args 60) empty =
      .error ⟨1, 7, .thrown outOfRange⟩ := rfl
  cases invoke_unique (by trivial) (by simp [Settled]) ran thrown

/-! Only named throws are transported: fuel exhaustion and unsupported execution are not exceptions. -/

/-- A literal body that leaves the throw unsupported still embeds: dead code constrains nothing. -/
def unsupportedThrow : Method := { check with code := check.code.set 6 (.unsupported "fixture") }

theorem unsupported_embeds : MethodEmbeds extracted 1 unsupportedThrow := by cil_embed

theorem unsupported_faults :
    Safety.invoke (extracted.set 1 unsupportedThrow) 10 1 [.scalar (.i64 101)] empty =
      .error ⟨1, 6, .unsupported "Non-memory instruction requires execution adapter"⟩ := rfl

example : ¬ Transported (.error ⟨1, 6, .unsupported "Non-memory instruction requires execution adapter"⟩ :
    Except LocatedFault (Safety.Memory × List Safety.Value)) := by
  rintro ⟨_, thrown⟩
  cases thrown

/-- The extraction raises, but the literal body proves nothing about it: it never raises. -/
example : ¬ Raises (extracted.set 1 unsupportedThrow) 1 [.scalar (.i64 101)] empty outOfRange := by
  rintro ⟨_, fault, ran, thrown⟩
  cases invoke_unique (by simp [Settled, thrown]) (by simp [Settled]) ran unsupported_faults
  simp at thrown

theorem literal_exhausted : Safety.invoke literal 0 1 [.scalar (.i64 101)] empty = .error ⟨1, 0, .fuelExhausted⟩ := rfl

example : ¬ Transported (.error ⟨1, 0, .fuelExhausted⟩ : Except LocatedFault (Safety.Memory × List Safety.Value)) := by
  rintro ⟨_, thrown⟩
  cases thrown

-- An exhausted run is not a throw, so it cannot be passed to the transport.
/--
but is expected to have type
  { method := 1, instruction := 0, fault := ExecutionFault.fuelExhausted }.fault = ExecutionFault.thrown outOfRange
-/
#guard_msgs (substring := true) in
example : Safety.invoke extracted 0 1 [.scalar (.i64 101)] empty = .error ⟨1, 0, .fuelExhausted⟩ :=
  Embeds.invoke_raise (program := extracted) (index := 1) (exception := outOfRange) rfl check_embeds_at literal_exhausted rfl

/-- info: 'Tests.OutcomeEmbedding.extracted_outer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms extracted_outer

/-- info: 'CIL.Safety.run_outcome_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run_outcome_refines

/-- info: 'CIL.Safety.step_raise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_raise

/-- info: 'CIL.MethodEmbeds.holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MethodEmbeds.holds

#print axioms check_in_range

/-- info: 'CIL.MethodEmbeds.method_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MethodEmbeds.method_holds

/-- info: 'Tests.OutcomeEmbedding.extracted_in_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms extracted_in_range

/-- info: 'CIL.MethodEmbeds.raises' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MethodEmbeds.raises

end Tests.OutcomeEmbedding
