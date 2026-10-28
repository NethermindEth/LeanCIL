import CIL.Semantics

/-!
# Instruction equations, fuel and determinism of the reference interpreter

`run` takes fuel, so a proof picks some amount. These lemmas show the choice does not
matter: more fuel never changes a successful result, and any two successful runs agree.
Exact feature and return equations avoid expanding the complete instruction dispatcher.
-/

namespace CIL

/-- A feature test pushes the profile's answer as `1` or `0`. -/
theorem step_feature (id : Feature) (returns : Bool) (pc : Nat) (args : List Value)
    (frame : Nat) (stack : List Value) (memory : Memory) (profile : FeatureProfile) :
    step (.feature id) returns pc args frame stack memory profile =
      some (.next (pc + 1) (.i32 (if profile.evaluate id then 1 else 0) :: stack) memory) :=
  rfl
#print axioms step_feature

/-- A return instruction checks the result without inspecting other instruction families. -/
theorem step_return (narrow : Option NarrowKind) (returns : Bool) (pc : Nat)
    (args : List Value) (frame : Nat) (stack : List Value) (memory : Memory)
    (profile : FeatureProfile) :
    step (.ret narrow) returns pc args frame stack memory profile =
      returnFromStack narrow returns stack memory := rfl
#print axioms step_return

/-- What `run` does with the action a step at `pc` returned: continue, enter a callee and
    resume after it, or return. -/
def runAction (program : Program) (fuel method pc : Nat) (args : List Value) (frame : Nat) :
    Action → Option (Memory × List Value)
  | .next target stack' memory' => run program fuel method target args frame stack' memory'
  | .call callee args' rest memory' => do
    let child ← program[callee]?
    let (final, result) ← run program fuel callee 0 args' (frame + 1) []
      (initFrame memory' (frame + 1) child args')
    run program fuel method (pc + 1) args frame (result ++ rest) final
  | .construct callee args' rest memory' => do
    let child ← program[callee]?
    let (final, result) ← run program fuel callee 0 args' (frame + 1) []
      (initFrame memory' (frame + 1) child args')
    if !result.isEmpty then none else
      run program fuel method (pc + 1) args frame
        ((← readVectorHome final frame 2 pc) :: rest) final
  | .returned result final => some (final, result)

/-- One unit of fuel runs a step and then its action. -/
theorem run_succ (program : Program) (fuel method pc : Nat) (args : List Value) (frame : Nat)
    (stack : List Value) (memory : Memory) :
    run program (fuel + 1) method pc args frame stack memory =
      (program[method]?).bind fun body => (body.code[pc]?).bind fun op =>
        (step op body.returnsValue pc args frame stack memory body.profile).bind
          (runAction program fuel method pc args frame) := by
  simp only [run, Option.bind_eq_bind]
  rfl

/-- A successful action carries over to another program and fuel whose runs keep every
    success and whose callees set up the same frames. -/
theorem runAction_transfer {source target : Program} {sourceFuel targetFuel : Nat}
    (callees : ∀ (callee : Nat) (child : Method), source[callee]? = some child →
      ∃ child', target[callee]? = some child' ∧
        ∀ memory frame args, initFrame memory frame child args = initFrame memory frame child' args)
    (runs : ∀ method pc args frame stack memory result,
      run source sourceFuel method pc args frame stack memory = some result →
      run target targetFuel method pc args frame stack memory = some result)
    (method pc : Nat) (args : List Value) (frame : Nat) (action : Action)
    (result : Memory × List Value)
    (h : runAction source sourceFuel method pc args frame action = some result) :
    runAction target targetFuel method pc args frame action = some result := by
  cases action with
  | next target' stack memory => exact runs _ _ _ _ _ _ _ h
  | returned values final => exact h
  | call callee args' rest memory =>
    simp only [runAction, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨child, found, ⟨final, values⟩, child_run, resumed⟩ := h
    obtain ⟨child', found', frames⟩ := callees callee child found
    exact ⟨child', found', (final, values), by rw [← frames]; exact runs _ _ _ _ _ _ _ child_run,
      runs _ _ _ _ _ _ _ resumed⟩
  | construct callee args' rest memory =>
    simp only [runAction, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨child, found, ⟨final, values⟩, child_run, resumed⟩ := h
    obtain ⟨child', found', frames⟩ := callees callee child found
    refine ⟨child', found', (final, values), by rw [← frames]; exact runs _ _ _ _ _ _ _ child_run,
      ?_⟩
    revert resumed
    split
    · exact id
    · simp only [Option.bind_eq_some_iff]
      exact fun ⟨value, read, resumed⟩ => ⟨value, read, runs _ _ _ _ _ _ _ resumed⟩

#print axioms run_succ
#print axioms runAction_transfer

/-- Increasing fuel preserves every successful execution, including nested calls. -/
theorem run_mono (program : Program) (fuel extra method pc : Nat)
    (args : List Value) (frame : Nat) (stack : List Value) (memory : Memory)
    (result : Memory × List Value)
    (h : run program fuel method pc args frame stack memory = some result) :
    run program (fuel + extra) method pc args frame stack memory = some result := by
  induction fuel generalizing method pc args frame stack memory result with
  | zero => simp [run] at h
  | succ fuel ih =>
    rw [Nat.succ_add, run_succ]
    rw [run_succ] at h
    simp only [Option.bind_eq_some_iff] at h ⊢
    obtain ⟨body, found, op, fetched, action, stepped, continued⟩ := h
    exact ⟨body, found, op, fetched, action, stepped,
      runAction_transfer (fun _ child found => ⟨child, found, fun _ _ _ => rfl⟩)
        (fun _ _ _ _ _ _ _ => ih _ _ _ _ _ _ _) _ _ _ _ _ _ continued⟩

theorem run_of_le (program : Program) (fuel larger method pc : Nat)
    (args : List Value) (frame : Nat) (stack : List Value) (memory : Memory)
    (result : Memory × List Value) (hf : fuel ≤ larger)
    (h : run program fuel method pc args frame stack memory = some result) :
    run program larger method pc args frame stack memory = some result := by
  have he : fuel + (larger - fuel) = larger := by omega
  simpa only [he] using
    run_mono program fuel (larger - fuel) method pc args frame stack memory result h

/-- Any two successful finite executions have the same observable result. -/
theorem run_result_unique (program : Program) (first second method pc : Nat)
    (args : List Value) (frame : Nat) (stack : List Value) (memory : Memory)
    (a b : Memory × List Value)
    (ha : run program first method pc args frame stack memory = some a)
    (hb : run program second method pc args frame stack memory = some b) : a = b := by
  have hmaxa := run_of_le program first (max first second) method pc args frame stack memory a
    (Nat.le_max_left _ _) ha
  have hmaxb := run_of_le program second (max first second) method pc args frame stack memory b
    (Nat.le_max_right _ _) hb
  exact Option.some.inj (hmaxa.symm.trans hmaxb)

theorem invoke_result_unique (program : Program) (first second method : Nat)
    (args : List Value) (memory : Memory) (a b : Memory × List Value)
    (ha : invoke program first method args memory = some a)
    (hb : invoke program second method args memory = some b) : a = b := by
  cases hbody : program[method]? with
  | none => simp [invoke, hbody] at ha
  | some body =>
    simp only [invoke, hbody] at ha hb
    exact run_result_unique _ _ _ _ _ _ _ _ _ _ _ ha hb

/-- One mapped witness fixes the observation of every successful fuel. -/
theorem invoke_observation_unique {α : Type} (p : Program)
    (fuel witnessFuel entry : Nat) (args : List Value) (memory : Memory)
    (observe : Memory × List Value → α) (outcome : Memory × List Value) (observed : α)
    (witness : (invoke p witnessFuel entry args memory).map observe = some observed)
    (normal : invoke p fuel entry args memory = some outcome) :
    observe outcome = observed := by
  cases execution : invoke p witnessFuel entry args memory with
  | none => simp [execution] at witness
  | some actual =>
    have unique := invoke_result_unique p fuel witnessFuel entry args memory
      outcome actual normal execution
    rw [unique]
    exact Option.some.inj (by simpa only [execution, Option.map_some] using witness)

end CIL
