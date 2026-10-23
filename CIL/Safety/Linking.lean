import CIL.Safety.Imports
import CIL.Safety.StepFlow

/-! A closed library relocated into a linked program runs exactly as alone; static identities are not renamed. -/

namespace CIL

/-- Renames the methods an instruction calls or constructs with; `.nativeBinary` never dispatches its operand. -/
def Op.relocate (f : Nat → Nat) : Op → Op
  | .call method argc => .call (f method) argc
  | .newVector256 method argc => .newVector256 (f method) argc
  | .newAggregate method argc size => .newAggregate (f method) argc size
  | op => op

-- Together these fail if a method-index constructor is added to one of `relocate` and `callees` only.
theorem Op.callees_relocate (f : Nat → Nat) (op : Op) : (op.relocate f).callees = op.callees.map f := by
  cases op <;> simp [Op.relocate, Op.callees]

theorem Op.relocate_of_callees_nil (f : Nat → Nat) (op : Op) (none : op.callees = []) : op.relocate f = op := by
  cases op <;> simp_all [Op.relocate, Op.callees]

/-- Renames the method indices in a body; pcs, locals, profile and static sites are unchanged. -/
def Method.relocate (f : Nat → Nat) (body : Method) : Method :=
  { body with code := body.code.map (Op.relocate f) }

end CIL

namespace CIL.Safety

/-- Every method index that `lib`'s code names is one of its own methods. -/
def Closed (lib : CIL.Program) : Prop :=
  ∀ (i : Nat) (body : CIL.Method), lib[i]? = some body → ∀ (pc : Nat) (op : CIL.Op), body.code[pc]? = some op →
    ∀ callee ∈ op.callees, callee < lib.length

/-- Decides `Closed` for a concrete library. -/
def closedCheck (lib : CIL.Program) : Bool :=
  lib.all fun body => body.code.all fun op => op.callees.all (· < lib.length)

theorem Closed.of_check {lib : CIL.Program} (checked : closedCheck lib = true) : Closed lib := by
  intro i body found pc op fetched callee member
  simp only [closedCheck, List.all_eq_true, decide_eq_true_eq] at checked
  exact checked body (List.mem_of_getElem? found) op (List.mem_of_getElem? fetched) callee member

/-- Method `i` of `lib` sits at `f i` in `linked`, relocated by `f`. -/
def RelocatesInto (lib linked : CIL.Program) (f : Nat → Nat) : Prop :=
  ∀ i (bound : i < lib.length), linked[f i]? = some (lib[i].relocate f)

/-- A fault at `method` is reported at `f method`, with the same pc and fault. -/
def LocatedFault.relocateMethod (f : Nat → Nat) (fault : LocatedFault) : LocatedFault :=
  ⟨f fault.method, fault.instruction, fault.fault⟩

/-- Renames the method a call or construction enters. -/
def FrameAction.relocate (f : Nat → Nat) : FrameAction → FrameAction
  | .call callee arguments rest memory => .call (f callee) arguments rest memory
  | .construct callee arguments rest frame temporary kind memory =>
    .construct (f callee) arguments rest frame temporary kind memory
  | action => action

theorem FrameAction.relocate_of_callee_none (f : Nat → Nat) (action : FrameAction) (none : action.callee = .none) :
    action.relocate f = action := by
  cases action <;> simp_all [FrameAction.relocate, FrameAction.callee]

theorem enterFrame_relocate (f : Nat → Nat) (body : CIL.Method) (args : List Value) (m : Memory) :
    enterFrame (body.relocate f) args m = enterFrame body args m := rfl

theorem step_body_relocate (f : Nat → Nat) (body : CIL.Method) (op : CIL.Op) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) :
    step (body.relocate f) op pc args frame stack m = step body op pc args frame stack m := rfl

/-- A relocated instruction steps exactly as the original, entering the renamed method. -/
theorem step_relocate (f : Nat → Nat) (body : CIL.Method) (op : CIL.Op) (pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (m : Memory) :
    step (body.relocate f) (op.relocate f) pc args frame stack m =
      (step body op pc args frame stack m).map (FrameAction.relocate f) := by
  rw [step_body_relocate]
  cases hc : op.callees with
  | nil =>
    rw [CIL.Op.relocate_of_callees_nil f op hc]
    cases hs : step body op pc args frame stack m with
    | error => rfl
    | ok action =>
      have none := step_callee hs
      rw [hc] at none
      simp only [Except.map, FrameAction.relocate_of_callee_none f action none]
  | cons callee rest =>
    cases op <;> simp only [CIL.Op.callees, reduceCtorEq] at hc
    all_goals
      unfold step
      simp only [CIL.Op.relocate, observerCount, Bool.or_false,
        Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map]
      repeat' (split <;> simp_all [FrameAction.relocate])

/-- A method that `step` enters is a callee its instruction names, so it is in a closed library. -/
theorem Closed.callee {lib : CIL.Program} (closed : Closed lib) {method pc : Nat} {body : CIL.Method}
    {op : CIL.Op} {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    {callee : Nat} (found : lib[method]? = some body) (fetched : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack m = .ok action) (enters : action.callee = some callee) :
    callee < lib.length :=
  closed method body found pc op fetched callee (List.mem_of_mem_head? ((step_callee stepped).symm.trans enters))

theorem Method.relocate_code {f : Nat → Nat} {body : CIL.Method} {pc : Nat} :
    (body.relocate f).code[pc]? = (body.code[pc]?).map (CIL.Op.relocate f) := by
  simp [CIL.Method.relocate]

/-- A closed library runs in the linked program exactly as alone; only a fault's method index is renamed. -/
theorem run_relocate {lib linked : CIL.Program} {f : Nat → Nat} (closed : Closed lib)
    (relocates : RelocatesInto lib linked f) (fuel method pc : Nat) (args : List Value) (frame : Frame)
    (stack : List Value) (memory : Memory) (bound : method < lib.length) :
    run linked fuel (f method) pc args frame stack memory =
      (run lib fuel method pc args frame stack memory).mapError (LocatedFault.relocateMethod f) := by
  induction fuel generalizing method pc args frame stack memory with
  | zero => simp only [run, Except.mapError, LocatedFault.relocateMethod]
  | succ fuel ih =>
    have found : lib[method]? = some lib[method] := List.getElem?_eq_getElem bound
    have moved := relocates method bound
    generalize lib[method] = body at found moved
    cases ho : body.code[pc]? with
    | none =>
      have lo : (body.relocate f).code[pc]? = none := by rw [Method.relocate_code, ho]; rfl
      simp only [run, found, moved, ho, lo, Except.mapError, LocatedFault.relocateMethod]
    | some op =>
      have lo : (body.relocate f).code[pc]? = some (op.relocate f) := by rw [Method.relocate_code, ho]; rfl
      have ls := step_relocate f body op pc args frame stack memory
      cases hs : step body op pc args frame stack memory with
      | error fault =>
        simp only [run, found, moved, ho, lo, ls, hs, Except.map, Bind.bind, Except.bind, Except.mapError,
          LocatedFault.relocateMethod]
      | ok action =>
        cases action with
        | next target values nextFrame updated =>
          simp only [run, found, moved, ho, lo, ls, hs, Except.map, FrameAction.relocate, Bind.bind,
            Except.bind, Except.mapError]
          exact ih method target args nextFrame values updated bound
        | returned values updated =>
          simp only [run, found, moved, ho, lo, ls, hs, Except.map, FrameAction.relocate, Bind.bind,
            Except.bind, Except.mapError]
          cases values.mapM (checkedValue (leaveFrame frame updated)) <;> rfl
        | call callee arguments rest updated =>
          have inside := closed.callee found ho hs rfl
          have child : lib[callee]? = some lib[callee] := List.getElem?_eq_getElem inside
          have childMoved := relocates callee inside
          generalize lib[callee] = callBody at child childMoved
          simp only [run, found, moved, ho, lo, ls, hs, child, childMoved, enterFrame_relocate, Except.map,
            FrameAction.relocate, Bind.bind, Except.bind, Except.mapError]
          cases he : enterFrame callBody arguments updated with
          | error fault => rfl
          | ok entered =>
            obtain ⟨childFrame, childMemory⟩ := entered
            simp only
            rw [ih callee 0 arguments childFrame [] childMemory inside]
            cases run lib fuel callee 0 arguments childFrame [] childMemory with
            | error fault => rfl
            | ok result =>
              obtain ⟨final, values⟩ := result
              exact ih method (pc + 1) args frame (values ++ rest) final bound
        | construct callee arguments rest nextFrame temporary kind updated =>
          have inside := closed.callee found ho hs rfl
          have child : lib[callee]? = some lib[callee] := List.getElem?_eq_getElem inside
          have childMoved := relocates callee inside
          generalize lib[callee] = callBody at child childMoved
          simp only [run, found, moved, ho, lo, ls, hs, child, childMoved, enterFrame_relocate, Except.map,
            FrameAction.relocate, Bind.bind, Except.bind, Except.mapError]
          cases he : enterFrame callBody arguments updated with
          | error fault => rfl
          | ok entered =>
            obtain ⟨childFrame, childMemory⟩ := entered
            simp only
            rw [ih callee 0 arguments childFrame [] childMemory inside]
            cases run lib fuel callee 0 arguments childFrame [] childMemory with
            | error fault => rfl
            | ok result =>
              obtain ⟨final, values⟩ := result
              simp only [Except.mapError]
              cases !values.isEmpty with
              | true => simp only [↓reduceIte, LocatedFault.relocateMethod]
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                cases loadLocal final (.bytes kind temporary) with
                | error fault => rfl
                | ok value => exact ih method (pc + 1) args nextFrame (value :: rest) final bound

/-- `run_relocate` from a method entry. -/
theorem invoke_relocate {lib linked : CIL.Program} {f : Nat → Nat} (closed : Closed lib)
    (relocates : RelocatesInto lib linked f) (fuel method : Nat) (args : List Value) (memory : Memory)
    (bound : method < lib.length) :
    invoke linked fuel (f method) args memory =
      (invoke lib fuel method args memory).mapError (LocatedFault.relocateMethod f) := by
  have found : lib[method]? = some lib[method] := List.getElem?_eq_getElem bound
  have moved := relocates method bound
  generalize lib[method] = body at found moved
  simp only [invoke, found, moved, enterFrame_relocate, Bind.bind, Except.bind, Except.mapError]
  cases args.mapM (checkedValue memory) with
  | error fault => rfl
  | ok checked =>
    simp only
    cases enterFrame body checked memory with
    | error fault => rfl
    | ok entered =>
      obtain ⟨frame, entered⟩ := entered
      exact run_relocate closed relocates fuel method 0 checked frame [] entered bound

/-- Only an index the library has can return or raise. -/
theorem invoke_bound {lib : CIL.Program} {fuel method : Nat} {args : List Value} {memory : Memory}
    {outcome : Except LocatedFault (Memory × List Value)} (resolved : NoInvalidState outcome)
    (invoked : invoke lib fuel method args memory = outcome) : method < lib.length := by
  apply Classical.byContradiction
  intro outside
  rw [invoke_unlinked (List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt outside))] at invoked
  exact resolved _ invoked.symm rfl

/-- A raised exception is raised by the relocated method. -/
theorem Raises.relocate {lib linked : CIL.Program} {f : Nat → Nat} {method : Nat} {args : List Value}
    {memory : Memory} {exception : String} (raised : Raises lib method args memory exception)
    (closed : Closed lib) (relocates : RelocatesInto lib linked f) :
    Raises linked (f method) args memory exception := by
  obtain ⟨fuel, fault, invoked, thrown⟩ := raised
  have bound := invoke_bound (fun located same => by cases same; rw [thrown]; exact nofun) invoked
  refine ⟨fuel, fault.relocateMethod f, ?_, thrown⟩
  rw [invoke_relocate closed relocates fuel method args memory bound, invoked]
  rfl

/-- A contract proved on a closed library holds at the relocated index. -/
theorem MethodContract.Holds.relocate {Input Output : Type} {c : MethodContract Input Output}
    {lib linked : CIL.Program} {f : Nat → Nat} {method : Nat} (holds : c.Holds lib method)
    (closed : Closed lib) (relocates : RelocatesInto lib linked f) : c.Holds linked (f method) := by
  intro input initial permitted
  obtain ⟨fuel, final, values, invoked, framed, returns⟩ := holds input initial permitted
  have bound := invoke_bound (outcome := .ok (final, values)) (fun _ h => nomatch h) invoked
  refine ⟨fuel, final, values, ?_, framed, returns⟩
  rw [invoke_relocate closed relocates fuel method _ initial bound, invoked]
  rfl

/-- Both outcomes transfer: a normal return as for `MethodContract`, a raise by `Raises.relocate`. -/
theorem OutcomeContract.Holds.relocate {Input Output : Type} {c : OutcomeContract Input Output}
    {lib linked : CIL.Program} {f : Nat → Nat} {method : Nat} (holds : c.Holds lib method)
    (closed : Closed lib) (relocates : RelocatesInto lib linked f) : c.Holds linked (f method) := by
  intro input initial permitted
  have outcome := holds input initial permitted
  revert outcome
  cases c.raises input initial with
  | some exception => exact fun raised => raised.relocate closed relocates
  | none =>
    intro ⟨fuel, final, values, invoked, framed, returns⟩
    have bound := invoke_bound (outcome := .ok (final, values)) (fun _ h => nomatch h) invoked
    refine ⟨fuel, final, values, ?_, framed, returns⟩
    rw [invoke_relocate closed relocates fuel method _ initial bound, invoked]
    rfl

theorem MethodContract.relocateGiven {Input Output : Type} {c : MethodContract Input Output}
    {base completion target : CIL.Program} {imports : CIL.Program -> Prop} {method : Nat} {f : Nat -> Nat}
    (given : HoldsGiven base imports (fun linked => c.Holds linked method))
    (linkedPrefix : Links base completion) (met : imports completion) (closed : Closed completion)
    (relocates : RelocatesInto completion target f) : c.Holds target (f method) :=
  (given completion linkedPrefix met).relocate closed relocates

theorem OutcomeContract.relocateGiven {Input Output : Type} {c : OutcomeContract Input Output}
    {base completion target : CIL.Program} {imports : CIL.Program -> Prop} {method : Nat} {f : Nat -> Nat}
    (given : HoldsGiven base imports (fun linked => c.Holds linked method))
    (linkedPrefix : Links base completion) (met : imports completion) (closed : Closed completion)
    (relocates : RelocatesInto completion target f) : c.Holds target (f method) :=
  (given completion linkedPrefix met).relocate closed relocates

/-- A separately extracted library: its exported method at index 0, then its private helpers. -/
structure Library where
  entry : CIL.Method
  helpers : CIL.Program := []

def Library.program (lib : Library) : CIL.Program := lib.entry :: lib.helpers

/-- Helpers of the libraries before `j`. -/
def helperOffset (libs : List Library) (j : Nat) : Nat := ((libs.take j).map (·.helpers.length)).sum

/-- Library `j`'s entry fills import slot `j`; its helpers follow every entry, after earlier libraries' helpers. -/
def linkSlot (app : CIL.Program) (libs : List Library) (j : Nat) : Nat → Nat
  | 0 => importIndex app j
  | i + 1 => app.length + libs.length + helperOffset libs j + i

/-- `app`, then every library entry at its import slot, then every library's helpers. -/
def link (app : CIL.Program) (libs : List Library) : CIL.Program :=
  app ++ libs.mapIdx (fun j lib => lib.entry.relocate (linkSlot app libs j)) ++
    (libs.mapIdx fun j lib => lib.helpers.map (CIL.Method.relocate (linkSlot app libs j))).flatten

theorem link_links (app : CIL.Program) (libs : List Library) : Links app (link app libs) :=
  ⟨_, List.append_assoc _ _ _⟩

theorem getElem?_flatten_offset {blocks : List (List α)} {j k : Nat} (hj : j < blocks.length)
    (hk : k < blocks[j].length) : blocks.flatten[((blocks.take j).map List.length).sum + k]? = blocks[j][k]? := by
  induction blocks generalizing j with
  | nil => cases hj
  | cons block rest ih =>
    cases j with
    | zero =>
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons,
        List.getElem_cons_zero] at hk ⊢
      exact List.getElem?_append_left hk
    | succ j =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons,
        List.getElem_cons_succ] at hk ⊢
      rw [List.getElem?_append_right (by omega), show block.length + ((rest.take j).map List.length).sum + k -
        block.length = ((rest.take j).map List.length).sum + k by omega]
      exact ih (Nat.lt_of_succ_lt_succ hj) hk

/-- Every library lands in the linked program relocated by its slot map. -/
theorem link_relocates (app : CIL.Program) (libs : List Library) {j : Nat} (hj : j < libs.length) :
    RelocatesInto libs[j].program (link app libs) (linkSlot app libs j) := by
  intro i bound
  cases i with
  | zero =>
    simp only [link, linkSlot, importIndex, Library.program, List.getElem_cons_zero, List.append_assoc]
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simpa using hj), List.getElem?_mapIdx, List.getElem?_eq_getElem hj]
    rfl
  | succ i =>
    simp only [Library.program, List.length_cons] at bound
    simp only [link, linkSlot, Library.program, List.getElem_cons_succ, List.append_assoc]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by simp; omega)]
    have lengths : (libs.mapIdx fun j lib => lib.helpers.map (CIL.Method.relocate (linkSlot app libs j))).map
        List.length = libs.map (·.helpers.length) :=
      List.ext_getElem (by simp) (by intro n _ _; simp)
    have offset : app.length + libs.length + helperOffset libs j + i - app.length -
        (libs.mapIdx fun j lib => lib.entry.relocate (linkSlot app libs j)).length =
        (((libs.mapIdx fun j lib => lib.helpers.map (CIL.Method.relocate (linkSlot app libs j))).take j).map
          List.length).sum + i := by
      rw [List.map_take, lengths, ← List.map_take]
      simp only [helperOffset, List.length_mapIdx]
      omega
    rw [offset, getElem?_flatten_offset (by simpa using hj) (by simpa using Nat.lt_of_succ_lt_succ bound)]
    simp only [List.getElem_mapIdx, List.getElem?_map, List.getElem?_eq_getElem (Nat.lt_of_succ_lt_succ bound)]
    rfl

/-- A method property that survives relocating its closed library, such as a proved contract. -/
structure Relocatable where
  holds : CIL.Program → Nat → Prop
  relocate : ∀ {lib linked : CIL.Program} {f : Nat → Nat} {method : Nat},
    Closed lib → RelocatesInto lib linked f → holds lib method → holds linked (f method)

def MethodContract.relocatable {Input Output : Type} (c : MethodContract Input Output) : Relocatable :=
  ⟨c.Holds, fun closed relocates holds => holds.relocate closed relocates⟩

def OutcomeContract.relocatable {Input Output : Type} (c : OutcomeContract Input Output) : Relocatable :=
  ⟨c.Holds, fun closed relocates holds => holds.relocate closed relocates⟩

/-- Import slot `j` of `app` meets `specs[j]`. -/
def Imports (app : CIL.Program) (specs : List Relocatable) (linked : CIL.Program) : Prop :=
  ∀ j (bound : j < specs.length), specs[j].holds linked (importIndex app j)

/-- Libraries proved alone meet their import specifications in the linked program. -/
theorem link_imports {app : CIL.Program} {libs : List Library} {specs : List Relocatable}
    (length : libs.length = specs.length) (closed : ∀ j (bound : j < libs.length), Closed libs[j].program)
    (proved : ∀ j (bound : j < libs.length) (spec : j < specs.length), specs[j].holds libs[j].program 0) :
    Imports app specs (link app libs) := fun j spec =>
  have bound : j < libs.length := length ▸ spec
  specs[j].relocate (f := linkSlot app libs j) (method := 0) (closed j bound) (link_relocates app libs bound) (proved j bound spec)

/-- A caller proved given its imports holds for the concrete program linking libraries proved alone. -/
theorem composed {app : CIL.Program} {libs : List Library} {specs : List Relocatable}
    {claim : CIL.Program → Prop} (given : HoldsGiven app (Imports app specs) claim)
    (length : libs.length = specs.length) (closed : ∀ j (bound : j < libs.length), Closed libs[j].program)
    (proved : ∀ j (bound : j < libs.length) (spec : j < specs.length), specs[j].holds libs[j].program 0) :
    claim (link app libs) :=
  given.discharge (link_links app libs) (link_imports length closed proved)

/-- A claim given stronger imports. -/
theorem HoldsGiven.mono {base : CIL.Program} {weak strong claim : CIL.Program → Prop}
    (given : HoldsGiven base weak claim) (implies : ∀ linked, strong linked → weak linked) :
    HoldsGiven base strong claim :=
  fun linked links met => given linked links (implies linked met)

#print axioms step_callee
#print axioms step_relocate
#print axioms run_relocate
#print axioms invoke_relocate
#print axioms Raises.relocate
#print axioms MethodContract.Holds.relocate
#print axioms OutcomeContract.Holds.relocate
#print axioms MethodContract.relocateGiven
#print axioms OutcomeContract.relocateGiven
#print axioms link_relocates
#print axioms composed

end CIL.Safety
