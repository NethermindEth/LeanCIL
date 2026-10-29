import CIL.Safety.Embedding.Step
import CIL.Safety.Certificate

/-!
# Simulation under embedding

A program whose methods embed into the methods of another program simulates it:
every successful checked run, invocation or invocation certificate of the
expected program is one of the actual program, with each pc renamed by its
method's map. A thrown exception transfers with the same name, and its fault
location moves to the pc its method's map assigns. Other faults do not transfer:
the actual program may run code where the expected one has none.

Each step is matched by `step_relabel` and `step_raise` from `Embedding.Step`; this file
lifts them through `run`, `invoke` and `InvocationCertificate` by induction on fuel.
-/

namespace CIL.Embedding

open CIL

theorem Op.relabel_id (op : Op) : op.relabel id = op := by
  induction op <;> simp only [Op.relabel, id] <;> simp_all

/-- The facts about one method that the simulation consumes. -/
structure BodyRefines (expected actual : Method) (r : Nat → Nat) : Prop where
  profile : actual.profile = expected.profile
  returnsValue : actual.returnsValue = expected.returnsValue
  locals : actual.locals = expected.locals
  localKinds : actual.localKinds = expected.localKinds
  opaqueVectorLocals : actual.opaqueVectorLocals = expected.opaqueVectorLocals
  vectorArgs : actual.vectorArgs = expected.vectorArgs
  parameterHomes : actual.parameterHomes = expected.parameterHomes
  descriptors : actual.staticSites.map Prod.snd = expected.staticSites.map Prod.snd
  entry : r 0 = 0
  /-- Each live expected instruction sits relabeled at its renamed pc with the same static
      descriptor, and an instruction that falls through keeps its successor adjacent. -/
  code : ∀ p op, expected.code[p]? = some op → op.live = true →
    actual.code[r p]? = some (op.relabel r) ∧ staticAt actual (r p) = staticAt expected p ∧
    (op.continues = true → r (p + 1) = r p + 1)

/-- Every body refines itself under the identity renaming. -/
theorem BodyRefines.refl (body : Method) : BodyRefines body body id :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ op found _ => ⟨by simp [found, Op.relabel_id], rfl, fun _ => rfl⟩⟩

/-- A live instruction at `p` appears in `sites` with its mapped pc and mapped successor. -/
theorem mem_sites {limit : Nat} {code : List Op} {map : List Nat} {start p : Nat} {op : Op}
    (found : code[p]? = some op) (live : op.live = true) :
    (⟨start + p, map.getD p limit, map.getD (p + 1) limit, op⟩ : Site) ∈
      sites limit start code map := by
  induction code generalizing map start p with
  | nil => cases found
  | cons head tail ih =>
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      cases map with
      | nil => simp [sites, live, List.headD]
      | cons first rest => cases rest <;> simp [sites, live, List.headD]
    | succ p =>
      simp only [List.getElem?_cons_succ] at found
      have member := ih (map := map.tail) (start := start + 1) found
      have shifted : ∀ n, map.tail.getD n limit = map.getD (n + 1) limit := by
        intro n; cases map <;> simp
      rw [shifted, shifted, show start + 1 + p = start + (p + 1) by omega] at member
      unfold sites
      split
      · exact List.mem_cons_of_mem _ member
      · exact member

/-- `pick` agrees with pointwise lookup whenever its cursor is `code.drop start`. -/
theorem pick_eq (code : List Op) (qs : List Nat) (start : Nat) :
    pick code (code.drop start) start qs = qs.map (fun q => code[q]?) := by
  induction qs generalizing start with
  | nil => rfl
  | cons q qs ih =>
    unfold pick
    split
    · rename_i ordered
      have dropped : (code.drop start).drop (q - start) = code.drop q := by
        rw [List.drop_drop]; congr 1; omega
      simp only [dropped, List.head?_drop, ih, List.map_cons]
    · simp only [ih, List.map_cons]

/-- The decidable `Embeds` check yields the per-method facts the simulation consumes. -/
theorem _root_.CIL.Embeds.refines {expected actual : Method} {map : List Nat}
    (embeds : Embeds expected actual map) :
    BodyRefines expected actual (rename map actual.code.length) := by
  refine ⟨embeds.profile, embeds.returnsValue, embeds.locals, embeds.localKinds,
    embeds.opaqueVectorLocals, embeds.vectorArgs, embeds.parameterHomes, embeds.descriptors,
    embeds.entry, ?_⟩
  intro p op found live
  have member := mem_sites (limit := actual.code.length) (map := map) (start := 0) found live
  rw [Nat.zero_add] at member
  have picked := embeds.code
  have dropped :=
    pick_eq actual.code ((sites actual.code.length 0 expected.code map).map Site.image) 0
  rw [List.drop_zero] at dropped
  rw [dropped, List.map_map] at picked
  have code := List.map_inj_left.mp picked _ member
  have statics := List.map_inj_left.mp embeds.statics _ member
  have flow := List.all_eq_true.mp embeds.flow _ member
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at flow
  refine ⟨code, statics, fun continues => ?_⟩
  rcases flow with stops | next
  · rw [continues] at stops; cases stops
  · exact next

end CIL.Embedding

namespace CIL.Safety

open CIL.Embedding

/-- Refining bodies set up identical frames. -/
theorem enterFrame_congr {expected actual : CIL.Method} {r : Nat → Nat}
    (refines : BodyRefines expected actual r) (args : List Value) (m : Memory) :
    enterFrame actual args m = enterFrame expected args m := by
  simp only [enterFrame, refines.locals, refines.localKinds, refines.opaqueVectorLocals,
    refines.vectorArgs, refines.parameterHomes]

/-- `.unsupported` never steps successfully. -/
theorem step_unsupported {body : CIL.Method} {description : String} {pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body (.unsupported description) pc args frame stack m = .ok action) : False := by
  change Except.error
    (ExecutionFault.unsupported "Not a memory instruction") =
      .ok action at h
  cases h

/-- `.throw` never steps successfully. -/
theorem step_throw {body : CIL.Method} {exception : String} {pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body (.throw exception) pc args frame stack m = .ok action) : False := by
  cases h

/-- A successful `.ret` step always returns. -/
theorem step_ret_returns {body : CIL.Method} {narrow : Option NarrowKind} {pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body (.ret narrow) pc args frame stack m = .ok action) :
    ∃ values m', action = .returned values m' := by
  cases narrow
  · have known : unspecifiedOperands 1 stack = false := by
      cases observed : unspecifiedOperands 1 stack with
      | false => rfl
      | true => simp [step, observerCount, observed] at h
    simp only [step, observerCount, known, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at h
    change (if stack.length = (if body.returnsValue then 1 else 0) then
        (do return FrameAction.returned (← stack.mapM (checkedValue m)) m)
      else .error .invalidState) = .ok action at h
    by_cases sized : stack.length = (if body.returnsValue then 1 else 0)
    · rw [ite_eq_left sized] at h
      obtain ⟨_, _, h⟩ := except_bind_ok h
      cases h
      exact ⟨_, _, rfl⟩
    · rw [ite_eq_right sized] at h
      cases h
  · rename_i kind
    cases stack with
    | nil => cases h
    | cons value rest =>
      cases value <;> try (solve | cases rest <;> cases h)
      rename_i value
      cases value <;> cases rest <;> try (solve | cases h)
      rename_i bits
      change (if body.returnsValue then
        (do return FrameAction.returned
              (← [Value.scalar (.i32 (kind.extend bits))].mapM (checkedValue m)) m)
        else .error .invalidState) = .ok action at h
      split at h
      · obtain ⟨_, _, h⟩ := except_bind_ok h
        cases h
        exact ⟨_, _, rfl⟩
      · cases h

/-- Calls and constructions come only from instructions that resume at the next pc. -/
theorem continues_of_invocation {body : CIL.Method} {op : CIL.Op} {pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body op pc args frame stack m = .ok action)
    (resumes : match action with | .call .. | .construct .. => True | _ => False) :
    op.continues = true := by
  cases op
  case throw => exact (step_throw h).elim
  case unsupported => exact (step_unsupported h).elim
  case branch target =>
    change Except.ok (.next target stack frame m) = .ok action at h
    cases h
    exact resumes.elim
  case ret narrow =>
    obtain ⟨_, _, rfl⟩ := step_ret_returns h
    exact resumes.elim
  case tailCall callee argc =>
    simp only [step] at h
    repeat' first
      | contradiction
      | exact resumes.elim
      | cases h
      | split at h
      | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals rfl

/-- Each method of `expected` embeds into the same method of `actual` under `maps`. -/
structure ProgramRefines (expected actual : CIL.Program) (maps : Nat → Nat → Nat) : Prop where
  method : ∀ index body, expected[index]? = some body →
    ∃ target, actual[index]? = some target ∧ BodyRefines body target (maps index)
  descriptors : programStaticDescriptors expected = programStaticDescriptors actual

/-- Every program refines itself with every method renamed by the identity. -/
theorem ProgramRefines.refl (program : CIL.Program) :
    ProgramRefines program program (fun _ => id) :=
  ⟨fun _ body found => ⟨body, found, BodyRefines.refl body⟩, rfl⟩

/-- Replacing a method by one with the same descriptor list keeps the program-wide list. -/
theorem programStaticDescriptors_set (program : CIL.Program) (index : Nat) (body : CIL.Method)
    (same : ∀ old, program[index]? = some old →
      old.staticSites.map Prod.snd = body.staticSites.map Prod.snd) :
    programStaticDescriptors (program.set index body) = programStaticDescriptors program := by
  induction program generalizing index with
  | nil => rfl
  | cons head tail ih =>
    cases index with
    | zero =>
      have := same head rfl
      simp only [List.set_cons_zero, programStaticDescriptors, List.flatMap_cons] at this ⊢
      rw [this]
    | succ index =>
      have := ih index (fun old found => same old (by simpa using found))
      simp only [List.set_cons_succ, programStaticDescriptors, List.flatMap_cons] at this ⊢
      rw [this]

/-- Substituting an expected method that refines the actual method `index` keeps the
    refinement, renaming that method's pcs by `r`. -/
theorem ProgramRefines.set_body {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) {index : Nat} {body target : CIL.Method}
    {r : Nat → Nat} (found : actual[index]? = some target) (refined : BodyRefines body target r) :
    ProgramRefines (expected.set index body) actual
      (fun j => if j = index then r else maps j) := by
  constructor
  · intro j candidate fetched
    by_cases same : j = index
    · subst same
      simp only [List.getElem?_set_self'] at fetched
      cases present : expected[j]? <;> simp [present] at fetched
      subst fetched
      exact ⟨target, found, by simpa using refined⟩
    · rw [List.getElem?_set_ne (Ne.symm same)] at fetched
      simpa [same] using refines.method j candidate fetched
  · rw [programStaticDescriptors_set _ _ _ ?_]
    · exact refines.descriptors
    · intro old present
      obtain ⟨actualOld, fetched, oldRefines⟩ := refines.method index old present
      rw [found] at fetched
      cases fetched
      exact oldRefines.descriptors.symm.trans refined.descriptors

/-- `ProgramRefines.set_body` for a method checked by `Embeds`. -/
theorem ProgramRefines.set {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) {index : Nat} {body target : CIL.Method}
    {map : List Nat} (found : actual[index]? = some target) (embeds : Embeds body target map) :
    ProgramRefines (expected.set index body) actual
      (fun j => if j = index then rename map target.code.length else maps j) :=
  refines.set_body found embeds.refines

/-- `fault` at the pc that `maps` assigns its instruction in its own method. -/
def LocatedFault.relocate (maps : Nat → Nat → Nat) (fault : LocatedFault) : LocatedFault :=
  { fault with instruction := maps fault.method fault.instruction }

/-- What the simulation carries: every result and every thrown exception, never another
    fault. -/
def Transported : Except LocatedFault α → Prop
  | .ok _ => True
  | .error fault => ∃ exception, fault.fault = .thrown exception

/-- An expected result or throw is the actual run's from the renamed pc, with the fault
    relocated. -/
theorem run_outcome_refines {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) :
    ∀ fuel method pc args frame stack (m : Memory) outcome,
      run expected fuel method pc args frame stack m = outcome → Transported outcome →
      run actual fuel method (maps method pc) args frame stack m =
        outcome.mapError (·.relocate maps) := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ _ _ _ h transported
    subst h
    obtain ⟨_, thrown⟩ := transported
    cases thrown
  | succ fuel ih =>
    intro method pc args frame stack m outcome h transported
    rw [run] at h ⊢
    cases fetched : expected[method]? with
    | none =>
      simp only [fetched] at h
      subst h
      obtain ⟨_, thrown⟩ := transported
      cases thrown
    | some body =>
      simp only [fetched] at h
      obtain ⟨target, found, refined⟩ := refines.method method body fetched
      cases decoded : body.code[pc]? with
      | none =>
        simp only [decoded] at h
        subst h
        obtain ⟨_, thrown⟩ := transported
        cases thrown
      | some op =>
        simp only [decoded, bind, Except.bind] at h
        cases stepped : step body op pc args frame stack m with
        | error fault =>
          simp only [stepped, Except.mapError] at h
          subst h
          obtain ⟨exception, thrown⟩ := transported
          dsimp only at thrown
          subst thrown
          have live : op.live = true := by
            cases op <;> first
              | rfl
              | (change Except.error (ExecutionFault.unsupported _) = _ at stepped; cases stepped)
          obtain ⟨code, statics, next⟩ := refined.code pc op decoded live
          have actualStep := step_raise op body target (maps method) pc (maps method pc) args
            frame stack m exception ⟨refined.profile, refined.returnsValue, statics, next⟩ stepped
          simp only [found, code, actualStep, Except.mapError, bind, Except.bind]
          rfl
        | ok action =>
          simp only [stepped, Except.mapError] at h
          have live : op.live = true := by
            cases op <;> first | rfl | exact (step_unsupported stepped).elim
          obtain ⟨code, statics, next⟩ := refined.code pc op decoded live
          have actualStep := step_relabel op body target (maps method) pc (maps method pc) args
            frame stack m action ⟨refined.profile, refined.returnsValue, statics, next⟩ stepped
          simp only [found, code, actualStep, Except.mapError, bind, Except.bind]
          cases action with
          | next target' stack' frame' m' =>
            dsimp only [FrameAction.relabel] at h ⊢
            exact ih method target' args frame' stack' m' outcome h transported
          | call callee arguments rest m' =>
            dsimp only [FrameAction.relabel] at h ⊢
            cases child : expected[callee]? with
            | none =>
              simp only [child] at h
              subst h
              obtain ⟨_, thrown⟩ := transported
              cases thrown
            | some childBody =>
              simp only [child] at h ⊢
              obtain ⟨childTarget, childFound, childRefines⟩ :=
                refines.method callee childBody child
              simp only [childFound, enterFrame_congr childRefines]
              cases entered : enterFrame childBody arguments m' with
              | error _ => simp only [entered] at h ⊢; subst h; rfl
              | ok setup =>
                simp only [entered] at h ⊢
                cases ran : run expected fuel callee 0 arguments setup.1 [] setup.2 with
                | error fault =>
                  simp only [ran] at h
                  subst h
                  have childRun := ih callee 0 arguments setup.1 [] setup.2 _ ran transported
                  rw [childRefines.entry] at childRun
                  simp only [childRun, Except.mapError]
                | ok returned =>
                  simp only [ran] at h
                  have childRun := ih callee 0 arguments setup.1 [] setup.2 _ ran trivial
                  rw [childRefines.entry] at childRun
                  simp only [childRun, Except.mapError]
                  have resumed := ih method (pc + 1) args frame (returned.2 ++ rest) returned.1
                    outcome h transported
                  rw [next (continues_of_invocation stepped trivial)] at resumed
                  exact resumed
          | tailCall callee arguments m' =>
            dsimp only [FrameAction.relabel] at h ⊢
            cases child : expected[callee]? with
            | none =>
              simp only [child] at h
              subst h
              obtain ⟨_, thrown⟩ := transported
              cases thrown
            | some childBody =>
              simp only [child] at h ⊢
              obtain ⟨childTarget, childFound, childRefines⟩ :=
                refines.method callee childBody child
              simp only [childFound, childRefines.returnsValue, refined.returnsValue,
                enterFrame_congr childRefines]
              split at h
              · subst h; obtain ⟨_, thrown⟩ := transported; cases thrown
              · rename_i returns
                simp only [returns, ↓reduceIte]
                cases checked : arguments.mapM (checkedValue (leaveFrame frame m')) with
                | error fault => simp only [checked] at h ⊢; subst h; rfl
                | ok values =>
                  simp only [checked] at h ⊢
                  cases entered : enterFrame childBody values (leaveFrame frame m') with
                  | error fault => simp only [entered] at h ⊢; subst h; rfl
                  | ok setup =>
                    simp only [entered] at h ⊢
                    have childRun := ih callee 0 values setup.1 [] setup.2 _ h transported
                    rw [childRefines.entry] at childRun
                    exact childRun
          | construct callee arguments rest frame' temporary kind m' =>
            dsimp only [FrameAction.relabel] at h ⊢
            cases child : expected[callee]? with
            | none =>
              simp only [child] at h
              subst h
              obtain ⟨_, thrown⟩ := transported
              cases thrown
            | some childBody =>
              simp only [child] at h ⊢
              obtain ⟨childTarget, childFound, childRefines⟩ :=
                refines.method callee childBody child
              simp only [childFound, enterFrame_congr childRefines]
              cases entered : enterFrame childBody arguments m' with
              | error _ => simp only [entered] at h ⊢; subst h; rfl
              | ok setup =>
                simp only [entered] at h ⊢
                cases ran : run expected fuel callee 0 arguments setup.1 [] setup.2 with
                | error fault =>
                  simp only [ran] at h
                  subst h
                  have childRun := ih callee 0 arguments setup.1 [] setup.2 _ ran transported
                  rw [childRefines.entry] at childRun
                  simp only [childRun, Except.mapError]
                | ok returned =>
                  simp only [ran] at h
                  have childRun := ih callee 0 arguments setup.1 [] setup.2 _ ran trivial
                  rw [childRefines.entry] at childRun
                  simp only [childRun, Except.mapError]
                  split at h
                  · subst h
                    obtain ⟨_, thrown⟩ := transported
                    cases thrown
                  · rename_i empty
                    simp only [empty]
                    cases loaded : loadLocal returned.1 (.bytes kind temporary) with
                    | error _ => simp only [loaded] at h ⊢; subst h; rfl
                    | ok value =>
                      simp only [loaded] at h ⊢
                      have resumed := ih method (pc + 1) args frame' (value :: rest) returned.1
                        outcome h transported
                      rw [next (continues_of_invocation stepped trivial)] at resumed
                      exact resumed
          | returned values m' =>
            dsimp only [FrameAction.relabel] at h ⊢
            cases checked : List.mapM (checkedValue (leaveFrame frame m')) values with
            | error _ => simp only [checked] at h ⊢; subst h; rfl
            | ok _ => simp only [checked] at h ⊢; subst h; rfl

/-- A successful expected run is the actual run from the renamed pc, with the same fuel and
    result. -/
theorem run_refines {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) :
    ∀ fuel method pc args frame stack (m : Memory) result,
      run expected fuel method pc args frame stack m = .ok result →
      run actual fuel method (maps method pc) args frame stack m = .ok result :=
  fun fuel method pc args frame stack m result h =>
    run_outcome_refines refines fuel method pc args frame stack m (.ok result) h trivial

/-- An expected run that throws `exception` throws it in the actual run, at the relocated pc. -/
theorem run_raise_refines {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) {fuel method pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {fault : LocatedFault} {exception : String}
    (h : run expected fuel method pc args frame stack m = .error fault)
    (thrown : fault.fault = .thrown exception) :
    run actual fuel method (maps method pc) args frame stack m = .error (fault.relocate maps) :=
  run_outcome_refines refines fuel method pc args frame stack m _ h ⟨exception, thrown⟩

/-- A result or thrown exception of an expected invocation is the actual one's, with the
    fault relocated. -/
theorem invoke_outcome_refines {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) {fuel method : Nat} {args : List Value}
    {m : Memory} {outcome : Except LocatedFault (Memory × List Value)}
    (h : invoke expected fuel method args m = outcome) (transported : Transported outcome) :
    invoke actual fuel method args m = outcome.mapError (·.relocate maps) := by
  unfold invoke at h ⊢
  cases fetched : expected[method]? with
  | none =>
    simp only [fetched] at h
    subst h
    obtain ⟨_, thrown⟩ := transported
    cases thrown
  | some body =>
    obtain ⟨target, found, refined⟩ := refines.method method body fetched
    simp only [fetched, found, enterFrame_congr refined, bind, Except.bind,
      Except.mapError] at h ⊢
    cases checkedArgs : args.mapM (checkedValue m) with
    | error _ =>
      simp only [checkedArgs] at h ⊢
      subst h
      simp only [LocatedFault.relocate, refined.entry]
    | ok checked =>
      simp only [checkedArgs] at h ⊢
      cases entered : enterFrame body checked m with
      | error _ =>
        simp only [entered] at h ⊢
        subst h
        simp only [LocatedFault.relocate, refined.entry]
      | ok setup =>
        simp only [entered] at h ⊢
        have ran :=
          run_outcome_refines refines fuel method 0 _ setup.1 [] setup.2 outcome h transported
        rw [refined.entry] at ran
        exact ran

/-- A successful expected invocation is the actual invocation with the same fuel and result. -/
theorem invoke_refines {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) {fuel method : Nat} {args : List Value}
    {m : Memory} {result : Memory × List Value}
    (h : invoke expected fuel method args m = .ok result) :
    invoke actual fuel method args m = .ok result :=
  invoke_outcome_refines refines h trivial

/-- An expected invocation that throws `exception` throws it in the actual one, at the
    relocated pc. -/
theorem invoke_raise_refines {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) {fuel method : Nat} {args : List Value}
    {m : Memory} {fault : LocatedFault} {exception : String}
    (h : invoke expected fuel method args m = .error fault)
    (thrown : fault.fault = .thrown exception) :
    invoke actual fuel method args m = .error (fault.relocate maps) :=
  invoke_outcome_refines refines h ⟨exception, thrown⟩

/-- `LiveState` depends on the program only through its static descriptors. -/
theorem LiveState.of_descriptors {expected actual : CIL.Program}
    (same : programStaticDescriptors expected = programStaticDescriptors actual)
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory}
    (live : LiveState expected args frame stack m) : LiveState actual args frame stack m :=
  ⟨live.memory, live.arguments, live.stack, live.references, live.owned, same ▸ live.statics⟩

/-- An expected invocation certificate is one of the actual program. -/
theorem InvocationCertificate.of_refines {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) {method : Nat} {args : List Value}
    {initial : Memory} {fuel : Nat} {final : Memory} {values : List Value}
    (certificate : InvocationCertificate expected method args initial fuel final values) :
    InvocationCertificate actual method args initial fuel final values := by
  obtain ⟨_, body, frame, entered, lookup, checked, setup, finished, live, _, _⟩ := certificate
  obtain ⟨target, found, refined⟩ := refines.method method body lookup
  have ran := run_refines refines fuel method 0 args frame [] entered (final, values) finished
  rw [refined.entry] at ran
  exact certify_invocation actual method target args initial frame entered fuel final values
    found checked (by rw [enterFrame_congr refined]; exact setup)
    (live.of_descriptors refines.descriptors) ran

/-- `MethodEmbeds program index expected` lets `program.set index expected` stand in for
    `program`. -/
theorem _root_.CIL.MethodEmbeds.refines {program : CIL.Program} {index : Nat}
    {expected : CIL.Method} (embeds : MethodEmbeds program index expected) :
    ∃ maps, ProgramRefines (program.set index expected) program maps := by
  obtain ⟨target, map, found, embedded⟩ := embeds
  exact ⟨_, (ProgramRefines.refl program).set found embedded⟩

/-- Substituting an embedded method keeps the program-wide static descriptors. -/
theorem _root_.CIL.MethodEmbeds.descriptors {program : CIL.Program} {index : Nat}
    {expected : CIL.Method} (embeds : MethodEmbeds program index expected) :
    programStaticDescriptors (program.set index expected) = programStaticDescriptors program := by
  obtain ⟨_, refines⟩ := embeds.refines
  exact refines.descriptors

/-- A successful invocation with `expected` in place of method `index` is one of `program`. -/
theorem _root_.CIL.MethodEmbeds.invoke {program : CIL.Program} {index : Nat}
    {expected : CIL.Method} (embeds : MethodEmbeds program index expected) {fuel method : Nat}
    {args : List Value} {m : Memory} {result : Memory × List Value}
    (h : CIL.Safety.invoke (program.set index expected) fuel method args m = .ok result) :
    CIL.Safety.invoke program fuel method args m = .ok result := by
  obtain ⟨_, refines⟩ := embeds.refines
  exact invoke_refines refines h

/-- An expected throw is `program`'s, at the pc the map assigns in method `index` and
    unchanged elsewhere. -/
theorem _root_.CIL.Embeds.invoke_raise {program : CIL.Program} {index : Nat}
    {expected target : CIL.Method} {map : List Nat} (found : program[index]? = some target)
    (embeds : Embeds expected target map)
    {fuel method : Nat} {args : List Value} {m : Memory} {fault : LocatedFault} {exception : String}
    (h : CIL.Safety.invoke (program.set index expected) fuel method args m = .error fault)
    (thrown : fault.fault = .thrown exception) :
    CIL.Safety.invoke program fuel method args m =
      .error (fault.relocate fun j => if j = index then rename map target.code.length else id) :=
  invoke_raise_refines ((ProgramRefines.refl program).set found embeds) h thrown

/-- An invocation certificate with `expected` in place of method `index` is one of
    `program`. -/
theorem _root_.CIL.MethodEmbeds.certificate {program : CIL.Program} {index : Nat}
    {expected : CIL.Method} (embeds : MethodEmbeds program index expected) {method : Nat}
    {args : List Value} {initial : Memory} {fuel : Nat} {final : Memory} {values : List Value}
    (certificate :
      InvocationCertificate (program.set index expected) method args initial fuel final values) :
    InvocationCertificate program method args initial fuel final values := by
  obtain ⟨_, refines⟩ := embeds.refines
  exact certificate.of_refines refines

end CIL.Safety
