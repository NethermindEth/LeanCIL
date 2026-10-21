import CIL.Safety.Embedding.Step
import CIL.Safety.Certificate

/-!
A program whose methods embed into the methods of another program simulates it:
every successful checked run, invocation or invocation certificate of the
expected program is one of the actual program, with each pc renamed by its
method's map. Only successful results transfer; a fault reports the pc it
occurred at, which the renaming changes.
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
  vectorArgs : actual.vectorArgs = expected.vectorArgs
  parameterHomes : actual.parameterHomes = expected.parameterHomes
  descriptors : actual.staticSites.map Prod.snd = expected.staticSites.map Prod.snd
  entry : r 0 = 0
  code : ∀ p op, expected.code[p]? = some op → op.live = true →
    actual.code[r p]? = some (op.relabel r) ∧ staticAt actual (r p) = staticAt expected p ∧
    (op.continues = true → r (p + 1) = r p + 1)

theorem BodyRefines.refl (body : Method) : BodyRefines body body id :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ op found _ => ⟨by simp [found, Op.relabel_id], rfl, fun _ => rfl⟩⟩

theorem mem_sites {limit : Nat} {code : List Op} {map : List Nat} {start p : Nat} {op : Op}
    (found : code[p]? = some op) (live : op.live = true) :
    (⟨start + p, map.getD p limit, map.getD (p + 1) limit, op⟩ : Site) ∈ sites limit start code map := by
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

theorem _root_.CIL.Embeds.refines {expected actual : Method} {map : List Nat} (embeds : Embeds expected actual map) :
    BodyRefines expected actual (rename map actual.code.length) := by
  refine ⟨embeds.profile, embeds.returnsValue, embeds.locals, embeds.localKinds, embeds.vectorArgs,
    embeds.parameterHomes, embeds.descriptors, embeds.entry, ?_⟩
  intro p op found live
  have member := mem_sites (limit := actual.code.length) (map := map) (start := 0) found live
  rw [Nat.zero_add] at member
  have picked := embeds.code
  have dropped := pick_eq actual.code ((sites actual.code.length 0 expected.code map).map Site.image) 0
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

theorem enterFrame_congr {expected actual : CIL.Method} {r : Nat → Nat} (refines : BodyRefines expected actual r)
    (args : List Value) (m : Memory) : enterFrame actual args m = enterFrame expected args m := by
  simp only [enterFrame, refines.locals, refines.localKinds, refines.vectorArgs, refines.parameterHomes]

theorem step_unsupported {body : CIL.Method} {description : String} {pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body (.unsupported description) pc args frame stack m = .ok action) : False := by
  change Except.error (ExecutionFault.unsupported "Non-memory instruction requires execution adapter") = .ok action at h
  cases h

theorem step_ret_returns {body : CIL.Method} {narrow : Option NarrowKind} {pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : step body (.ret narrow) pc args frame stack m = .ok action) :
    ∃ values m', action = .returned values m' := by
  cases narrow
  · change (if stack.length = (if body.returnsValue then 1 else 0) then
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
        (do return FrameAction.returned (← [Value.scalar (.i32 (kind.extend bits))].mapM (checkedValue m)) m)
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
  case unsupported => exact (step_unsupported h).elim
  case branch target =>
    change Except.ok (.next target stack frame m) = .ok action at h
    cases h
    exact resumes.elim
  case ret narrow =>
    obtain ⟨_, _, rfl⟩ := step_ret_returns h
    exact resumes.elim
  all_goals rfl

/-- Each method of `expected` embeds into the same method of `actual` under `maps`. -/
structure ProgramRefines (expected actual : CIL.Program) (maps : Nat → Nat → Nat) : Prop where
  method : ∀ index body, expected[index]? = some body →
    ∃ target, actual[index]? = some target ∧ BodyRefines body target (maps index)
  descriptors : programStaticDescriptors expected = programStaticDescriptors actual

theorem ProgramRefines.refl (program : CIL.Program) : ProgramRefines program program (fun _ => id) :=
  ⟨fun _ body found => ⟨body, found, BodyRefines.refl body⟩, rfl⟩

theorem programStaticDescriptors_set (program : CIL.Program) (index : Nat) (body : CIL.Method)
    (same : ∀ old, program[index]? = some old → old.staticSites.map Prod.snd = body.staticSites.map Prod.snd) :
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

/-- Replacing one expected method by a body that embeds into the actual method keeps the refinement. -/
theorem ProgramRefines.set {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) {index : Nat} {body target : CIL.Method} {map : List Nat}
    (found : actual[index]? = some target) (embeds : Embeds body target map) :
    ProgramRefines (expected.set index body)  actual
      (fun j => if j = index then rename map target.code.length else maps j) := by
  constructor
  · intro j candidate fetched
    by_cases same : j = index
    · subst same
      simp only [List.getElem?_set_self'] at fetched
      cases present : expected[j]? <;> simp [present] at fetched
      subst fetched
      exact ⟨target, found, by simpa using embeds.refines⟩
    · rw [List.getElem?_set_ne (Ne.symm same)] at fetched
      simpa [same] using refines.method j candidate fetched
  · rw [programStaticDescriptors_set _ _ _ ?_]
    · exact refines.descriptors
    · intro old present
      obtain ⟨actualOld, fetched, oldRefines⟩ := refines.method index old present
      rw [found] at fetched
      cases fetched
      exact oldRefines.descriptors.symm.trans embeds.descriptors

/-- A successful expected run is the actual run from the renamed pc, with the same fuel and result. -/
theorem run_refines {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) :
    ∀ fuel method pc args frame stack (m : Memory) result,
      run expected fuel method pc args frame stack m = .ok result →
      run actual fuel method (maps method pc) args frame stack m = .ok result := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ h; cases h
  | succ fuel ih =>
    intro method pc args frame stack m result h
    rw [run] at h ⊢
    cases fetched : expected[method]? with
    | none => simp only [fetched] at h; cases h
    | some body =>
      simp only [fetched] at h
      obtain ⟨target, found, refined⟩ := refines.method method body fetched
      cases decoded : body.code[pc]? with
      | none => simp only [decoded] at h; cases h
      | some op =>
        simp only [decoded, bind, Except.bind] at h
        cases stepped : step body op pc args frame stack m with
        | error _ => simp only [stepped, Except.mapError] at h; cases h
        | ok action =>
          simp only [stepped, Except.mapError] at h
          have live : op.live = true := by
            cases op <;> first | rfl | exact (step_unsupported stepped).elim
          obtain ⟨code, statics, next⟩ := refined.code pc op decoded live
          have actualStep := step_relabel op body target (maps method) pc (maps method pc) args frame stack m action
            ⟨refined.profile, refined.returnsValue, statics, next⟩ stepped
          simp only [found, code, actualStep, Except.mapError, bind, Except.bind]
          cases action with
          | next target' stack' frame' m' =>
            dsimp only [FrameAction.relabel] at h ⊢
            exact ih method target' args frame' stack' m' result h
          | call callee arguments rest m' =>
            dsimp only [FrameAction.relabel] at h ⊢
            cases child : expected[callee]? with
            | none => simp only [child] at h ⊢; cases h
            | some childBody =>
              simp only [child] at h ⊢
              obtain ⟨childTarget, childFound, childRefines⟩ := refines.method callee childBody child
              simp only [childFound, enterFrame_congr childRefines]
              cases entered : enterFrame childBody arguments m' with
              | error _ => simp only [entered] at h; cases h
              | ok setup =>
                simp only [entered] at h ⊢
                cases ran : run expected fuel callee 0 arguments setup.1 [] setup.2 with
                | error _ => simp only [ran] at h; cases h
                | ok returned =>
                  simp only [ran] at h
                  have childRun := ih callee 0 arguments setup.1 [] setup.2 returned ran
                  rw [childRefines.entry] at childRun
                  simp only [childRun]
                  have resumed := ih method (pc + 1) args frame (returned.2 ++ rest) returned.1 result h
                  rw [next (continues_of_invocation stepped trivial)] at resumed
                  exact resumed
          | construct callee arguments rest frame' temporary kind m' =>
            dsimp only [FrameAction.relabel] at h ⊢
            cases child : expected[callee]? with
            | none => simp only [child] at h ⊢; cases h
            | some childBody =>
              simp only [child] at h ⊢
              obtain ⟨childTarget, childFound, childRefines⟩ := refines.method callee childBody child
              simp only [childFound, enterFrame_congr childRefines]
              cases entered : enterFrame childBody arguments m' with
              | error _ => simp only [entered] at h; cases h
              | ok setup =>
                simp only [entered] at h ⊢
                cases ran : run expected fuel callee 0 arguments setup.1 [] setup.2 with
                | error _ => simp only [ran] at h; cases h
                | ok returned =>
                  simp only [ran] at h
                  have childRun := ih callee 0 arguments setup.1 [] setup.2 returned ran
                  rw [childRefines.entry] at childRun
                  simp only [childRun]
                  split at h
                  · cases h
                  · rename_i empty
                    simp only [empty]
                    cases loaded : loadLocal returned.1 (.bytes kind temporary) with
                    | error _ => simp only [loaded] at h; cases h
                    | ok value =>
                      simp only [loaded] at h ⊢
                      have resumed := ih method (pc + 1) args frame' (value :: rest) returned.1 result h
                      rw [next (continues_of_invocation stepped trivial)] at resumed
                      exact resumed
          | returned values m' =>
            dsimp only [FrameAction.relabel] at h ⊢
            cases checked : List.mapM (checkedValue (leaveFrame frame m')) values with
            | error _ => simp only [checked] at h; cases h
            | ok _ => simp only [checked] at h ⊢; exact h


/-- A successful expected invocation is the actual invocation with the same fuel and result. -/
theorem invoke_refines {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) {fuel method : Nat} {args : List Value} {m : Memory}
    {result : Memory × List Value} (h : invoke expected fuel method args m = .ok result) :
    invoke actual fuel method args m = .ok result := by
  unfold invoke at h ⊢
  cases fetched : expected[method]? with
  | none => simp only [fetched] at h; cases h
  | some body =>
    obtain ⟨target, found, refined⟩ := refines.method method body fetched
    simp only [fetched, found, enterFrame_congr refined, bind, Except.bind, Except.mapError] at h ⊢
    cases checkedArgs : args.mapM (checkedValue m) with
    | error _ => simp only [checkedArgs] at h; cases h
    | ok checked =>
      simp only [checkedArgs] at h ⊢
      cases entered : enterFrame body checked m with
      | error _ => simp only [entered] at h; cases h
      | ok setup =>
        simp only [entered] at h ⊢
        have ran := run_refines refines fuel method 0 _ setup.1 [] setup.2 result h
        rw [refined.entry] at ran
        exact ran


theorem LiveState.of_descriptors {expected actual : CIL.Program}
    (same : programStaticDescriptors expected = programStaticDescriptors actual)
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory}
    (live : LiveState expected args frame stack m) : LiveState actual args frame stack m :=
  ⟨live.memory, live.arguments, live.stack, live.references, live.owned, same ▸ live.statics⟩

/-- An expected invocation certificate is one of the actual program. -/
theorem InvocationCertificate.of_refines {expected actual : CIL.Program} {maps : Nat → Nat → Nat}
    (refines : ProgramRefines expected actual maps) {method : Nat} {args : List Value} {initial : Memory}
    {fuel : Nat} {final : Memory} {values : List Value}
    (certificate : InvocationCertificate expected method args initial fuel final values) :
    InvocationCertificate actual method args initial fuel final values := by
  obtain ⟨_, body, frame, entered, lookup, checked, setup, finished, live, _, _⟩ := certificate
  obtain ⟨target, found, refined⟩ := refines.method method body lookup
  have ran := run_refines refines fuel method 0 args frame [] entered (final, values) finished
  rw [refined.entry] at ran
  exact certify_invocation actual method target args initial frame entered fuel final values found checked
    (by rw [enterFrame_congr refined]; exact setup) (live.of_descriptors refines.descriptors) ran


/-- `MethodEmbeds program index expected` lets `program.set index expected` stand in for `program`. -/
theorem _root_.CIL.MethodEmbeds.refines {program : CIL.Program} {index : Nat} {expected : CIL.Method}
    (embeds : MethodEmbeds program index expected) :
    ∃ maps, ProgramRefines (program.set index expected) program maps := by
  obtain ⟨target, map, found, embedded⟩ := embeds
  exact ⟨_, (ProgramRefines.refl program).set found embedded⟩

theorem _root_.CIL.MethodEmbeds.descriptors {program : CIL.Program} {index : Nat} {expected : CIL.Method}
    (embeds : MethodEmbeds program index expected) :
    programStaticDescriptors (program.set index expected) = programStaticDescriptors program := by
  obtain ⟨_, refines⟩ := embeds.refines
  exact refines.descriptors

theorem _root_.CIL.MethodEmbeds.invoke {program : CIL.Program} {index : Nat} {expected : CIL.Method}
    (embeds : MethodEmbeds program index expected) {fuel method : Nat} {args : List Value} {m : Memory}
    {result : Memory × List Value} (h : CIL.Safety.invoke (program.set index expected) fuel method args m = .ok result) :
    CIL.Safety.invoke program fuel method args m = .ok result := by
  obtain ⟨_, refines⟩ := embeds.refines
  exact invoke_refines refines h

theorem _root_.CIL.MethodEmbeds.certificate {program : CIL.Program} {index : Nat} {expected : CIL.Method}
    (embeds : MethodEmbeds program index expected) {method : Nat} {args : List Value} {initial : Memory}
    {fuel : Nat} {final : Memory} {values : List Value}
    (certificate : InvocationCertificate (program.set index expected) method args initial fuel final values) :
    InvocationCertificate program method args initial fuel final values := by
  obtain ⟨_, refines⟩ := embeds.refines
  exact certificate.of_refines refines


end CIL.Safety
