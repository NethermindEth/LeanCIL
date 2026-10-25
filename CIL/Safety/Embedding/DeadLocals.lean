import CIL.Safety.Embedding.Outcomes

/-!
# Refinement modulo dead locals

`EmbedsDeadLocals expected actual map` lets `actual` declare trailing locals that `expected`
lacks, provided each is a managed reference initialized to null or left unmodeled. Frame
entry creates such a local as a root slot without allocating, so every allocation identity and
every memory state is the same with or without it; the only difference is the frame's slot
list, which is `expected`'s followed by the dead slots. Instructions address locals by index,
so a step that succeeds or throws with the shorter list behaves the same with the longer one.

The proof composes two refinements: `Embeds expected (actual.withLocalsOf expected) map`,
which the existing simulation handles, and `run_padded`, which runs the same code under frames
padded with the dead slots. Numeric dead locals are not covered: each allocates a home, which
shifts every later allocation identity.
-/

namespace CIL.Safety

open CIL.Embedding

/-- `frame` with the slots `extra` placed after its locals. -/
def Frame.appendLocals (frame : Frame) (extra : List LocalSlot) : Frame :=
  { frame with locals := frame.locals ++ extra }

/-- Padding with no slots leaves a frame unchanged. -/
@[simp] theorem Frame.appendLocals_nil (frame : Frame) : frame.appendLocals [] = frame := by
  simp [Frame.appendLocals]

#print axioms CIL.Safety.Frame.appendLocals_nil

/-- The action with `extra` slots after the locals of the frame it resumes in. -/
def FrameAction.appendLocals (extra : List LocalSlot) : FrameAction → FrameAction
  | .next target stack frame memory => .next target stack (frame.appendLocals extra) memory
  | .construct callee args rest frame temporary kind memory =>
    .construct callee args rest (frame.appendLocals extra) temporary kind memory
  | action => action

/-- A step outcome the padded simulation carries: a success or a thrown exception. -/
def StepKept : ExecutionResult α → Prop
  | .ok _ => True
  | .error fault => ∃ exception, fault = .thrown exception

/-- A local present in `frame` is the same slot after padding. -/
theorem Frame.appendLocals_getElem? {frame : Frame} {extra : List LocalSlot} {index : Nat}
    {slot : LocalSlot} (found : frame.locals[index]? = some slot) :
    (frame.appendLocals extra).locals[index]? = some slot := by
  simp only [Frame.appendLocals]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

#print axioms CIL.Safety.Frame.appendLocals_getElem?

/-- Storing to a local present in `frame` commutes with padding. -/
theorem Frame.appendLocals_set {frame : Frame} {extra : List LocalSlot} {index : Nat}
    {slot old : LocalSlot} (found : frame.locals[index]? = some old) :
    { frame.appendLocals extra with
        locals := (frame.appendLocals extra).locals.set index slot } =
      { frame with locals := frame.locals.set index slot }.appendLocals extra := by
  simp only [Frame.appendLocals]
  rw [List.set_append_left _ _ (List.getElem?_eq_some_iff.mp found).1]

#print axioms CIL.Safety.Frame.appendLocals_set

/-- Closes `step` on a padded frame against the unpadded step mapped through the padding,
    splitting both sides in lockstep; fails on a branch that reads a local the unpadded frame
    lacks. -/
local macro "frame_natural" : tactic => `(tactic| repeat' (first
  | rfl
  | contradiction
  | (simp only [map_bind, map_pure, FrameAction.appendLocals, Frame.appendLocals]; done)
  | split
  | (apply bind_congr; intro)
  | simp only [map_bind]))

-- Splitting every dispatcher arm takes about 300000 heartbeats.
set_option maxHeartbeats 400000 in
/-- A step that succeeds or throws in `frame` does the same in `frame` padded with `extra`,
    resuming in the padded frame: instructions only read locals the unpadded frame has. -/
theorem step_appendLocals (body : CIL.Method) (op : CIL.Op) (pc : Nat) (args : List Value)
    (frame : Frame) (extra : List LocalSlot) (stack : List Value) (memory : Memory)
    (outcome : ExecutionResult FrameAction)
    (stepped : step body op pc args frame stack memory = outcome) (kept : StepKept outcome) :
    step body op pc args (frame.appendLocals extra) stack memory =
      FrameAction.appendLocals extra <$> outcome := by
  subst stepped
  cases op
  case «local» index _ | vectorLocal index | vectorLocalAddr index | setVectorLocal index
    | localAddr index | setLocal index _ =>
    cases found : frame.locals[index]? with
    | some slot =>
      cases stack <;>
        simp only [step, found, Frame.appendLocals_getElem? found,
          Frame.appendLocals_set found] <;>
        frame_natural
    | none =>
      revert kept
      cases stack <;> simp only [step, found] <;> repeat' split
      all_goals first | (simp [StepKept]; done) | (intro; frame_natural; done)
  all_goals (simp only [step]; frame_natural)

#print axioms step_appendLocals

/-- Replacing a body's locals keeps every step that succeeds or throws: steps read the
    profile, return arity and static sites, never the local declarations. -/
theorem step_withLocalsOf (actual expected : CIL.Method) (op : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (outcome : ExecutionResult FrameAction)
    (stepped : step (actual.withLocalsOf expected) op pc args frame stack memory = outcome)
    (kept : StepKept outcome) :
    step actual op pc args frame stack memory = outcome := by
  have context : StepContext (actual.withLocalsOf expected) actual id op pc pc :=
    ⟨rfl, rfl, rfl, fun _ => rfl⟩
  cases outcome with
  | ok action =>
    have same := step_relabel op _ actual id pc pc args frame stack memory action context stepped
    rw [Op.relabel_id] at same
    rw [same]
    cases action <;> rfl
  | error fault =>
    obtain ⟨exception, thrown⟩ := kept
    subst thrown
    have same := step_raise op _ actual id pc pc args frame stack memory exception context stepped
    rwa [Op.relabel_id] at same

#print axioms step_withLocalsOf

/-- The slot frame entry gives a root local with initializer `initial`. -/
def rootSlot : CIL.Value → LocalSlot
  | .nullRef => .root (some .null)
  | _ => .root none

/-- A root local is created without touching memory. -/
theorem makeLocal_root {kind : CIL.LocalKind} {initial : CIL.Value}
    (root : rootLocal kind initial = true) (activation : Nat) (memory : Memory) :
    makeLocal activation kind initial memory = .ok (rootSlot initial, [], memory) := by
  unfold rootLocal at root
  split at root <;> first | rfl | cases root

#print axioms CIL.Safety.makeLocal_root

/-- Root locals are created without touching memory, each as its `rootSlot`. -/
theorem makeLocals_roots (activation : Nat) : ∀ (kinds : List CIL.LocalKind)
    (initials : List CIL.Value) (memory : Memory), rootLocals kinds initials = true →
      makeLocals activation kinds initials memory = .ok (initials.map rootSlot, [], memory)
  | [], [], _, _ => rfl
  | kind :: kinds, initial :: initials, memory, roots => by
    simp only [rootLocals, List.length_cons, List.zip_cons_cons, List.all_cons,
      Bool.and_eq_true, beq_iff_eq, Nat.add_right_cancel_iff] at roots
    obtain ⟨length, root, rest⟩ := roots
    have tail := makeLocals_roots activation kinds initials memory
      (by simp only [rootLocals, Bool.and_eq_true, beq_iff_eq]; exact ⟨length, rest⟩)
    simp [makeLocals, makeLocal_root root, tail, bind, Except.bind, pure, Except.pure]
  | [], _ :: _, _, roots | _ :: _, [], _, roots => by simp [rootLocals] at roots

#print axioms makeLocals_roots

/-- Pads the slots of a `makeLocals` result with the root slots of `deadInitials`. -/
def padSlots (deadInitials : List CIL.Value) :
    List LocalSlot × List AllocationId × Memory → List LocalSlot × List AllocationId × Memory
  | (slots, owned, memory) => (slots ++ deadInitials.map rootSlot, owned, memory)

/-- Trailing root locals add their root slots and nothing else to the frame's locals. -/
theorem makeLocals_append (activation : Nat) {deadKinds : List CIL.LocalKind}
    {deadInitials : List CIL.Value} (roots : rootLocals deadKinds deadInitials = true) :
    ∀ (kinds : List CIL.LocalKind) (initials : List CIL.Value) (memory : Memory),
      kinds.length = initials.length →
      makeLocals activation (kinds ++ deadKinds) (initials ++ deadInitials) memory =
        padSlots deadInitials <$> makeLocals activation kinds initials memory
  | [], [], memory, _ => by
    simp [makeLocals_roots activation _ _ memory roots, makeLocals, padSlots]; rfl
  | kind :: kinds, initial :: initials, memory, length => by
    simp only [List.cons_append, makeLocals, map_bind]
    refine bind_congr fun ⟨slot, owned, memory⟩ => ?_
    rw [makeLocals_append activation roots kinds initials memory (by simpa using length),
      bind_map_left]
    refine bind_congr fun ⟨slots, other, memory⟩ => ?_
    simp [padSlots]
  | [], _ :: _, _, length | _ :: _, [], _, length => by simp at length

#print axioms makeLocals_append

/-- Root locals at positions outside `indices` are created as by `makeLocals`. -/
theorem makeSelectedLocalsFrom_roots (activation : Nat) (indices : List Nat) :
    ∀ (start : Nat) (kinds : List CIL.LocalKind) (initials : List CIL.Value) (memory : Memory),
      (∀ index ∈ indices, index < start) → rootLocals kinds initials = true →
      makeSelectedLocalsFrom activation indices start kinds initials memory =
        .ok (initials.map rootSlot, [], memory)
  | _, [], [], _, _, _ => rfl
  | start, kind :: kinds, initial :: initials, memory, below, roots => by
    simp only [rootLocals, List.length_cons, List.zip_cons_cons, List.all_cons,
      Bool.and_eq_true, beq_iff_eq, Nat.add_right_cancel_iff] at roots
    obtain ⟨length, root, rest⟩ := roots
    have outside : start ∉ indices := fun member => Nat.lt_irrefl _ (below start member)
    have tail := makeSelectedLocalsFrom_roots activation indices (start + 1) kinds initials
      memory (fun index member => Nat.lt_succ_of_lt (below index member))
      (by simp only [rootLocals, Bool.and_eq_true, beq_iff_eq]; exact ⟨length, rest⟩)
    simp [makeSelectedLocalsFrom, outside, makeLocal_root root, tail, bind, Except.bind, pure,
      Except.pure]
  | _, [], _ :: _, _, _, roots | _, _ :: _, [], _, _, roots => by simp [rootLocals] at roots

#print axioms makeSelectedLocalsFrom_roots

/-- Trailing root locals past every opaque index add only their root slots. -/
theorem makeSelectedLocalsFrom_append (activation : Nat) (indices : List Nat)
    {deadKinds : List CIL.LocalKind} {deadInitials : List CIL.Value}
    (roots : rootLocals deadKinds deadInitials = true) :
    ∀ (start : Nat) (kinds : List CIL.LocalKind) (initials : List CIL.Value) (memory : Memory),
      kinds.length = initials.length → (∀ index ∈ indices, index < start + kinds.length) →
      makeSelectedLocalsFrom activation indices start (kinds ++ deadKinds)
          (initials ++ deadInitials) memory =
        padSlots deadInitials <$> makeSelectedLocalsFrom activation indices start kinds initials
          memory
  | start, [], [], memory, _, below => by
    simp [makeSelectedLocalsFrom_roots activation indices start _ _ memory
      (by simpa using below) roots, makeSelectedLocalsFrom]; rfl
  | start, kind :: kinds, initial :: initials, memory, length, below => by
    have tail := fun memory => makeSelectedLocalsFrom_append activation indices roots
      (start + 1) kinds initials memory (by simpa using length)
      (fun index member => by have := below index member; simp at this; omega)
    simp only [List.cons_append, makeSelectedLocalsFrom]
    repeat' split
    all_goals try rfl
    all_goals
      simp only [map_bind]
      refine bind_congr fun ⟨slot, owned, memory⟩ => ?_
      rw [tail memory, bind_map_left]
      refine bind_congr fun ⟨slots, other, memory⟩ => ?_
      simp [padSlots]
  | _, [], _ :: _, _, length, _ | _, _ :: _, [], _, length, _ => by simp at length

#print axioms makeSelectedLocalsFrom_append

/-- The root slots of `actual`'s locals past `expected`'s. -/
def deadSlots (expected actual : CIL.Method) : List LocalSlot :=
  (actual.locals.drop expected.locals.length).map rootSlot

/-- Under `EmbedsDeadLocals`, `actual` enters the frame `actual.withLocalsOf expected` enters,
    padded with the dead root slots, in the same memory. -/
theorem enterFrame_deadLocals {expected actual : CIL.Method} {map : List Nat}
    (embeds : EmbedsDeadLocals expected actual map) (args : List Value) (memory : Memory) :
    enterFrame actual args memory =
      (fun setup => (setup.1.appendLocals (deadSlots expected actual), setup.2)) <$>
        enterFrame (actual.withLocalsOf expected) args memory := by
  have bounded := List.all_eq_true.mp embeds.opaqueVectorLocals
  have kept : actual.opaqueVectorLocals = expected.opaqueVectorLocals :=
    embeds.embeds.opaqueVectorLocals
  have roots := embeds.dead
  have selected : makeSelectedLocals memory.nextIdentity actual.opaqueVectorLocals
      actual.localKinds actual.locals memory =
        padSlots (actual.locals.drop expected.locals.length) <$> makeSelectedLocals
          memory.nextIdentity actual.opaqueVectorLocals expected.localKinds expected.locals
          memory := by
    conv => lhs; rw [embeds.localKinds, embeds.locals]
    unfold makeSelectedLocals
    split
    · exact makeLocals_append _ roots _ _ _ embeds.initialized
    · exact makeSelectedLocalsFrom_append _ _ roots 0 _ _ _ embeds.initialized
        (fun index member => by rw [kept] at member; simpa using bounded index member)
  simp only [enterFrame, Method.withLocalsOf, selected, embeds.parameterHomes, bind_map_left,
    map_bind]
  refine bind_congr fun ⟨slots, owned, entered⟩ => ?_
  refine bind_congr fun ⟨arguments, argumentIds, entered⟩ => ?_
  simp [makeParameterHomes, padSlots, deadSlots, Frame.appendLocals]

#print axioms enterFrame_deadLocals

/-- Each method `j` of `unpadded` runs as the same method of `program` once its frames carry
    the slots `extra j` after their locals: the code is the same, every step that succeeds or
    throws is the same, and frame entry agrees up to that padding. -/
structure PaddedRefines (unpadded program : CIL.Program) (extra : Nat → List LocalSlot) :
    Prop where
  method : ∀ index body, unpadded[index]? = some body →
    ∃ target, program[index]? = some target ∧ target.code = body.code ∧
    (∀ op pc args frame stack memory outcome,
      step body op pc args frame stack memory = outcome → StepKept outcome →
      step target op pc args frame stack memory = outcome) ∧
    ∀ args memory, enterFrame target args memory =
      (fun setup => (setup.1.appendLocals (extra index), setup.2)) <$>
        enterFrame body args memory

/-- A result or thrown exception of a run of `unpadded` is the same outcome of the run of
    `program` in the padded frame; pcs and faults are unchanged. -/
theorem run_padded {unpadded program : CIL.Program} {extra : Nat → List LocalSlot}
    (refines : PaddedRefines unpadded program extra) :
    ∀ fuel method pc args frame stack (memory : Memory) outcome,
      run unpadded fuel method pc args frame stack memory = outcome → Transported outcome →
      run program fuel method pc args (frame.appendLocals (extra method)) stack memory =
        outcome := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ _ _ _ ran transported
    subst ran
    obtain ⟨_, thrown⟩ := transported
    cases thrown
  | succ fuel ih =>
    intro method pc args frame stack memory outcome ran transported
    rw [run] at ran ⊢
    cases fetched : unpadded[method]? with
    | none =>
      simp only [fetched] at ran
      subst ran
      obtain ⟨_, thrown⟩ := transported
      cases thrown
    | some body =>
      simp only [fetched] at ran
      obtain ⟨target, found, code, steps, entries⟩ := refines.method method body fetched
      cases decoded : body.code[pc]? with
      | none =>
        simp only [decoded] at ran
        subst ran
        obtain ⟨_, thrown⟩ := transported
        cases thrown
      | some op =>
        simp only [decoded, bind, Except.bind] at ran
        cases stepped : step body op pc args frame stack memory with
        | error fault =>
          simp only [stepped, Except.mapError] at ran
          subst ran
          obtain ⟨exception, thrown⟩ := transported
          dsimp only at thrown
          subst thrown
          have kept : StepKept (Except.error (ε := ExecutionFault) (α := FrameAction)
              (.thrown exception)) := ⟨exception, rfl⟩
          have padded := step_appendLocals target op pc args frame (extra method) stack memory
            _ (steps op pc args frame stack memory _ stepped kept) kept
          simp only [found, code, decoded, padded, Except.mapError, bind, Except.bind]
          rfl
        | ok action =>
          simp only [stepped, Except.mapError] at ran
          have padded := step_appendLocals target op pc args frame (extra method) stack memory
            _ (steps op pc args frame stack memory _ stepped trivial) trivial
          simp only [found, code, decoded, padded, Except.mapError, bind, Except.bind]
          cases action with
          | next target' stack' frame' memory' =>
            exact ih method target' args frame' stack' memory' outcome ran transported
          | call callee arguments rest memory' =>
            dsimp only [FrameAction.appendLocals, Functor.map, Except.map]
            cases child : unpadded[callee]? with
            | none =>
              simp only [child] at ran
              subst ran
              obtain ⟨_, thrown⟩ := transported
              cases thrown
            | some childBody =>
              simp only [child] at ran
              obtain ⟨childTarget, childFound, _, _, childEntries⟩ :=
                refines.method callee childBody child
              simp only [childFound, childEntries]
              cases entered : enterFrame childBody arguments memory' with
              | error _ =>
                simp only [entered] at ran ⊢; subst ran; rfl
              | ok setup =>
                simp only [entered] at ran ⊢
                cases childRan : run unpadded fuel callee 0 arguments setup.1 [] setup.2 with
                | error fault =>
                  simp only [childRan] at ran
                  subst ran
                  have padded := ih callee 0 arguments setup.1 [] setup.2 _ childRan transported
                  simp only [Functor.map, Except.map, padded]
                | ok returned =>
                  simp only [childRan] at ran
                  have padded := ih callee 0 arguments setup.1 [] setup.2 _ childRan trivial
                  simp only [Functor.map, Except.map, padded]
                  exact ih method (pc + 1) args frame (returned.2 ++ rest) returned.1 outcome ran
                    transported
          | construct callee arguments rest frame' temporary kind memory' =>
            dsimp only [FrameAction.appendLocals, Functor.map, Except.map]
            cases child : unpadded[callee]? with
            | none =>
              simp only [child] at ran
              subst ran
              obtain ⟨_, thrown⟩ := transported
              cases thrown
            | some childBody =>
              simp only [child] at ran
              obtain ⟨childTarget, childFound, _, _, childEntries⟩ :=
                refines.method callee childBody child
              simp only [childFound, childEntries]
              cases entered : enterFrame childBody arguments memory' with
              | error _ =>
                simp only [entered] at ran ⊢; subst ran; rfl
              | ok setup =>
                simp only [entered] at ran ⊢
                cases childRan : run unpadded fuel callee 0 arguments setup.1 [] setup.2 with
                | error fault =>
                  simp only [childRan] at ran
                  subst ran
                  have padded := ih callee 0 arguments setup.1 [] setup.2 _ childRan transported
                  simp only [Functor.map, Except.map, padded]
                | ok returned =>
                  simp only [childRan] at ran
                  have padded := ih callee 0 arguments setup.1 [] setup.2 _ childRan trivial
                  simp only [Functor.map, Except.map, padded]
                  split at ran
                  · subst ran
                    obtain ⟨_, thrown⟩ := transported
                    cases thrown
                  · rename_i empty
                    simp only [empty]
                    cases loaded : loadLocal returned.1 (.bytes kind temporary) with
                    | error _ => simp only [loaded] at ran ⊢; subst ran; rfl
                    | ok value =>
                      simp only [loaded] at ran ⊢
                      exact ih method (pc + 1) args frame' (value :: rest) returned.1 outcome
                        ran transported
          | returned values memory' =>
            dsimp only [FrameAction.appendLocals, Functor.map, Except.map]
            exact ran

#print axioms run_padded

/-- A result or thrown exception of an invocation of `unpadded` is the same outcome of the
    invocation of `program`. -/
theorem invoke_padded {unpadded program : CIL.Program} {extra : Nat → List LocalSlot}
    (refines : PaddedRefines unpadded program extra) {fuel method : Nat} {args : List Value}
    {memory : Memory} {outcome : Except LocatedFault (Memory × List Value)}
    (invoked : invoke unpadded fuel method args memory = outcome)
    (transported : Transported outcome) : invoke program fuel method args memory = outcome := by
  unfold invoke at invoked ⊢
  cases fetched : unpadded[method]? with
  | none =>
    simp only [fetched] at invoked
    subst invoked
    obtain ⟨_, thrown⟩ := transported
    cases thrown
  | some body =>
    obtain ⟨target, found, _, _, entries⟩ := refines.method method body fetched
    simp only [fetched, found, entries, bind, Except.bind, Except.mapError] at invoked ⊢
    cases checked : args.mapM (checkedValue memory) with
    | error _ => simp only [checked] at invoked ⊢; exact invoked
    | ok values =>
      simp only [checked] at invoked ⊢
      cases entered : enterFrame body values memory with
      | error _ => simp only [entered] at invoked ⊢; exact invoked
      | ok setup =>
        simp only [entered] at invoked ⊢
        exact run_padded refines fuel method 0 values setup.1 [] setup.2 outcome invoked
          transported

#print axioms invoke_padded

/-- `program` with method `index` given `expected`'s locals runs as `program`, padding the
    frames of method `index` with the dead slots. -/
theorem _root_.CIL.EmbedsDeadLocals.padded {program : CIL.Program} {index : Nat}
    {expected actual : CIL.Method} {map : List Nat} (found : program[index]? = some actual)
    (embeds : EmbedsDeadLocals expected actual map) :
    PaddedRefines (program.set index (actual.withLocalsOf expected)) program
      (fun method => if method = index then deadSlots expected actual else []) := by
  refine ⟨fun method body fetched => ?_⟩
  rw [List.getElem?_set] at fetched
  by_cases same : index = method
  · subst same
    have bound : index < program.length := (List.getElem?_eq_some_iff.mp found).1
    simp only [bound, ite_true, Option.some.injEq] at fetched
    subst fetched
    refine ⟨actual, found, rfl, fun op pc args frame stack memory outcome stepped kept =>
      step_withLocalsOf actual expected op pc args frame stack memory outcome stepped kept,
      fun args memory => ?_⟩
    simp only [ite_true]
    exact enterFrame_deadLocals embeds args memory
  · simp only [same, ite_false] at fetched
    refine ⟨body, fetched, rfl, fun _ _ _ _ _ _ _ stepped _ => stepped, fun args memory => ?_⟩
    simp only [Ne.symm same, ite_false, Frame.appendLocals_nil]
    cases enterFrame body args memory <;> rfl

#print axioms CIL.EmbedsDeadLocals.padded

/-- The fault relocation `Embeds.invoke_raise` applies: method `index` renamed by `map` over
    `actual`'s code, every other method unchanged. -/
def deadLocalsRelocation (index : Nat) (actual : CIL.Method) (map : List Nat) :
    Nat → Nat → Nat :=
  fun method => if method = index then rename map actual.code.length else id

/-- A result or thrown exception of an invocation with `expected` in place of method `index`
    is `program`'s, with a thrown fault relocated into `actual`'s code. -/
theorem _root_.CIL.EmbedsDeadLocals.invoke_outcome {program : CIL.Program} {index : Nat}
    {expected actual : CIL.Method} {map : List Nat} (found : program[index]? = some actual)
    (embeds : EmbedsDeadLocals expected actual map) {fuel method : Nat} {args : List Value}
    {memory : Memory} {outcome : Except LocatedFault (Memory × List Value)}
    (invoked : invoke (program.set index expected) fuel method args memory = outcome)
    (transported : Transported outcome) :
    invoke program fuel method args memory =
      outcome.mapError (·.relocate (deadLocalsRelocation index actual map)) := by
  have bound : index < program.length := (List.getElem?_eq_some_iff.mp found).1
  have kept : (program.set index (actual.withLocalsOf expected))[index]? =
      some (actual.withLocalsOf expected) := List.getElem?_set_self (by simpa using bound)
  have embedded := (ProgramRefines.refl (program.set index (actual.withLocalsOf expected))).set
    kept embeds.embeds
  rw [List.set_set] at embedded
  have relocated := invoke_outcome_refines embedded invoked transported
  refine invoke_padded (embeds.padded found) relocated ?_
  cases outcome with
  | ok _ => trivial
  | error fault => exact transported

#print axioms CIL.EmbedsDeadLocals.invoke_outcome

/-- A successful invocation with `expected` in place of method `index` is one of `program`. -/
theorem _root_.CIL.MethodEmbedsDeadLocals.invoke {program : CIL.Program} {index : Nat}
    {expected : CIL.Method} (embeds : MethodEmbedsDeadLocals program index expected)
    {fuel method : Nat} {args : List Value} {memory : Memory} {result : Memory × List Value}
    (invoked : invoke (program.set index expected) fuel method args memory = .ok result) :
    invoke program fuel method args memory = .ok result := by
  obtain ⟨_, _, found, embedded⟩ := embeds
  exact embedded.invoke_outcome found invoked trivial

#print axioms CIL.MethodEmbedsDeadLocals.invoke

/-- An expected throw is `program`'s, at the pc the map assigns in method `index` and
    unchanged elsewhere. -/
theorem _root_.CIL.EmbedsDeadLocals.invoke_raise {program : CIL.Program} {index : Nat}
    {expected actual : CIL.Method} {map : List Nat} (found : program[index]? = some actual)
    (embeds : EmbedsDeadLocals expected actual map) {fuel method : Nat} {args : List Value}
    {memory : Memory} {fault : LocatedFault} {exception : String}
    (invoked : invoke (program.set index expected) fuel method args memory = .error fault)
    (thrown : fault.fault = .thrown exception) :
    invoke program fuel method args memory =
      .error (fault.relocate (deadLocalsRelocation index actual map)) :=
  embeds.invoke_outcome found invoked ⟨exception, thrown⟩

#print axioms CIL.EmbedsDeadLocals.invoke_raise

/-- A named exception raised with `expected` in place of method `index` is raised by
    `program`. -/
theorem _root_.CIL.MethodEmbedsDeadLocals.raises {program : CIL.Program} {index : Nat}
    {expected : CIL.Method} (embeds : MethodEmbedsDeadLocals program index expected)
    {method : Nat} {args : List Value} {memory : Memory} {exception : String}
    (raised : Raises (program.set index expected) method args memory exception) :
    Raises program method args memory exception := by
  obtain ⟨_, _, found, embedded⟩ := embeds
  obtain ⟨fuel, fault, invoked, thrown⟩ := raised
  exact ⟨fuel, _, embedded.invoke_raise found invoked thrown, thrown⟩

#print axioms CIL.MethodEmbedsDeadLocals.raises

/-- A method contract proved with `expected` in place of method `index` holds for
    `program`. -/
theorem _root_.CIL.MethodEmbedsDeadLocals.method_holds {Input Output : Type}
    {contract : MethodContract Input Output} {program : CIL.Program} {index : Nat}
    {expected : CIL.Method} (embeds : MethodEmbedsDeadLocals program index expected)
    {method : Nat} (holds : contract.Holds (program.set index expected) method) :
    contract.Holds program method := by
  intro input initial permitted
  obtain ⟨fuel, final, values, invoked, confined, returns⟩ := holds input initial permitted
  exact ⟨fuel, final, values, embeds.invoke invoked, confined, returns⟩

#print axioms CIL.MethodEmbedsDeadLocals.method_holds

/-- An outcome contract proved with `expected` in place of method `index` holds for
    `program`. -/
theorem _root_.CIL.MethodEmbedsDeadLocals.holds {Input Output : Type}
    {contract : OutcomeContract Input Output} {program : CIL.Program} {index : Nat}
    {expected : CIL.Method} (embeds : MethodEmbedsDeadLocals program index expected)
    {method : Nat} (holds : contract.Holds (program.set index expected) method) :
    contract.Holds program method := by
  intro input initial permitted
  have outcome := holds input initial permitted
  split
  · rename_i raised
    rw [raised] at outcome
    exact embeds.raises outcome
  · rename_i raised
    rw [raised] at outcome
    obtain ⟨fuel, final, values, invoked, confined, returns⟩ := outcome
    exact ⟨fuel, final, values, embeds.invoke invoked, confined, returns⟩

#print axioms CIL.MethodEmbedsDeadLocals.holds

end CIL.Safety
