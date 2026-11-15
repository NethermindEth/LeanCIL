import CIL.Safety.SegmentLocals
import CIL.Safety.RuntimeExceptions
import CIL.Safety.RegionRun

/-! Segment contracts retain checked interpreter outcomes and memory confinement. -/

namespace CIL.Safety

/-- Stable outcomes agree across a prefix, which consumes at least `cost` fuel. -/
structure ReachesRun (program : CIL.Program) (method start finish cost : Nat)
    (arguments : List Value) (before after : SegmentState) : Prop where
  spends : forall fuel outcome, Stable outcome ->
    run program fuel method start arguments before.frame before.stack before.memory = outcome ->
      And (cost <= fuel)
        (run program (fuel - cost) method finish arguments after.frame after.stack after.memory =
          outcome)
  continues : forall fuel outcome, Stable outcome ->
    run program fuel method finish arguments after.frame after.stack after.memory = outcome ->
      Exists fun more =>
        run program more method start arguments before.frame before.stack before.memory = outcome

/-- Every exact segment preserves stable outcomes with its exact fuel lower bound. -/
theorem SegmentRun.reaches {program : CIL.Program} {method start finish cost : Nat}
    {arguments : List Value} {before after : SegmentState}
    (exactRun : SegmentRun program method start finish cost arguments before after) :
    ReachesRun program method start finish cost arguments before after := by
  constructor
  next =>
    intro fuel outcome settled ran
    have bound : cost <= fuel := by
      apply Classical.byContradiction
      intro short
      have more := run_mono program fuel (cost - fuel) method start arguments
        before.frame before.stack before.memory outcome settled ran
      have zero := exactRun 0
      rw [Nat.zero_add] at zero
      rw [show fuel + (cost - fuel) = cost by omega, zero] at more
      simp only [run] at more
      rw [<- more] at settled
      exact settled rfl
    exact And.intro bound (by
      have equation := exactRun (fuel - cost)
      rw [Nat.sub_add_cancel bound, ran] at equation
      exact equation.symm)
  next =>
    intro fuel outcome _ ran
    exact Exists.intro (fuel + cost) ((exactRun fuel).trans ran)

#print axioms SegmentRun.reaches

/-- Adjacent reaching prefixes add their fuel lower bounds. -/
theorem ReachesRun.trans {program : CIL.Program}
    {method start middle finish first second : Nat}
    {arguments : List Value} {before intermediate after : SegmentState}
    (head : ReachesRun program method start middle first arguments before intermediate)
    (tail : ReachesRun program method middle finish second arguments intermediate after) :
    ReachesRun program method start finish (first + second) arguments before after := by
  constructor
  next =>
    intro fuel outcome settled ran
    cases head.spends fuel outcome settled ran
    rename_i headBound headRun
    cases tail.spends (fuel - first) outcome settled headRun
    rename_i tailBound tailRun
    exact And.intro (by omega) (by simpa [Nat.sub_sub] using tailRun)
  next =>
    intro fuel outcome settled ran
    cases tail.continues fuel outcome settled ran
    rename_i middleFuel middleRun
    exact head.continues middleFuel outcome settled middleRun

#print axioms ReachesRun.trans

/-- A successful continuation proves the same postcondition before the prefix. -/
theorem ReachesRun.wp {program : CIL.Program} {method start finish cost : Nat}
    {arguments : List Value} {before after : SegmentState}
    {post : Prod Memory (List Value) -> Prop}
    (reached : ReachesRun program method start finish cost arguments before after)
    (rest : WP (Execution (fun fuel =>
      run program fuel method finish arguments after.frame after.stack after.memory)) post) :
    WP (Execution (fun fuel =>
      run program fuel method start arguments before.frame before.stack before.memory)) post := by
  cases rest
  rename_i fuel resultWitness
  cases resultWitness
  rename_i result runPost
  cases runPost
  rename_i ran satisfied
  cases reached.continues fuel (.ok result) trivial ran
  rename_i more continued
  exact Exists.intro more (Exists.intro result (And.intro continued satisfied))

#print axioms ReachesRun.wp

/-- A returning callee reaches the caller continuation with its results pushed.
    The checked step supplies the callee arguments independently of the caller stack. -/
theorem ReachesRun.call {program : CIL.Program} {method pc callee : Nat}
    {body child : CIL.Method} {op : CIL.Instruction}
    {arguments stack values rest results : List Value} {frame childFrame : Frame}
    {memory updated entered final : Memory} {calleeFuel : Nat}
    (found : program[method]? = some body) (instruction : body.code[pc]? = some op)
    (stepped : step body op pc arguments frame stack memory =
      .ok (.call callee values rest updated))
    (calleeFound : program[callee]? = some child)
    (enter : enterFrame child values updated = .ok (childFrame, entered))
    (returned : run program calleeFuel callee 0 values childFrame [] entered =
      .ok (final, results)) :
    ReachesRun program method pc (pc + 1) 1 arguments
      { frame := frame, stack := stack, memory := memory }
      { frame := frame, stack := results ++ rest, memory := final } := by
  constructor
  next =>
    intro fuel outcome settled ran
    cases fuel with
    | zero =>
      simp only [run] at ran
      subst outcome
      exact False.elim (settled rfl)
    | succ fuel =>
      simp only [run, found, instruction, stepped, calleeFound, enter,
        Bind.bind, Except.bind, Except.mapError] at ran
      cases childRun : run program fuel callee 0 values childFrame [] entered with
      | error fault =>
        simp only [childRun] at ran
        have childSettled : Stable (.error fault : Except LocatedFault
            (Prod Memory (List Value))) := by simpa [ran] using settled
        have failed := run_mono program fuel calleeFuel callee 0 values childFrame [] entered
          (.error fault) childSettled childRun
        have succeeded := run_mono program calleeFuel fuel callee 0 values childFrame [] entered
          (.ok (final, results)) trivial returned
        rw [Nat.add_comm, failed] at succeeded
        cases succeeded
      | ok result =>
        have actual := run_mono program fuel calleeFuel callee 0 values childFrame [] entered
          (.ok result) trivial childRun
        have expected := run_mono program calleeFuel fuel callee 0 values childFrame [] entered
          (.ok (final, results)) trivial returned
        rw [Nat.add_comm, actual] at expected
        cases Except.ok.inj expected
        exact And.intro (by omega) (by simpa [childRun] using ran)
  next =>
    intro fuel outcome settled ran
    have childRun := run_mono program calleeFuel fuel callee 0 values childFrame [] entered
      (.ok (final, results)) trivial returned
    have continuation := run_mono program fuel calleeFuel method (pc + 1) arguments frame
      (results ++ rest) final outcome settled ran
    refine Exists.intro (calleeFuel + fuel + 1) ?_
    simpa only [run, found, instruction, stepped, calleeFound, enter,
      Bind.bind, Except.bind, Except.mapError, childRun, Nat.add_comm fuel calleeFuel]
      using continuation

#print axioms ReachesRun.call

/-- Agreement on a closed region transports reaching between two positions inside it. -/
theorem ReachesRun.congr_region {program other : CIL.Program}
    {region : Nat -> Nat -> Prop} {method start finish cost : Nat}
    {arguments : List Value} {before after : SegmentState}
    (closed : RegionClosed program region) (agrees : AgreesOn program other region)
    (entry : region method start) (continuation : region method finish)
    (reached : ReachesRun program method start finish cost arguments before after) :
    ReachesRun other method start finish cost arguments before after := by
  constructor
  next =>
    intro fuel outcome settled ran
    rw [run_congr_region closed agrees _ _ _ _ _ _ _ entry] at ran
    cases reached.spends fuel outcome settled ran
    rename_i bound continued
    exact And.intro bound (by
      rw [run_congr_region closed agrees _ _ _ _ _ _ _ continuation]
      exact continued)
  next =>
    intro fuel outcome settled ran
    rw [run_congr_region closed agrees _ _ _ _ _ _ _ continuation] at ran
    cases reached.continues fuel outcome settled ran
    rename_i more continued
    exact Exists.intro more (by
      rw [run_congr_region closed agrees _ _ _ _ _ _ _ entry]
      exact continued)

#print axioms ReachesRun.congr_region

/-- Control reaches a continuation, returns, faults, or exhausts every fuel budget. -/
inductive SegmentExit where
  | reaches (pc : Nat) (state : SegmentState)
  | returns (memory : Memory) (values : List Value)
  | faults (fault : LocatedFault)
  | diverges

/-- The exit's fault names this CLR exception, including arithmetic exceptions. -/
def SegmentExit.Raises (exit : SegmentExit) (exception : CIL.ExceptionType) : Prop :=
  Exists fun fault => And (exit = .faults fault) (fault.fault.clrException = some exception)

/-- An exit has interpreter evidence. A fault exit is definite, so an `unsupported` fault is no
    exit; reaching also requires a positive fuel lower bound. -/
def SegmentExit.Exhibited (program : CIL.Program) (method start : Nat)
    (arguments : List Value) (before : SegmentState) : SegmentExit -> Prop
  | .reaches pc after => Exists fun cost => And (0 < cost)
      (ReachesRun program method start pc cost arguments before after)
  | .returns memory values => Exists fun fuel =>
      run program fuel method start arguments before.frame before.stack before.memory =
        .ok (memory, values)
  | .faults fault => And (fault.fault.definite ≠ false) (Exists fun fuel =>
      run program fuel method start arguments before.frame before.stack before.memory =
        .error fault)
  | .diverges => forall fuel, Exists fun fault => And (fault.fault = .fuelExhausted)
      (run program fuel method start arguments before.frame before.stack before.memory =
        .error fault)

/-- Continuing and returned memories preserve existing storage outside the footprint. -/
def SegmentExit.Confined (footprint : List (Prod Reference Nat)) (before : SegmentState) :
    SegmentExit -> Prop
  | .reaches _ after => CIL.Safety.Confined footprint before.memory after.memory
  | .returns memory _ => CIL.Safety.Confined footprint before.memory memory
  | .faults _ => True
  | .diverges => True

/-- The byte homes and widths of the frame slots a code segment of `body` stores to directly. -/
def SegmentState.localFootprint (body : CIL.Method) (code : List CIL.Instruction)
    (state : SegmentState) : List (Prod Reference Nat) :=
  let locals : Array LocalSlot := state.frame.locals.toArray
  (segmentStores body code).filterMap fun index => match locals[index]? with
    | some (LocalSlot.bytes kind home) => some (home, localWidth kind)
    | _ => none

/-- A boundary precondition, permitted memory writes and predicate on checked exits. -/
structure SegmentContract where
  pre : List Value -> SegmentState -> Prop
  footprint : List Value -> SegmentState -> List (Prod Reference Nat) := fun _ _ => []
  post : List Value -> SegmentState -> SegmentExit -> Prop

/-- Every permitted input exhibits an exit within the footprint satisfying the postcondition. -/
def SegmentContract.Holds (contract : SegmentContract) (program : CIL.Program)
    (method start : Nat) : Prop :=
  forall arguments before, contract.pre arguments before -> Exists fun exit =>
    And (exit.Exhibited program method start arguments before)
      (And (exit.Confined (contract.footprint arguments before) before)
        (contract.post arguments before exit))

/-- Named evidence retained by one application of a checked segment contract. -/
structure SegmentResult (contract : SegmentContract) (program : CIL.Program)
    (method start : Nat) (arguments : List Value) (before : SegmentState)
    (exit : SegmentExit) : Prop where
  ran : exit.Exhibited program method start arguments before
  framed : exit.Confined (contract.footprint arguments before) before
  post : contract.post arguments before exit

/-- An impossible precondition describes unused successors. -/
def SegmentContract.unreachable : SegmentContract where
  pre _ _ := False
  post _ _ _ := False

/-- An unreachable contract holds at every instruction position. -/
theorem SegmentContract.unreachable_holds (program : CIL.Program) (method start : Nat) :
    unreachable.Holds program method start := by
  intro arguments before impossible
  exact False.elim impossible

#print axioms SegmentContract.unreachable_holds

/-- A contract that reaches one specified continuation with a relational state postcondition. -/
def SegmentContract.continuing (finish : Nat) (pre : List Value -> SegmentState -> Prop)
    (post : List Value -> SegmentState -> SegmentState -> Prop)
    (footprint : List Value -> SegmentState -> List (Prod Reference Nat)) : SegmentContract where
  pre := pre
  footprint := footprint
  post arguments before
    | .reaches pc after => And (pc = finish) (post arguments before after)
    | _ => False

/-- An exact segment between increasing pcs supplies a positive reaching contract. -/
theorem Segment.contract {program : CIL.Program} {method start finish : Nat}
    {pre post : List Value -> SegmentState -> Prop}
    {footprint : List Value -> SegmentState -> List (Prod Reference Nat)}
    (segment : Segment program method start finish pre post) (distinct : start < finish)
    (framed : forall arguments before after, pre arguments before -> post arguments after ->
      Confined (footprint arguments before) before.memory after.memory) :
    (SegmentContract.continuing finish pre (fun arguments _ after => post arguments after)
      footprint).Holds program method start := by
  intro arguments before permitted
  cases segment arguments before permitted
  rename_i cost stateWitness
  cases stateWitness
  rename_i after runPost
  cases runPost
  rename_i exactRun satisfied
  have positive : 0 < cost := by
    cases cost with
    | zero =>
      have zero := exactRun 0
      simp only [run, Except.error.injEq, LocatedFault.mk.injEq] at zero
      omega
    | succ cost => omega
  exact Exists.intro (.reaches finish after)
    (And.intro (Exists.intro cost (And.intro positive exactRun.reaches))
      (And.intro (framed arguments before after permitted satisfied) (And.intro rfl satisfied)))

#print axioms Segment.contract

/-- A successful goal after each permitted exit establishes success before the segment. -/
def SegmentExit.Continues (program : CIL.Program) (method : Nat) (arguments : List Value)
    (post : Prod Memory (List Value) -> Prop) : SegmentExit -> Prop
  | .reaches pc after => WP (Execution (fun fuel =>
      run program fuel method pc arguments after.frame after.stack after.memory)) post
  | .returns memory values => post (memory, values)
  | .faults _ => False
  | .diverges => False

/-- A checked summary and its exit obligations imply a successful interpreter run. -/
theorem SegmentContract.Holds.wp {contract : SegmentContract} {program : CIL.Program}
    {method start : Nat} {arguments : List Value} {before : SegmentState}
    {post : Prod Memory (List Value) -> Prop}
    (holds : contract.Holds program method start) (permitted : contract.pre arguments before)
    (next : forall exit, SegmentResult contract program method start arguments before exit ->
      exit.Continues program method arguments post) :
    WP (Execution (fun fuel =>
      run program fuel method start arguments before.frame before.stack before.memory)) post := by
  cases holds arguments before permitted
  rename_i exit exitWitness
  cases exitWitness
  rename_i ran framedPost
  cases framedPost
  rename_i framed satisfied
  have rest := next exit { ran := ran, framed := framed, post := satisfied }
  cases exit with
  | reaches pc after =>
    cases ran
    rename_i cost progress
    cases progress
    rename_i _positive reached
    exact reached.wp rest
  | returns memory values =>
    cases ran
    rename_i fuel returned
    exact Exists.intro fuel (Exists.intro (memory, values) (And.intro returned rest))
  | faults fault => exact False.elim rest
  | diverges => exact False.elim rest

#print axioms SegmentContract.Holds.wp

/-- Named exceptions at an exit or its continuation give the same exception at entry. -/
theorem SegmentContract.Holds.raises {contract : SegmentContract} {program : CIL.Program}
    {method start : Nat} {arguments : List Value} {before : SegmentState}
    {exception : CIL.ExceptionType}
    (holds : contract.Holds program method start) (permitted : contract.pre arguments before)
    (next : forall exit, SegmentResult contract program method start arguments before exit ->
      Or (exit.Raises exception) (Exists fun pc => Exists fun after =>
        And (exit = .reaches pc after)
          (RunRaisesCLR program method pc arguments after.frame after.stack after.memory
            exception))) :
    RunRaisesCLR program method start arguments before.frame before.stack before.memory
      exception := by
  cases holds arguments before permitted
  rename_i exit exitWitness
  cases exitWitness
  rename_i ran framedPost
  cases framedPost
  rename_i framed satisfied
  rcases next exit { ran := ran, framed := framed, post := satisfied } with named | continued
  next =>
    cases named
    rename_i fault named
    rcases named.1 with rfl
    have named := named.2
    cases ran
    rename_i _settled failure
    cases failure
    rename_i fuel failed
    exact Exists.intro fuel (Exists.intro fault (And.intro failed named))
  next =>
    cases continued
    rename_i pc continued
    cases continued
    rename_i after continued
    rcases continued.1 with rfl
    have raised := continued.2
    cases ran
    rename_i cost progress
    cases progress
    rename_i _positive reached
    cases raised
    rename_i fuel faultWitness
    cases faultWitness
    rename_i fault failureName
    cases failureName
    rename_i failed named
    cases reached.continues fuel (.error fault) (settled_of_clrException named).stable failed
    rename_i more failed
    exact Exists.intro more (Exists.intro fault (And.intro failed named))

#print axioms SegmentContract.Holds.raises

/-- An exhibited exit after a reaching prefix is also exhibited before that prefix. -/
theorem ReachesRun.exhibited {program : CIL.Program} {method start finish cost : Nat}
    {arguments : List Value} {before after : SegmentState} {exit : SegmentExit}
    (reached : ReachesRun program method start finish cost arguments before after)
    (ran : exit.Exhibited program method finish arguments after) :
    exit.Exhibited program method start arguments before := by
  cases exit with
  | reaches pc final =>
    cases ran
    rename_i nextCost progress
    cases progress
    rename_i positive tail
    exact Exists.intro (cost + nextCost) (And.intro (by omega) (reached.trans tail))
  | returns memory values =>
    cases ran
    rename_i fuel returned
    exact reached.continues fuel (.ok (memory, values)) trivial returned
  | faults fault =>
    cases ran
    rename_i settled failure
    cases failure
    rename_i fuel failed
    exact And.intro settled (reached.continues fuel (.error fault)
      (Settled.stable (α := Prod Memory (List Value)) (outcome := .error fault) settled) failed)
  | diverges =>
    intro fuel
    cases actual : run program fuel method start arguments
        before.frame before.stack before.memory with
    | ok result =>
      cases reached.spends fuel (.ok result) trivial actual
      rename_i _bound continued
      cases ran (fuel - cost)
      rename_i fault failure
      cases failure
      rename_i _exhausted exhausted
      rw [continued] at exhausted
      cases exhausted
    | error fault =>
      refine Exists.intro fault (And.intro ?_ rfl)
      apply Classical.byContradiction
      intro settled
      cases reached.spends fuel (.error fault) settled actual
      rename_i _bound continued
      cases ran (fuel - cost)
      rename_i exhaustedFault failure
      cases failure
      rename_i exhausted failed
      rw [continued] at failed
      exact settled ((congrArg LocatedFault.fault (Except.error.inj failed)).trans exhausted)

#print axioms ReachesRun.exhibited

/-- Joined contracts preserve every stopping exit and compose each reachable successor. -/
theorem SegmentContract.Holds.seq {head : SegmentContract} {next : Nat -> SegmentContract}
    {composed : SegmentContract} {program : CIL.Program} {method start : Nat}
    (first : head.Holds program method start)
    (rest : forall pc, (next pc).Holds program method pc)
    (enters : forall arguments before, composed.pre arguments before -> head.pre arguments before)
    (links : forall arguments before pc after, composed.pre arguments before ->
      head.post arguments before (.reaches pc after) -> (next pc).pre arguments after)
    (stops : forall arguments before exit, composed.pre arguments before ->
      (forall pc after, Not (exit = .reaches pc after)) -> head.post arguments before exit ->
      exit.Confined (head.footprint arguments before) before ->
      And (exit.Confined (composed.footprint arguments before) before)
        (composed.post arguments before exit))
    (joins : forall arguments before pc after exit, composed.pre arguments before ->
      head.post arguments before (.reaches pc after) ->
      Confined (head.footprint arguments before) before.memory after.memory ->
      (next pc).post arguments after exit ->
      exit.Confined ((next pc).footprint arguments after) after ->
      And (exit.Confined (composed.footprint arguments before) before)
        (composed.post arguments before exit)) :
    composed.Holds program method start := by
  intro arguments before permitted
  cases first arguments before (enters arguments before permitted)
  rename_i exit exitWitness
  cases exitWitness
  rename_i ran framedPost
  cases framedPost
  rename_i framed satisfied
  cases exit with
  | reaches pc after =>
    cases ran
    rename_i cost progress
    cases progress
    rename_i _positive reached
    cases rest pc arguments after (links arguments before pc after permitted satisfied)
    rename_i final exitWitness
    cases exitWitness
    rename_i tail framedPost
    cases framedPost
    rename_i tailFramed tailPost
    exact Exists.intro final (And.intro (reached.exhibited tail)
      (joins arguments before pc after final permitted satisfied framed tailPost tailFramed))
  | returns memory values =>
    exact Exists.intro (.returns memory values) (And.intro ran
      (stops arguments before _ permitted (by intro pc after impossible; cases impossible)
        satisfied framed))
  | faults fault =>
    exact Exists.intro (.faults fault) (And.intro ran
      (stops arguments before _ permitted (by intro pc after impossible; cases impossible)
        satisfied framed))
  | diverges =>
    exact Exists.intro .diverges (And.intro ran
      (stops arguments before _ permitted (by intro pc after impossible; cases impossible)
        satisfied framed))

#print axioms SegmentContract.Holds.seq

/-- Two continuing contracts compose when their boundary predicates and footprints agree. -/
theorem SegmentContract.Holds.then {program : CIL.Program} {method start middle finish : Nat}
    {firstPre secondPre : List Value -> SegmentState -> Prop}
    {firstPost secondPost : List Value -> SegmentState -> SegmentState -> Prop}
    {firstFoot secondFoot footprint : List Value -> SegmentState -> List (Prod Reference Nat)}
    (first : (SegmentContract.continuing middle firstPre firstPost firstFoot).Holds
      program method start)
    (second : (SegmentContract.continuing finish secondPre secondPost secondFoot).Holds
      program method middle)
    (links : forall arguments before after, firstPre arguments before ->
      firstPost arguments before after -> secondPre arguments after)
    (covers : forall arguments before after, firstPre arguments before ->
      firstPost arguments before after ->
      And (forall entry, List.Mem entry (firstFoot arguments before) ->
        List.Mem entry (footprint arguments before))
      (forall entry, List.Mem entry (secondFoot arguments after) ->
        List.Mem entry (footprint arguments before))) :
    (SegmentContract.continuing finish firstPre
      (fun arguments before final => Exists fun after =>
        And (firstPost arguments before after) (secondPost arguments after final))
      footprint).Holds program method start := by
  intro arguments before permitted
  cases first arguments before permitted
  rename_i firstExit exitWitness
  cases exitWitness
  rename_i firstRun framedPost
  cases framedPost
  rename_i firstFramed firstSatisfied
  cases firstExit with
  | reaches pc after =>
    cases firstSatisfied
    rename_i destination firstPost
    rcases destination with rfl
    cases second arguments after (links arguments before after permitted firstPost)
    rename_i secondExit exitWitness
    cases exitWitness
    rename_i secondRun framedPost
    cases framedPost
    rename_i secondFramed secondPost
    cases secondExit with
    | reaches pc final =>
      cases secondPost
      rename_i destination secondPost
      rcases destination with rfl
      cases firstRun
      rename_i cost progress
      cases progress
      rename_i _positive reached
      cases covers arguments before after permitted firstPost
      rename_i firstCover secondCover
      exact Exists.intro (.reaches pc final) (And.intro (reached.exhibited secondRun)
        (And.intro ((firstFramed.widen firstCover).trans (secondFramed.widen secondCover))
          (And.intro rfl (Exists.intro after (And.intro firstPost secondPost)))))
    | returns memory values => exact False.elim secondPost
    | faults fault => exact False.elim secondPost
    | diverges => exact False.elim secondPost
  | returns memory values => exact False.elim firstSatisfied
  | faults fault => exact False.elim firstSatisfied
  | diverges => exact False.elim firstSatisfied

#print axioms SegmentContract.Holds.then

/-- A validated branch exposes its selected successor and preserves the incoming memory. -/
theorem SegmentContract.branch {program : CIL.Program} {method pc target : Nat}
    {body : CIL.Method} {op : CIL.Instruction}
    (pre taken : List Value -> SegmentState -> Prop)
    [_decidable : forall arguments state, Decidable (taken arguments state)]
    (popped : List Value -> SegmentState -> List Value)
    (found : program[method]? = some body) (instruction : body.code[pc]? = some op)
    (stepped : forall arguments state, pre arguments state ->
      step body op pc arguments state.frame state.stack state.memory =
        .ok (.next (if taken arguments state then target else pc + 1) (popped arguments state)
          state.frame state.memory)) :
    ({ pre := pre
       post := fun arguments before exit =>
         exit = .reaches (if taken arguments before then target else pc + 1)
           { frame := before.frame, stack := popped arguments before,
             memory := before.memory } } : SegmentContract).Holds program method pc := by
  intro arguments before permitted
  have exactRun : SegmentRun program method pc
      (if taken arguments before then target else pc + 1) 1 arguments before
      { frame := before.frame, stack := popped arguments before, memory := before.memory } := by
    intro fuel
    simp only [run, found, instruction, stepped arguments before permitted,
      Bind.bind, Except.bind, Except.mapError]
  exact Exists.intro (.reaches (if taken arguments before then target else pc + 1)
    { frame := before.frame, stack := popped arguments before, memory := before.memory })
    (And.intro (Exists.intro 1 (And.intro (by decide) exactRun.reaches))
      (And.intro (Confined.refl [] before.memory) rfl))

#print axioms SegmentContract.branch

/-- A validated branch composes with both successor summaries under explicit footprint coverage. -/
theorem SegmentContract.branch_seq {program : CIL.Program} {method pc target : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {composed : SegmentContract}
    (pre taken : List Value -> SegmentState -> Prop)
    [_decidable : forall arguments state, Decidable (taken arguments state)]
    (popped : List Value -> SegmentState -> List Value)
    (found : program[method]? = some body) (instruction : body.code[pc]? = some op)
    (stepped : forall arguments state, pre arguments state ->
      step body op pc arguments state.frame state.stack state.memory =
        .ok (.next (if taken arguments state then target else pc + 1) (popped arguments state)
          state.frame state.memory))
    (next : Nat -> SegmentContract) (rest : forall pc, (next pc).Holds program method pc)
    (enters : forall arguments before, composed.pre arguments before -> pre arguments before)
    (links : forall arguments before, composed.pre arguments before ->
      (next (if taken arguments before then target else pc + 1)).pre arguments
        { frame := before.frame, stack := popped arguments before, memory := before.memory })
    (joins : forall arguments before exit, composed.pre arguments before ->
      (next (if taken arguments before then target else pc + 1)).post arguments
        { frame := before.frame, stack := popped arguments before, memory := before.memory }
        exit ->
      exit.Confined ((next (if taken arguments before then target else pc + 1)).footprint arguments
        { frame := before.frame, stack := popped arguments before, memory := before.memory })
        { frame := before.frame, stack := popped arguments before, memory := before.memory } ->
      And (exit.Confined (composed.footprint arguments before) before)
        (composed.post arguments before exit)) :
    composed.Holds program method pc := by
  apply (SegmentContract.branch pre taken popped found instruction stepped).seq rest enters
  next =>
    intro arguments before nextPc after permitted matched
    cases matched
    exact links arguments before permitted
  next =>
    intro arguments before exit permitted stopped matched
    cases matched
    exact False.elim (stopped _ _ rfl)
  next =>
    intro arguments before nextPc after exit permitted matched _ satisfied framed
    cases matched
    exact joins arguments before exit permitted satisfied framed

#print axioms SegmentContract.branch_seq

end CIL.Safety
