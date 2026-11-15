import CIL

/-! Checked segment contracts bind placed opcodes and preserve interpreter outcomes. -/

namespace Tests.SegmentContract
open CIL.Safety

/-- A scalar boundary with arbitrary caller memory and frame. -/
def scalarState (frame : Frame) (memory : Memory) (value : CIL.W32) : SegmentState :=
  { frame := frame, stack := [.scalar (.i32 value)], memory := memory }

/-- An increment retains the frame, arguments and memory at its continuation. -/
def increment (finish : Nat) (arguments : List Value) (frame : Frame) (memory : Memory)
    (value : CIL.W32) : CIL.Safety.SegmentContract :=
  .continuing finish ((scalarState frame memory value).exact arguments)
    (fun actual _ after => (scalarState frame memory (value + 1)).exact arguments actual after)
    (fun _ _ => [])

/-- One placement proof binds both scalar instructions at every use of this contract. -/
theorem scalar_region {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (placed : CodeAt body start [.ldc_i4 1, .add])
    (arguments : List Value) (frame : Frame) (memory : Memory) (value : CIL.W32) :
    (increment (start + 2) arguments frame memory value).Holds program method start := by
  apply Segment.contract (by
    dsimp only [scalarState]
    cil_segment 2 [found, placed]) (by omega)
  intro actual before after permitted satisfied
  rcases permitted.1 with rfl
  rcases permitted.2 with rfl
  rcases satisfied.2 with rfl
  exact Confined.refl [] memory

#print axioms scalar_region

/-- Changing the arithmetic instruction invalidates the original placement proof. -/
def changed : CIL.Method :=
  { returnsValue := true, locals := [], code := [.ldc_i4 1, .sub, .ret] }

/-- Kernel-checked placement rejects reuse after an instruction changes. -/
theorem mutation_rejected : Not (CodeAt changed 0 [.ldc_i4 1, .add]) := by
  fail_if_success have placed : CodeAt changed 0 [.ldc_i4 1, .add] := by rfl
  simp [CodeAt, changed]

#print axioms mutation_rejected

/-- Division by zero provides an arithmetic fault with a CLR exception name. -/
def division : CIL.Method := { returnsValue := true, locals := [], code := [.div] }

/-- A divide-by-zero contract accepts the exact incoming scalar stack. -/
def dividing (arguments : List Value) (frame : Frame) (memory : Memory) :
    CIL.Safety.SegmentContract where
  pre := SegmentState.exact arguments
    { frame := frame, stack := [.scalar (.i32 0), .scalar (.i32 1)], memory := memory }
  post _ _ exit := exit.Raises .divideByZero

/-- The exception contract is witnessed by the checked interpreter's arithmetic fault. -/
theorem raises_region (arguments : List Value) (frame : Frame) (memory : Memory) :
    (dividing arguments frame memory).Holds [division] 0 0 := by
  intro actual before permitted
  rcases permitted.1 with rfl
  rcases permitted.2 with rfl
  refine Exists.intro (SegmentExit.faults
    (LocatedFault.mk 0 0 (.arithmetic .divideByZero))) (And.intro ?_ (And.intro trivial ?_))
  next =>
    exact And.intro (by decide) (Exists.intro 1 (by rfl))
  next =>
    exact Exists.intro _ (And.intro rfl rfl)

#print axioms raises_region

/-- The exception bridge preserves the CLR name at the run boundary. -/
theorem raises_run (arguments : List Value) (frame : Frame) (memory : Memory) :
    RunRaisesCLR [division] 0 0 arguments frame
      [.scalar (.i32 0), .scalar (.i32 1)] memory .divideByZero := by
  exact (raises_region arguments frame memory).raises (And.intro rfl rfl)
    (fun _ result => Or.inl result.post)

#print axioms raises_run

/-- The scalar prefix is followed by an ordinary value return. -/
def returning : CIL.Method :=
  { returnsValue := true, locals := [], code := [.ldc_i4 1, .add, .ret] }

/-- Consuming a reaching summary proves the actual returned scalar and released frame memory. -/
theorem scalar_return (arguments : List Value) (frame : Frame) (memory : Memory)
    (value : CIL.W32) :
    WP (Execution (fun fuel => run [returning] fuel 0 0 arguments frame
      [.scalar (.i32 value)] memory))
      (fun result => result = (leaveFrame frame memory, [.scalar (.i32 (value + 1))])) := by
  apply (scalar_region (program := [returning]) (method := 0) (start := 0)
    (by rfl) (by rfl) arguments frame memory value).wp (And.intro rfl rfl)
  intro exit result
  cases exit with
  | reaches pc after =>
    have satisfied := result.post
    rcases satisfied.1 with rfl
    rcases satisfied.2.2 with rfl
    exact Exists.intro 1 (Exists.intro _ (And.intro (by rfl) rfl))
  | returns memory values => exact False.elim result.post
  | faults fault => exact False.elim result.post
  | diverges => exact False.elim result.post

#print axioms scalar_return

/-- A terminating scalar body cannot exhibit a positive-cost return to its unchanged entry. -/
theorem empty_region_refused (arguments : List Value) (frame : Frame) (memory : Memory)
    (value : CIL.W32) :
    Not ((CIL.Safety.SegmentContract.continuing 0
      ((scalarState frame memory value).exact arguments)
      (fun _ before after => after = before) (fun _ _ => [])).Holds [returning] 0 0) := by
  intro holds
  cases holds arguments (scalarState frame memory value) (And.intro rfl rfl)
  rename_i exit witness
  have exhibited := witness.1
  have post := witness.2.2
  cases exit with
  | reaches pc after =>
    rcases post.1 with rfl
    rcases post.2 with rfl
    cases exhibited
    rename_i cost progress
    have positive := progress.1
    have reached := progress.2
    have returned : run [returning] 3 0 0 arguments frame [.scalar (.i32 value)] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 (value + 1))]) := by rfl
    have spent := reached.spends 3
      (.ok (leaveFrame frame memory, [.scalar (.i32 (value + 1))])) trivial returned
    have bound := spent.1
    have continued := spent.2
    have remaining : 3 - cost = 0 \/ 3 - cost = 1 \/ 3 - cost = 2 := by omega
    rcases remaining with zero | one | two
    all_goals simp only [*] at continued; cases continued
  | returns memory values => exact post
  | faults fault => exact post
  | diverges => exact post

#print axioms empty_region_refused

namespace DistinctArguments

/-- The caller increments the result of a two-argument call. -/
def caller : CIL.Method :=
  { returnsValue := true, locals := [], code := [.call 1 2, .ldc_i4 1, .add, .ret] }

/-- Subtraction distinguishes the callee's argument order. -/
def callee : CIL.Method :=
  { returnsValue := true, locals := [], code := [.ldarg 0, .ldarg 1, .sub, .ret] }

/-- The top-first stack places the second argument above the first argument. -/
def before (frame : Frame) (memory : Memory) : SegmentState :=
  { frame := frame, stack := [.scalar (.i32 2), .scalar (.i32 7)], memory := memory }

/-- The call reaches its continuation with first minus second on the stack. -/
theorem call_region (arguments : List Value) (frame : Frame) (memory : Memory) :
    (CIL.Safety.SegmentContract.continuing 1 ((before frame memory).exact arguments)
      (fun actual _ after => (scalarState frame memory 5).exact arguments actual after)
      (fun _ _ => [])).Holds [caller, callee] 0 0 := by
  intro actual state permitted
  rcases permitted.1 with rfl
  rcases permitted.2 with rfl
  have reached : ReachesRun [caller, callee] 0 0 1 1 actual
      (before frame memory) (scalarState frame memory 5) := by
    refine ReachesRun.call (program := [caller, callee]) (method := 0) (pc := 0) (callee := 1)
      (body := caller) (child := callee) (op := .call 1 2)
      (values := [.scalar (.i32 7), .scalar (.i32 2)]) (results := [.scalar (.i32 5)])
      (rest := []) (childFrame := { activation := memory.nextIdentity, locals := [], owned := [] })
      (updated := memory) (entered := memory) (calleeFuel := 4) ?_ ?_ ?_ ?_ ?_ ?_
    all_goals rfl
  exact Exists.intro (.reaches 1 (scalarState frame memory 5))
    (And.intro (Exists.intro 1 (And.intro (by decide) reached))
      (And.intro (Confined.refl [] memory) (And.intro rfl (And.intro rfl rfl))))

#print axioms call_region

/-- A call summary composes with its arithmetic continuation without repeating the callee proof. -/
theorem call_composition (arguments : List Value) (frame : Frame) (memory : Memory) :
    (CIL.Safety.SegmentContract.continuing 3 ((before frame memory).exact arguments)
      (fun actual _ final => Exists fun after =>
        And ((scalarState frame memory 5).exact arguments actual after)
          ((scalarState frame memory (5 + 1)).exact arguments actual final))
      (fun _ _ => [])).Holds [caller, callee] 0 0 := by
  exact (call_region arguments frame memory).then
    (scalar_region (program := [caller, callee]) (method := 0) (start := 1)
      (by rfl) (by rfl) arguments frame memory 5)
    (by intro actual state after _ satisfied; exact satisfied)
    (by intro actual state after _ _; exact And.intro (by simp) (by simp))

#print axioms call_composition

end DistinctArguments

/-- A backward branch retains the same boundary state for every iteration. -/
def spin : CIL.Method := { returnsValue := false, locals := [], code := [.br 0] }

/-- Every fuel budget for the backward branch ends in exhaustion. -/
theorem diverging_region (arguments : List Value) (state : SegmentState) :
    ({ pre := state.exact arguments
       post := fun _ _ exit => exit = .diverges } :
      CIL.Safety.SegmentContract).Holds [spin] 0 0 := by
  intro actual before permitted
  rcases permitted.1 with rfl
  rcases permitted.2 with rfl
  refine Exists.intro .diverges (And.intro ?_ (And.intro trivial rfl))
  intro fuel
  refine Exists.intro (LocatedFault.mk 0 0 .fuelExhausted) (And.intro rfl ?_)
  induction fuel with
  | zero => rfl
  | succ fuel previous =>
    cil_checked_steps 1 [spin]
    exact previous

#print axioms diverging_region

/-- Two scalar summaries retain their intermediate state without repeating instruction proofs. -/
theorem scalar_composition {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (placed : CodeAt body start ([.ldc_i4 1, .add] ++ [.ldc_i4 1, .add]))
    (arguments : List Value) (frame : Frame) (memory : Memory) (value : CIL.W32) :
    (CIL.Safety.SegmentContract.continuing (start + 4)
      ((scalarState frame memory value).exact arguments)
      (fun actual _before final => Exists fun after =>
        And ((scalarState frame memory (value + 1)).exact arguments actual after)
          ((scalarState frame memory (value + 1 + 1)).exact arguments actual final))
      (fun _ _ => [])).Holds program method start := by
  have first := scalar_region found placed.append_left arguments frame memory value
  have second := scalar_region found placed.append_right arguments frame memory (value + 1)
  have joined := first.then (footprint := fun _ _ => []) second
    (by intro actual before after _ satisfied; exact satisfied)
    (by intro actual before after _ _; exact And.intro (by simp) (by simp))
  simpa [increment, Nat.add_assoc] using joined

#print axioms scalar_composition

/-- A duplicate retains a scalar for the arithmetic region after a conditional branch. -/
def duplicated (frame : Frame) (memory : Memory) (value : CIL.W32) : SegmentState :=
  { frame := frame, stack := [.scalar (.i32 value), .scalar (.i32 value)], memory := memory }

/-- Both successors increment the retained scalar and reach their respective region boundaries. -/
def branchIncrement (start : Nat) (arguments : List Value) (frame : Frame) (memory : Memory)
    (value : CIL.W32) : CIL.Safety.SegmentContract where
  pre := (duplicated frame memory value).exact arguments
  post _ _ exit := exit = .reaches (if value = 0#32 then start + 6 else start + 4)
    (scalarState frame memory (value + 1))

/-- A branch and its two arithmetic successors compose using checked placement facts. -/
theorem branch_composition {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (placed : CodeAt body start
      [.dup, .brfalse (start + 4), .ldc_i4 1, .add, .ldc_i4 1, .add])
    (arguments : List Value) (frame : Frame) (memory : Memory) (value : CIL.W32) :
    (branchIncrement start arguments frame memory value).Holds program method (start + 1) := by
  let next := fun pc => if pc = start + 4 then
    increment (start + 6) arguments frame memory value else if pc = start + 2 then
    increment (start + 4) arguments frame memory value else
    CIL.Safety.SegmentContract.unreachable
  have takenRegion := scalar_region found (by
    simpa using placed.drop 4) arguments frame memory value
  have otherRegion := scalar_region found (by
    simpa using (placed.drop 2).take 2) arguments frame memory value
  have rest : forall pc, (next pc).Holds program method pc := by
    intro pc
    by_cases taken : pc = start + 4
    next =>
      subst pc
      simpa [next, Nat.add_assoc] using takenRegion
    next =>
      by_cases other : pc = start + 2
      next =>
        subst pc
        simpa [next, Nat.add_assoc] using otherRegion
      next =>
        simpa [next, taken, other] using
          CIL.Safety.SegmentContract.unreachable_holds program method pc
  apply CIL.Safety.SegmentContract.branch_seq (target := start + 4)
    ((duplicated frame memory value).exact arguments) (fun _ _ => value = 0#32)
    (fun _ _ => [.scalar (.i32 value)]) found (placed.lookup 1 (by rfl))
    (next := next) (rest := rest)
  next =>
    intro actual before permitted
    rcases permitted.1 with rfl
    rcases permitted.2 with rfl
    by_cases zero : value = 0#32 <;>
      simp [duplicated, step_brfalse_i32_eq, CIL.truth, zero, Nat.add_assoc] <;> rfl
  next =>
    intro actual before permitted
    exact permitted
  next =>
    intro actual before permitted
    rcases permitted.1 with rfl
    rcases permitted.2 with rfl
    by_cases zero : value = 0#32 <;>
      simp [next, zero, increment, CIL.Safety.SegmentContract.continuing,
        scalarState, duplicated, SegmentState.exact, Nat.add_assoc]
  next =>
    intro actual before exit permitted satisfied framed
    rcases permitted.1 with rfl
    rcases permitted.2 with rfl
    by_cases zero : value = 0#32
    all_goals
      simp [next, zero, Nat.add_assoc] at satisfied framed
      cases exit with
      | reaches pc after =>
        rcases satisfied.1 with rfl
        rcases satisfied.2.2 with rfl
        exact And.intro (Confined.refl [] memory) (by
          simp [branchIncrement, zero, scalarState, duplicated])
      | returns memory values => exact False.elim satisfied
      | faults fault => exact False.elim satisfied
      | diverges => exact False.elim satisfied

#print axioms branch_composition

/-- Duplicating the scalar before the branch composes with both validated successor summaries. -/
theorem duplicate_branch {program : CIL.Program} {method start : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (placed : CodeAt body start
      [.dup, .brfalse (start + 4), .ldc_i4 1, .add, .ldc_i4 1, .add])
    (arguments : List Value) (frame : Frame) (memory : Memory) (value : CIL.W32) :
    ({ branchIncrement start arguments frame memory value with
        pre := (scalarState frame memory value).exact arguments } :
      CIL.Safety.SegmentContract).Holds program method start := by
  have duplicate : Segment program method start (start + 1)
      ((scalarState frame memory value).exact arguments)
      ((duplicated frame memory value).exact arguments) := by
    dsimp only [scalarState, duplicated]
    cil_segment 1 [found, placed]
  have head := duplicate.contract (by omega) (footprint := fun _ _ => []) (by
    intro actual before after permitted satisfied
    rcases permitted.1 with rfl
    rcases permitted.2 with rfl
    rcases satisfied.2 with rfl
    exact Confined.refl [] memory)
  let next := fun pc => if pc = start + 1 then
    branchIncrement start arguments frame memory value else
    CIL.Safety.SegmentContract.unreachable
  apply head.seq (next := next)
  next =>
    intro pc
    by_cases equal : pc = start + 1
    next =>
      subst pc
      simpa [next] using branch_composition found placed arguments frame memory value
    next =>
      simpa [next, equal] using
        CIL.Safety.SegmentContract.unreachable_holds program method pc
  next =>
    intro actual before permitted
    exact permitted
  next =>
    intro actual before pc after _ satisfied
    rcases satisfied.1 with rfl
    have satisfied := satisfied.2
    simpa [next, branchIncrement] using satisfied
  next =>
    intro actual before exit _ stopped satisfied
    cases exit <;> simp_all [CIL.Safety.SegmentContract.continuing]
  next =>
    intro actual before pc after exit permitted satisfied _ post framed
    rcases permitted.1 with rfl
    rcases permitted.2 with rfl
    rcases satisfied.1 with rfl
    rcases satisfied.2.2 with rfl
    simpa only [next, ite_eq_left rfl, branchIncrement, scalarState, duplicated,
      SegmentExit.Confined] using (And.intro framed post)

#print axioms duplicate_branch

namespace StoredReturn

/-- One writable caller allocation whose four bytes initially contain zero. -/
def initial : Memory where
  allocations := fun index => if index = 0 then
    some { kind := .callerStack, layout := { size := 4, alignment := 1 } } else none
  cells := fun _ _ => { bits := 0, initialized := true }
  views := [{ allocation := 0, start := 0, length := 4, readable := true, writable := true }]
  nextIdentity := 1

/-- The byte home used by the store. -/
def home : Reference := { allocation := 0, offset := 0 }

/-- The store writes one to the first byte and keeps the other three bytes zero. -/
def finalMemory : Memory :=
  match write initial home [1, 0, 0, 0] 1 with
  | .ok memory => memory
  | .error _ => initial

/-- The store succeeds against the caller's writable home. -/
theorem written : write initial home [1, 0, 0, 0] 1 = .ok finalMemory := by rfl
#print axioms written

/-- The store is confined to its four-byte footprint. -/
theorem confined : Confined [(home, 4)] initial finalMemory :=
  Confined.write written (by decide)
#print axioms confined

/-- The store changes an existing byte, so an empty footprint cannot describe it. -/
theorem not_empty : Not (Confined [] initial finalMemory) := by
  intro framed
  have same := framed.cells 0 (by decide) 0 (by simp [Outside])
  have bits := congrArg Cell.bits same
  change (1 : BitVec 8) = 0 at bits
  contradiction
#print axioms not_empty

/-- The frame exposes caller storage as a local without owning its allocation. -/
def frame : Frame := { activation := 1, locals := [.bytes .word32 home], owned := [] }

/-- A local store returns the caller allocation with its written byte. -/
def body : CIL.Method := { returnsValue := false, locals := [], code := [.stloc 0, .ret] }

/-- The boundary state supplies the scalar to store. -/
def before : SegmentState :=
  { frame := frame, stack := [.scalar (.i32 1)], memory := initial }

/-- The actual interpreter returns the modified memory. -/
theorem returned :
    run [body] 2 0 0 [] before.frame before.stack before.memory = .ok (finalMemory, []) := by
  rfl
#print axioms returned

/-- The returning store permits exactly its four-byte home and its actual return. -/
def contract : CIL.Safety.SegmentContract where
  pre := before.exact []
  footprint _ state := state.localFootprint body body.code
  post _ _ exit := exit = .returns finalMemory []

/-- The stored byte is retained in the contract's returned memory. -/
theorem holds : contract.Holds [body] 0 0 := by
  intro arguments state permitted
  rcases permitted.1 with rfl
  rcases permitted.2 with rfl
  exact Exists.intro (.returns finalMemory [])
    (And.intro (Exists.intro 2 returned) (And.intro confined rfl))

#print axioms holds

/-- A returning store cannot satisfy a contract that omits the written caller home. -/
theorem empty_footprint_refused :
    Not (({ contract with footprint := fun _ _ => [] } :
      CIL.Safety.SegmentContract).Holds [body] 0 0) := by
  intro holds
  cases holds [] before (And.intro rfl rfl)
  rename_i exit witness
  have framed := witness.2.1
  have post := witness.2.2
  change exit = .returns finalMemory [] at post
  subst exit
  exact not_empty framed

#print axioms empty_footprint_refused

/-- Sequence preserves a returning head's actual footprint when no successor is reachable. -/
theorem composed_return : contract.Holds [body] 0 0 := by
  apply holds.seq (next := fun _ => CIL.Safety.SegmentContract.unreachable)
  next => exact fun pc => CIL.Safety.SegmentContract.unreachable_holds [body] 0 pc
  next => exact fun _ _ permitted => permitted
  next => intro arguments state pc after _ post; cases post
  next => exact fun _ _ _ _ _ post framed => And.intro framed post
  next => intro arguments state pc after exit _ post; cases post

#print axioms composed_return

end StoredReturn

end Tests.SegmentContract
