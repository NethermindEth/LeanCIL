import CIL.Safety.Execution

/-!
# Steps that leave protected ranges and finally handlers

`leave` and `endfinally` change only the pending resumptions of the running frame: they keep
memory, push nothing, and continue at a pc or raise a recorded exception again. In a body without
exception clauses `leave` is a jump and `endfinally` is an invalid state. Whole-run invariants
proved by induction on successful runs take `HandlerFree`, which `handler_free` discharges.
-/

/-- Whether `op` reads the exception clauses of its body to choose where it continues: `leave` and
    `endfinally`. -/
def CIL.Instruction.readsClauses : CIL.Instruction → Bool
  | .leave _ | .endfinally => true
  | _ => false

namespace CIL.Safety

/-- `action` continues in `frame` with other pending resumptions and the same `memory`: at a pc
    with an empty stack, or raising a recorded exception again. -/
def FrameAction.Resumes (frame : Frame) (memory : Memory) (action : FrameAction) : Prop :=
  ∃ resumptions : List (Nat × Resumption),
    (∃ target, action = .next target [] { frame with resumptions } memory) ∨
    (∃ location object, action = .raise location object { frame with resumptions } memory)

/-- A `leave` continues in its frame and memory with only its resumptions changed. -/
theorem leaveFrom_resumes (body : CIL.Method) (pc target : Nat) (frame : Frame)
    (memory : Memory) : (leaveFrom body pc target frame memory).Resumes frame memory := by
  unfold leaveFrom
  split
  · exact ⟨frame.resumptions, .inl ⟨target, rfl⟩⟩
  · exact ⟨_, .inl ⟨_, rfl⟩⟩

#print axioms leaveFrom_resumes

/-- A successful `leave` step changes only the resumptions of its frame. -/
theorem leaveStep_resumes {body : CIL.Method} {pc target : Nat} {frame : Frame}
    {memory : Memory} {action : FrameAction}
    (stepped : leaveStep body pc target frame memory = .ok action) :
    action.Resumes frame memory := by
  unfold leaveStep at stepped
  split at stepped
  · cases stepped
  · cases stepped
    exact leaveFrom_resumes _ _ _ _ _

#print axioms leaveStep_resumes

/-- A successful `endfinally` step changes only the resumptions of its frame. -/
theorem endFinallyStep_resumes {body : CIL.Method} {pc : Nat} {frame : Frame}
    {memory : Memory} {action : FrameAction}
    (stepped : endFinallyStep body pc frame memory = .ok action) :
    action.Resumes frame memory := by
  unfold endFinallyStep at stepped
  split at stepped
  · split at stepped
    · cases stepped
    · split at stepped
      · cases stepped
        exact leaveFrom_resumes _ _ _ _ _
      · cases stepped
        exact ⟨_, .inr ⟨_, _, rfl⟩⟩
  · cases stepped

#print axioms endFinallyStep_resumes

/-- In a body without exception clauses `leave` jumps to its target with an empty stack. -/
theorem leaveStep_of_handlers_nil {body : CIL.Method} (empty : body.handlers = [])
    (pc target : Nat) (frame : Frame) (memory : Memory) :
    leaveStep body pc target frame memory = .ok (.next target [] frame memory) := by
  simp [leaveStep, leaveFrom, findClause, empty]

#print axioms leaveStep_of_handlers_nil

/-- In a body without exception clauses no finally handler runs, so `endfinally` is an invalid
    state. -/
theorem endFinallyStep_of_handlers_nil {body : CIL.Method} (empty : body.handlers = [])
    (pc : Nat) (frame : Frame) (memory : Memory) :
    endFinallyStep body pc frame memory = .error .invalidState := by
  simp [endFinallyStep, findClause, empty]

#print axioms endFinallyStep_of_handlers_nil

/-- In a body without exception clauses `leave` steps to its target with an empty stack. -/
theorem step_leave_of_handlers_nil {body : CIL.Method} (empty : body.handlers = [])
    (target pc : Nat) (args : List Value) (frame : Frame) (stack : List Value)
    (memory : Memory) :
    step body (.leave target) pc args frame stack memory = .ok (.next target [] frame memory) := by
  rw [← leaveStep_of_handlers_nil empty pc target frame memory]
  rfl

#print axioms step_leave_of_handlers_nil

/-- In a body without exception clauses `endfinally` is an invalid state. -/
theorem step_endfinally_of_handlers_nil {body : CIL.Method} (empty : body.handlers = [])
    (pc : Nat) (args : List Value) (frame : Frame) (stack : List Value) (memory : Memory) :
    step body .endfinally pc args frame stack memory = .error .invalidState := by
  rw [← endFinallyStep_of_handlers_nil empty pc frame memory]
  rfl

#print axioms step_endfinally_of_handlers_nil

/-- A pc of a method whose body has no exception clauses is unprotected. -/
theorem unprotected_of_handlers_nil {program : CIL.Program} {method : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (empty : body.handlers = []) (pc : Nat) :
    (program[method]?).all (·.unprotectedAt pc) = true := by
  simp [found, CIL.Method.unprotectedAt, empty]

#print axioms unprotected_of_handlers_nil

/-- A pc of a method a program does not have is unprotected. -/
theorem unprotected_of_none {program : CIL.Program} {method : Nat}
    (missing : program[method]? = none) (pc : Nat) :
    (program[method]?).all (·.unprotectedAt pc) = true := by
  simp [missing]

#print axioms unprotected_of_none

/-- Only `endfinally` raises a recorded exception again, so no step of a body without exception
    clauses produces a `raise`. -/
theorem step_ne_raise {body : CIL.Method} {operation : CIL.Instruction} {pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory}
    {location : LocatedFault} {object : Option Reference} {raised : Frame} {after : Memory}
    (empty : body.handlers = [])
    (h : step body operation pc args frame stack m = .ok (.raise location object raised after)) :
    False := by
  unfold step referenceCompareCall referenceSubtractCall newobjStep
    constructAggregate constructObject modelStep observedCall runModel featureCall
    typedTransferCall skipInitCall initializeSpanHome spanInPlaceCall at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals repeat' first
    | (cases h; done)
    | (rw [leaveStep_of_handlers_nil empty] at h; cases h; done)
    | (rw [endFinallyStep_of_handlers_nil empty] at h; cases h; done)
    | unfold calliStep at h
    | unfold returnFrom at h
    | unfold localAllocation at h
    | unfold initializeSpanHome at h
    | unfold intrinsicCall at h
    | unfold referenceCompareCall at h
    | unfold referenceSubtractCall at h
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    | split at h

#print axioms step_ne_raise

/-- Replacing a method of a program without exception clauses by a body without them keeps the
    program free of them. -/
theorem HandlerFree.set {program : CIL.Program} (free : HandlerFree program) {body : CIL.Method}
    (empty : body.handlers = []) (index : Nat) : HandlerFree (program.set index body) := by
  intro candidate member
  rcases List.mem_or_eq_of_mem_set member with inside | rfl
  · exact free candidate inside
  · exact empty

#print axioms HandlerFree.set

/-- A run whose located outcome is a success succeeded at the level of stopped states. -/
theorem runFaulting_of_run_ok {program : CIL.Program} {fuel method pc : Nat} {args : List Value}
    {frame : Frame} {stack : List Value} {memory : Memory} {result : Memory × List Value}
    (ran : run program fuel method pc args frame stack memory = .ok result) :
    runFaulting (program[·]?) fuel method pc args frame stack memory = .ok result := by
  unfold run runWith at ran
  cases faulting : runFaulting (program[·]?) fuel method pc args frame stack memory <;>
    simp only [faulting, Except.mapError] at ran <;> cases ran <;> rfl

#print axioms runFaulting_of_run_ok

/-- A program whose every method has an empty clause list is handler-free; a concrete program
    discharges the check by evaluation. -/
theorem HandlerFree.of_all {program : CIL.Program}
    (checked : program.all (·.handlers.isEmpty) = true) : HandlerFree program := by
  intro body member
  exact List.isEmpty_iff.mp (List.all_eq_true.mp checked body member)

#print axioms HandlerFree.of_all

/-- Proves `HandlerFree program` from a hypothesis in scope or, for a concrete program, by
    evaluating its clause lists. -/
macro "handler_free" : tactic =>
  `(tactic| first | assumption | exact CIL.Safety.HandlerFree.of_all (by rfl))

end CIL.Safety
