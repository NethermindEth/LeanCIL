import CIL.Safety.AggregateMemorySteps
import CIL.Safety.SymbolicExecution

/-!
# Aggregate operation facts

Checked aggregate steps consume byte or snapshot operations. Unknown bytes retain their flags;
access authority, an old snapshot and a mismatched width cannot supply the missing contents.
-/

namespace Tests.AggregateMemorySteps
open CIL.Safety

/-- Initialized bytes load as an ordinary aggregate. -/
theorem initialized_load {memory : Memory} {source : Reference} {width : Nat}
    {bytes : List (BitVec 8)} (loaded : read memory source width 1 = .ok bytes)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.loadAggregate width) pc args frame (.reference (.address source) :: rest)
      memory = .ok (.next (pc + 1) (.scalar (.aggregate bytes) :: rest) frame memory) := by
  cil_checked_step [loaded]
#print axioms initialized_load

/-- Readonly loads preserve the same initialized byte evidence. -/
theorem readonly_load {memory : Memory} {source : Reference} {width : Nat}
    {bytes : List (BitVec 8)} (loaded : read memory source width 1 = .ok bytes)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.loadAggregate width) pc args frame (.readOnlyReference (.address source) :: rest)
      memory = .ok (.next (pc + 1) (.scalar (.aggregate bytes) :: rest) frame memory) := by
  cil_checked_step [loaded]
#print axioms readonly_load

/-- A read stated at a local kind's width, as a remembered aggregate local gives it, supplies
    the load at the numeral width the opcode carries. -/
theorem kind_width_load {memory : Memory} {source : Reference} {bytes : List (BitVec 8)}
    (loaded : read memory source (localWidth (.aggregate 32)) 1 = .ok bytes)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.loadAggregate 32) pc args frame (.reference (.address source) :: rest)
      memory = .ok (.next (pc + 1) (.scalar (.aggregate bytes) :: rest) frame memory) := by
  cil_checked_step [loaded]
#print axioms kind_width_load

/-- An unknown byte loads as a snapshot without becoming initialized. -/
theorem unknown_load {memory : Memory} {source : Reference}
    (loaded : readSnapshot memory source 1 1 = .ok [(0, false)])
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.loadAggregate 1) pc args frame (.reference (.address source) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.snapshot (.aggregate 1) [(0, false)]) :: rest)
        frame memory) := by
  cil_checked_step [loaded]
#print axioms unknown_load

/-- Readonly aggregate loads also retain an unknown byte's initialization flag. -/
theorem readonly_unknown_load {memory : Memory} {source : Reference}
    (loaded : readSnapshot memory source 1 1 = .ok [(0, false)])
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.loadAggregate 1) pc args frame (.readOnlyReference (.address source) :: rest)
      memory = .ok (.next (pc + 1)
        (.scalar (.snapshot (.aggregate 1) [(0, false)]) :: rest) frame memory) := by
  cil_checked_step [loaded]
#print axioms readonly_unknown_load

/-- A symbolic snapshot preserves all its flags when at least one byte is unknown. -/
theorem symbolic_unknown_load {memory : Memory} {source : Reference} {width : Nat}
    {bytes : List (BitVec 8 × Bool)} (loaded : readSnapshot memory source width 1 = .ok bytes)
    (unknown : bytes.all Prod.snd = false)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.loadAggregate width) pc args frame (.reference (.address source) :: rest)
      memory = .ok (.next (pc + 1) (.scalar (.snapshot (.aggregate width) bytes) :: rest)
        frame memory) := by
  cil_checked_step [loaded, unknown]
#print axioms symbolic_unknown_load

/-- A store uses the checked byte write and does not need old destination contents. -/
theorem initialized_store {memory after : Memory} {destination : Reference}
    {bytes : List (BitVec 8)} (written : write memory destination bytes 1 = .ok after)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.storeAggregate bytes.length) pc args frame
      (.scalar (.aggregate bytes) :: .reference (.address destination) :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  cil_checked_step [written]
#print axioms initialized_store

/-- Storing unknown bytes uses the snapshot write, which retains their initialization flags. -/
theorem unknown_store {memory after : Memory} {destination : Reference}
    (written : writeSnapshot memory destination [(0, false)] 1 = .ok after)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.storeAggregate 1) pc args frame
      (.scalar (.snapshot (.aggregate 1) [(0, false)]) ::
        .reference (.address destination) :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  cil_checked_step [written]
#print axioms unknown_store

/-- An unknown snapshot cannot be reported as an initialized aggregate. -/
theorem unknown_is_not_initialized {memory : Memory} {source : Reference}
    (loaded : readSnapshot memory source 1 1 = .ok [(0, false)])
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.loadAggregate 1) pc args frame (.reference (.address source) :: rest) memory ≠
      .ok (.next (pc + 1) (.scalar (.aggregate [0]) :: rest) frame memory) := by
  rw [unknown_load loaded]
  simp
#print axioms unknown_is_not_initialized

/-- A snapshot with the wrong shape width is rejected before its write operation. -/
theorem wrong_snapshot_width (memory : Memory) (destination : Reference)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.storeAggregate 1) pc args frame
      (.scalar (.snapshot (.aggregate 2) [(0, false)]) ::
        .reference (.address destination) :: rest) memory = .error .invalidState := by
  cil_checked_step []
#print axioms wrong_snapshot_width

/-- A null aggregate load preserves the requested width in its fault. -/
theorem null_load_width (memory : Memory) (body : CIL.Method) (pc : Nat) (args : List Value)
    (frame : Frame) (rest : List Value) :
    step body (.loadAggregate 8) pc args frame (.reference .null :: rest) memory =
      .error (.memory .nullDereference .null 8) := by
  cil_checked_step []
#print axioms null_load_width

/-- Read authority alone cannot prove any particular loaded aggregate. -/
theorem access_does_not_supply_contents (memory : Memory) (source : Reference)
    (_readable : access memory source 1 1 false = .ok ())
    (_body : CIL.Method) (_pc : Nat) (_args : List Value) (_frame : Frame) (_rest : List Value) :
    True := by
  fail_if_success
    have : step _body (.loadAggregate 1) _pc _args _frame
        (.reference (.address source) :: _rest) memory =
        .ok (.next (_pc + 1) (.scalar (.aggregate [0]) :: _rest) _frame memory) := by
      cil_checked_step [_readable]
  trivial
#print axioms access_does_not_supply_contents

end Tests.AggregateMemorySteps
