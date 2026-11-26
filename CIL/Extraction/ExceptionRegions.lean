import CIL.Extraction.Generics

/-!
# Exception regions

The protected ranges and handlers of a method's exception clauses, in instruction indices, and
the structural rules a body with clauses must satisfy before it is admitted (ECMA-335 I.12.4.2
and II.19). `checkRegions` decides them on the decoded instructions: clauses are disjoint or
properly nested with inner clauses listed first, no instruction that leaves the activation sits
inside a region, control enters a region only at the first instruction of a protected range,
only `leave` exits one, `endfinally` ends only a finally handler, and no `leave` exits a finally
handler.

The clauses are sorted once and swept once against the instructions, so the check costs the
sort of the clauses plus a constant per instruction and branch target.
-/

namespace CIL.Extraction

/-- The protected range or the handler of the clause numbered `clause`, as the instruction
    indices `[start, stop)`. -/
structure ClauseRegion where
  start : Nat
  stop : Nat
  clause : Nat
  /-- The region is the handler, rather than the protected range. -/
  handler : Bool
  /-- The clause is a finally clause. -/
  isFinally : Bool
  deriving DecidableEq, Repr

/-- Whether `region` holds the instruction at `pc`. -/
def ClauseRegion.holds (region : ClauseRegion) (pc : Nat) : Bool :=
  region.start ≤ pc && pc < region.stop

/-- The two regions of every clause, numbered in list order. -/
def clauseRegions (handlers : List ExceptionClause) : List ClauseRegion :=
  handlers.zipIdx.flatMap fun (clause, index) =>
    [⟨clause.tryStart, clause.tryEnd, index, false, clause.isFinally⟩,
      ⟨clause.handlerStart, clause.handlerEnd, index, true, clause.isFinally⟩]

/-- The sweep order of regions keyed by start, stop and region number: an earlier start, then a
    later stop, then a later clause. Every region then follows the regions that contain it. -/
def regionOrder (first second : Nat × Nat × Nat) : Ordering :=
  (compare first.1 second.1).then <|
    (compare second.2.1 first.2.1).then (compare second.2.2 first.2.2)

/-- The regions of `handlers` in `regionOrder`. The key numbers each clause's two regions apart,
    so no region is dropped. -/
def sortedRegions (handlers : List ExceptionClause) : List ClauseRegion :=
  let sorted := (clauseRegions handlers).foldl
    (fun sorted region => sorted.insert
      (region.start, region.stop, 2 * region.clause + if region.handler then 1 else 0) region)
    (∅ : Std.TreeMap (Nat × Nat × Nat) ClauseRegion regionOrder)
  sorted.toList.map Prod.snd

/-- Whether `inner`, which starts inside `outer`, nests in it: it ends inside it, its clause is
    listed first, and the two coincide only as the protected range two catch clauses share. -/
def ClauseRegion.nestsIn (inner outer : ClauseRegion) : Bool :=
  inner.stop ≤ outer.stop && inner.clause < outer.clause &&
    (inner.start != outer.start || inner.stop != outer.stop ||
      !inner.handler && !outer.handler && !inner.isFinally && !outer.isFinally)

/-- Whether the sorted `regions` are pairwise disjoint or nested, given the regions `enclosing`
    the previous start, innermost first. -/
def regionsNest : List ClauseRegion → List ClauseRegion → Bool
  | [], _ => true
  | region :: rest, enclosing =>
    let holding := enclosing.dropWhile (·.stop ≤ region.start)
    holding.head?.all region.nestsIn && regionsNest rest (region :: holding)

/-- The regions around one instruction. -/
structure RegionsAt where
  /-- The innermost region that holds the instruction. -/
  inner : Option ClauseRegion := none
  /-- The innermost region holding the instruction that a transfer cannot enter from outside it:
      the first one above the protected ranges that start at the instruction. -/
  entry : Option ClauseRegion := none
  /-- The innermost finally handler that holds the instruction. -/
  finallyHandler : Option ClauseRegion := none
  /-- Some handler holds the instruction. -/
  inHandler : Bool := false
  deriving Repr

/-- An open region of the sweep, with the finally handler and handler facts of its nesting. -/
private structure OpenRegion where
  region : ClauseRegion
  finallyHandler : Option ClauseRegion
  inHandler : Bool

/-- Open `region` inside the regions `enclosing` it, innermost first. -/
private def OpenRegion.inside (enclosing : List OpenRegion) (region : ClauseRegion) :
    OpenRegion :=
  { region,
    finallyHandler := if region.handler && region.isFinally then some region
      else enclosing.head?.bind (·.finallyHandler),
    inHandler := region.handler || enclosing.head?.any (·.inHandler) }

/-- The first of the open regions, innermost first, that is not a protected range starting at
    `pc`. -/
private def entryRegion (pc : Nat) : List OpenRegion → Option ClauseRegion
  | [] => none
  | top :: rest =>
    if top.region.start == pc && !top.region.handler then entryRegion pc rest
    else some top.region

/-- Open the regions of `pending`, sorted outer first, that start at `pc`. -/
private def openAt (pc : Nat) :
    List ClauseRegion → List OpenRegion → List ClauseRegion × List OpenRegion
  | region :: rest, enclosing =>
    if region.start == pc then openAt pc rest (OpenRegion.inside enclosing region :: enclosing)
    else (region :: rest, enclosing)
  | [], enclosing => ([], enclosing)

/-- Append the regions around each of `count` instructions from `pc` to `table`, opening the
    sorted `pending` regions as the sweep reaches them. -/
private def regionsFrom : Nat → Nat → List ClauseRegion → List OpenRegion → Array RegionsAt →
    Array RegionsAt
  | 0, _, _, _, table => table
  | count + 1, pc, pending, enclosing, table =>
    let (pending, enclosing) := openAt pc pending (enclosing.dropWhile (·.region.stop ≤ pc))
    let top := enclosing.head?
    regionsFrom count (pc + 1) pending enclosing (table.push
      { inner := top.map (·.region), entry := entryRegion pc enclosing,
        finallyHandler := top.bind (·.finallyHandler), inHandler := top.any (·.inHandler) })

/-- Why a body's exception regions are refused. -/
inductive RegionError where
  /-- Two clauses overlap without nesting, share a region other than the protected range of
      two catches, or an enclosing clause is listed before the clause it encloses. -/
  | misnested
  /-- The instruction at the index leaves the activation inside a region (`ret`, `jmp`,
      `tail.`), or allocates frame storage inside a handler (`localloc`). -/
  | forbidden (index : Nat)
  /-- A branch or fall-through from the instruction at the index exits a region other than by
      `leave`, or enters one other than at the first instruction of a protected range. -/
  | crossesRegion (index : Nat)
  /-- An `endfinally` at the index lies outside the handler of a finally clause. -/
  | endsOutsideFinally (index : Nat)
  /-- A `leave` at the index exits the handler of a finally clause. -/
  | leavesFinally (index : Nat)
  deriving DecidableEq, Repr

/-- Raw opcodes after which control never reaches the next instruction: `jmp`, `ret`, `br`,
    `br.s`, `throw`, `endfinally`, `leave`, `leave.s`, `endfilter` and `rethrow`. -/
def endsFlow (opcode : Nat) : Bool :=
  opcode ∈ [39, 42, 43, 56, 122, 220, 221, 222, 0xFE11, 0xFE1A]

/-- Raw opcodes that leave the activation: `jmp`, `ret` and the `tail.` prefix. -/
private def leavesActivation (opcode : Nat) : Bool := opcode ∈ [39, 42, 0xFE14]

/-- The raw opcode of `localloc`. -/
private def localAllocation : Nat := 0xFE0F

/-- The raw opcode of `endfinally`. -/
private def endFinallyOpcode : Nat := 220

/-- Whether the raw opcode is `leave` or `leave.s`. -/
def leaveOpcode (opcode : Nat) : Bool := opcode == 221 || opcode == 222

/-- The regions the sweep recorded at `pc`, or none past the code. -/
private def regionsAt (table : Array RegionsAt) (pc : Nat) : RegionsAt := table[pc]?.getD {}

/-- A transfer from `pc` to `target` enters only protected ranges that start at `target`. -/
private def entersAtTry (table : Array RegionsAt) (pc target : Nat) : Bool :=
  (regionsAt table target).entry.all (·.holds pc)

/-- A transfer from `pc` to `target` exits no region. -/
private def staysIn (table : Array RegionsAt) (pc target : Nat) : Bool :=
  (regionsAt table pc).inner.all (·.holds target)

/-- The region rule the instruction at `pc` of a body of `count` instructions breaks, if any. -/
private def instructionRegionError (table : Array RegionsAt) (count pc : Nat)
    (instruction : RawInstruction) : Option RegionError :=
  let here := regionsAt table pc
  let leave := leaveOpcode instruction.opcode
  let targets := match instruction.operand with
    | .target target => [target]
    | .targets targets => targets
    | _ => []
  let branches := targets.all fun target =>
    entersAtTry table pc target && (leave || staysIn table pc target)
  -- Falling off the last instruction of the code is the flow check's to refuse.
  let falls := endsFlow instruction.opcode ||
    if pc + 1 < count then entersAtTry table pc (pc + 1) && staysIn table pc (pc + 1)
    else here.inner.isNone
  if here.inner.isSome && leavesActivation instruction.opcode ||
      here.inHandler && instruction.opcode == localAllocation then some (.forbidden pc)
  else if instruction.opcode == endFinallyOpcode &&
      !here.inner.any (fun region => region.handler && region.isFinally) then
    some (.endsOutsideFinally pc)
  else if leave && targets.any (fun target => here.finallyHandler.any (!·.holds target)) then
    some (.leavesFinally pc)
  else if !branches || !falls then some (.crossesRegion pc)
  else none

/-- The regions around every instruction of `code` for clauses that pass `regionsNest`. -/
def regionTable (code : List RawInstruction) (handlers : List ExceptionClause) :
    Array RegionsAt :=
  regionsFrom code.length 0 (sortedRegions handlers) [] #[]

/-- The structural rules for the exception clauses `handlers` of `code`, whose ranges are
    nonempty, disjoint within each clause, and bounded by the code. A body without clauses
    passes. -/
def checkRegions (code : List RawInstruction) (handlers : List ExceptionClause) :
    Except RegionError Unit := do
  if handlers.isEmpty then return ()
  unless regionsNest (sortedRegions handlers) [] do
    throw .misnested
  let table := regionTable code handlers
  match code.zipIdx.findSome? fun (instruction, pc) =>
      instructionRegionError table code.length pc instruction with
  | some error => throw error
  | none => return ()

end CIL.Extraction
