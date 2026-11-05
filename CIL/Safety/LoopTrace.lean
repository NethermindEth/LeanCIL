import Lean
import CIL.DebugNames

/-!
# Loop step trace

The trace class `CIL.loop`: with `set_option trace.CIL.loop true`, each instruction a loop
tactic takes reports its pc, instruction and source location, the lemma applied, the hypotheses
its proof used, the parts of the state it changed and the goals left by obligation tag. Every
line is read from the step's proof term and goals, so a fact appears only when the proof used
it. With the option unset nothing is built or printed.
-/

namespace CIL.Safety

open Lean Elab Tactic Meta

initialize registerTraceClass `CIL.loop

/-- The facts a step's trace explains by their statement's head, with what each says. A name
    here is checked against the environment by `Tests.LoopDiagnostics`. -/
def loopFactMeanings : List (Name × String) := [
  (`CIL.Safety.SpanApart, "the footprints are disjoint"),
  (`CIL.Safety.Writable, "the range is writable"),
  (`CIL.Safety.Filled, "the buffer's contents are known"),
  (`CIL.Safety.CheckedSpan, "the span is valid at this memory")]

/-- What a hypothesis says, named by the head of its statement, when `loopFactMeanings` has it. -/
def loopFactMeaning? (statement : Expr) : Option String := do
  let head ← statement.consumeMData.getAppFn.constName?
  (loopFactMeanings.lookup head)

/-- The source line of `pc` in `method` from `ExtractedSymbols`, or why there is none. -/
def loopSourceOf (method pc : Option Nat) : MetaM String := do
  let (some method, some pc) := (method, pc) | return "unknown, since the pc is not a literal"
  match ← CIL.DebugNames.entries CIL.DebugNames.Point `points method with
  | none => return "unknown, since the proof does not import ExtractedSymbols"
  | some _ =>
    let found ← CIL.DebugNames.location? method pc
    return found.getD "unknown, since no sequence point precedes this pc"

/-- The hypotheses of `goal`'s context that its assigned proof mentions: the facts a step used. -/
def loopUsedFacts (goal : MVarId) : MetaM (Array LocalDecl) := goal.withContext do
  let proof ← instantiateMVars (mkMVar goal)
  let mut used := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    unless ← isProp decl.type do continue
    if proof.containsFVar decl.fvarId then used := used.push decl
  return used

/-- The parts of a loop state, named by `names`, that differ between `before` and `after`;
    a literal list part is compared entry by entry. -/
def loopChanges (names : Array String) (before after : Array Expr) :
    MetaM (Array MessageData) := do
  let mut changes := #[]
  for index in [:min names.size (min before.size after.size)] do
    let old ← instantiateMVars before[index]!
    let new ← instantiateMVars after[index]!
    if old == new then continue
    let name := names[index]!
    match old.listLit?, new.listLit? with
    | some (_, olds), some (_, news) =>
      let (olds, news) := (olds.toArray, news.toArray)
      if olds.size == news.size then
        for slot in [:olds.size] do
          unless olds[slot]! == news[slot]! do
            changes := changes.push m!"{name} {slot}: {olds[slot]!} ⟶ {news[slot]!}"
      else changes := changes.push m!"{name}: {old} ⟶ {new}"
    | _, _ => changes := changes.push m!"{name}: {old} ⟶ {new}"
  return changes

/-- The goals open now, each by its tag, or `main` for an untagged goal. -/
def loopGoalsLeft : TacticM MessageData := do
  let goals ← getGoals
  if goals.isEmpty then return m!"none"
  let tags ← goals.mapM fun goal => do
    let tag := (← goal.getTag).eraseMacroScopes
    return if tag.isAnonymous then "main" else tag.toString
  return MessageData.joinSep (tags.map toMessageData) ", "

end CIL.Safety
