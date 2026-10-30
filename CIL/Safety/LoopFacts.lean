import CIL.Safety.SymbolicExecution
import CIL.Safety.NumericLocals

/-!
# Loop facts from the proof context

The facts a loop proof's context already determines, gathered for the loop stepping tactics in
`CIL.Safety.LoopAutomation`: the definitions `bind_entry` and `bind_cutpoint` generated in
scope, hypotheses that state checked steps, loads, stores and span checks, and the facts that
follow from checked spans, numeric entry homes and entry memory. Hypotheses are selected by the
head of their type, so a context of unrelated hypotheses adds nothing to simp.
-/

namespace CIL.Safety

/-- Heads of the equations the loop tactics take from the context: checked steps, local and
    memory loads and stores, and span element, slice, validity, width and mode checks. -/
def loopFactHeads : List Lean.Name :=
  [``CIL.Safety.step, ``CIL.Safety.instruction, ``CIL.Safety.memoryInstruction,
    ``CIL.Safety.staticInstruction, ``CIL.Safety.loadLocal, ``CIL.Safety.storeLocal,
    ``CIL.Safety.loadValue, ``CIL.Safety.storeValue, ``CIL.Safety.SpanView.element,
    ``CIL.Safety.SpanView.slice, ``CIL.Safety.SpanView.validate, ``CIL.Safety.SpanView.width,
    ``CIL.Safety.SpanView.writable]

open Lean Meta in
/-- For an equation, possibly quantified, whose left side has a head in `loopFactHeads`, or a
    conjunction of such equations: the free variables of its left and of its right sides. -/
partial def loopFactSides? (type : Expr) : MetaM (Option (Array FVarId × Array FVarId)) :=
  forallTelescope type fun bound body => do
    let outer (e : Expr) := (collectFVars {} e).fvarIds.filter fun id => !bound.contains (.fvar id)
    let body := body.consumeMData
    if body.isAppOfArity ``And 2 then
      let some (leftL, leftR) ← loopFactSides? body.appFn!.appArg! | return none
      let some (rightL, rightR) ← loopFactSides? body.appArg! | return none
      return some (leftL ++ rightL, leftR ++ rightR)
    let some (_, lhs, rhs) := body.eq? | return none
    unless lhs.getAppFn.constName?.any loopFactHeads.contains do return none
    return some (outer lhs, outer rhs)

open Lean Meta in
/-- The memories the left sides of a `loopFactSides?` fact read: their arguments of type `Memory`
    that do not depend on its quantifiers. -/
partial def loopFactMemories (type : Expr) : MetaM (Array Expr) :=
  forallTelescope type fun bound body => do
    let body := body.consumeMData
    if body.isAppOfArity ``And 2 then
      return (← loopFactMemories body.appFn!.appArg!) ++ (← loopFactMemories body.appArg!)
    let some (_, lhs, _) := body.eq? | return #[]
    lhs.getAppArgs.filterM fun argument => do
      if argument.hasAnyFVar (bound.contains <| .fvar ·) then return false
      return (← instantiateMVars (← inferType argument)).isConstOf ``Memory

open Lean Elab Tactic Meta in
/-- The declarations in scope with `cil_loop_unfold`, sorted by name: the loop states, entry
    frames and slot facts that `bind_cutpoint` and `bind_entry` generated for this proof. -/
def loopUnfoldNames : TacticM (Array Name) := do
  let some extension ← getSimpExtension? `cil_loop_unfold | return #[]
  let theorems ← extension.getTheorems
  let equations := theorems.toUnfoldThms.foldl (fun found _ names => found ++ names) #[]
  let mut names := theorems.toUnfold.fold (·.push ·) #[]
  names := theorems.toUnfoldThms.foldl (fun found name _ => found.push name) names
  names := theorems.lemmaNames.fold (init := names) fun found origin => match origin with
    | .decl name .. => if equations.contains name then found else found.push name
    | _ => found
  let kept := names.filter fun name => !theorems.erased.contains (.decl name)
  return kept.toList.eraseDups.toArray.qsort Name.lt

open Lean Elab Tactic Meta in
/-- The `cil_loop_unfold` declarations a goal can meet: each theorem, and each definition that
    `seed` names or that the value of an included definition names. -/
def reachableLoopUnfolds (seed : Array Lean.Name) : TacticM (Array Lean.Name) := do
  let registered ← loopUnfoldNames
  let mut included : Array Lean.Name := #[]
  let mut mentioned : NameSet := seed.foldl (·.insert ·) {}
  let mut changed := true
  while changed do
    changed := false
    for name in registered do
      if included.contains name then continue
      let info ← getConstInfo name
      unless (← isProp info.type) || mentioned.contains name do continue
      included := included.push name
      changed := true
      if let some value := info.value? then
        mentioned := value.getUsedConstants.foldl (·.insert ·) mentioned
  return registered.filter included.contains

open Lean Elab Tactic Meta in
/-- Assert the proof `fact` elaborates to as a hygienic hypothesis named after `base`, returning
    it and its statement; nothing when it does not elaborate to a proof without metavariables or
    states one of `known`. -/
def assertLoopFact (base : Name) (fact : Term) (known : Array Expr) :
    TacticM (Option (Term × Expr)) := withMainContext do
  let saved ← saveState
  try
    let proof ← Term.withoutErrToSorry <| Term.elabTerm fact none
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    let type ← instantiateMVars (← inferType proof)
    if proof.hasMVar || type.hasMVar || !(← isProp type) || known.contains type then
      saved.restore
      return none
    let name ← mkFreshUserName base
    let (_, goal) ← (← (← getMainGoal).assert name type proof).intro1P
    replaceMainGoal [goal]
    return some (mkIdent name, type)
  catch _ =>
    saved.restore
    return none

open Lean Meta in
/-- Whether code that `program` reaches through definitions in its own root namespace, or
    through methods and programs, reads a method argument; true when `program` is not a
    constant. -/
def readsArguments (program : Expr) : MetaM Bool := do
  let some root := program.getAppFn.constName? | return true
  let code (type : Expr) : Bool := type.isConstOf ``CIL.Method || type.isConstOf ``CIL.Program
  let mut pending := #[root]
  let mut seen : NameSet := {}
  while let some name := pending.back? do
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some value := ((← getEnv).find? name).bind (·.value?) | continue
    for used in value.getUsedConstants do
      if used == ``CIL.Op.arg then return true
      if seen.contains used then continue
      let follow := used.getRoot == root.getRoot ||
        (((← getEnv).find? used).any fun info => code info.type)
      if follow then pending := pending.push used
  return false

/-- What a loop goal lets stepping read. -/
structure LoopGoalScope where
  /-- The terms whose variables stepping can meet. -/
  parts : Array Lean.Expr
  /-- The memories the goal's states hold, when every state reduces to a literal. -/
  memories : Option (Array Lean.Expr)
  /-- Whether the goal can be closed by returning from the method. -/
  returns : Bool

open Lean Meta in
/-- The scope of a loop goal: for `LoopReaches` or `LoopTerminates`, its states, any
    postcondition and, only when the program reads an argument, the arguments; for any other
    goal, all of it. -/
def loopGoalScope (target : Expr) : MetaM LoopGoalScope := do
  let arguments := target.getAppArgs
  let (states, post) :=
    if target.isAppOfArity `CIL.Safety.LoopReaches 5 then (#[arguments[3]!, arguments[4]!], #[])
    else if target.isAppOfArity `CIL.Safety.LoopTerminates 5 then
      (#[arguments[4]!], #[arguments[3]!])
    else (#[], #[])
  if states.isEmpty then return { parts := #[target], memories := none, returns := true }
  let read := if ← readsArguments arguments[0]! then #[arguments[2]!] else #[]
  let parts := states ++ post ++ read
  let returns := !post.isEmpty
  let mut memories := #[]
  for state in states do
    let state ← whnf state
    unless state.isAppOfArity `CIL.Safety.LoopState.mk 4 do
      return { parts, memories := none, returns }
    memories := memories.push (← whnfR state.appArg!)
  return { parts, memories := some memories, returns }

open Lean Elab Meta in
/-- The value a numeric home of `kind` reads back as when it holds `number`, given as a word's
    `toNat` or a literal; `none` for other kinds and numbers. -/
def homeValue? (kind number : Expr) : TermElabM (Option Term) := do
  let constructor := match (← whnfR kind).getAppFn.constName? with
    | some ``CIL.LocalKind.word64 => some ``CIL.Value.i64
    | some ``CIL.LocalKind.word32 | some ``CIL.LocalKind.narrow
    | some ``CIL.LocalKind.byte => some ``CIL.Value.i32
    | _ => none
  let some constructor := constructor | return none
  let number := (← instantiateMVars number).consumeMData
  let word : Option Term ← if number.isAppOfArity ``BitVec.toNat 2 then
      pure (some (← Term.exprToSyntax number.appArg!))
    else match number.nat? <|> number.rawNatLit? with
      | some literal => pure (some ⟨Syntax.mkNumLit (toString literal)⟩)
      | none => pure none
  let some word := word | return none
  return some (← `($(mkCIdent constructor) $word))

open Lean Meta in
/-- Whether `type` mentions `numericOfWidth` at a literal width, which unfolds to one value. -/
def loadsAtLiteralWidth (type : Expr) : Bool :=
  (type.find? fun e => e.isAppOfArity `CIL.Safety.numericOfWidth 2 &&
    (e.appFn!.appArg!.nat? <|> e.appFn!.appArg!.rawNatLit?).isSome).isSome

open Lean Elab Tactic Meta in
/-- `facts`, followed by the facts a loop proof's context determines, each at most once:
    * the declarations in scope with `cil_loop_unfold` that `reachableLoopUnfolds` finds from
      the goal and the facts;
    * hypotheses `loopFactSides?` recognizes;
    * for `span : CheckedSpan`, `span.facts`, `span.length_nil` or `span.length_cons` when its
      values are `[]` or a cons, and `(span.within wellFormed frame).facts` for each
      `frame : EntryMemory` from its memory with that memory's `wellFormed` in context;
    * for `contents : SpanContents`, `contents.elementWidth`;
    * for `home : NumericEntryHome`, its load when its number is a word's `toNat` or a literal,
      with `localResult`;
    * for `frame : EntryMemory` and the entry's `setup` equation, `frame.leave setup` when the
      goal can return;
    * `numericOfWidth` and `BitVec.ofNat_toNat` when a gathered fact loads at a literal width.
    Only hypotheses reachable by name are read, so shadowed and hygienic ones are skipped. A
    fact is kept only when the goal reaches every variable it is about: those of the scope
    `loopGoalScope` gives and of the explicit facts, then the right side of each kept equation;
    a derived fact must be about variables reached without an equation. An equation is kept only
    at a memory that a state of the goal holds or a kept equation or explicit fact mentions, and
    a derived fact only at a state's memory. Derived facts are asserted as hygienic hypotheses,
    skipping any statement already gathered. -/
def gatherLoopFacts (facts : Array Term) : TacticM (Array Term) := withMainContext do
  let context ← getLCtx
  let explicitNames ← facts.filterMapM fun fact => do
    unless fact.raw.isIdent do return none
    if (context.findFromUserName? fact.raw.getId).isSome then return some fact.raw.getId
    try return some (← resolveGlobalConstNoOverload fact.raw) catch _ => return none
  let mut gathered : Array Term := #[]
  let target ← instantiateMVars (← getMainTarget)
  let mut constants := target.getUsedConstants
  for name in explicitNames do
    if let some value := ((← getEnv).find? name).bind (·.value?) then
      constants := constants ++ value.getUsedConstants
  let mut typed : Array (LocalDecl × Expr) := #[]
  for declaration in context do
    if declaration.isImplementationDetail || declaration.userName.hasMacroScopes then continue
    unless (context.findFromUserName? declaration.userName).any
      (·.fvarId == declaration.fvarId) do continue
    let type ← instantiateMVars declaration.type
    if ← isProp type then typed := typed.push (declaration, type.consumeMData)
  let variables (terms : Array Expr) : Array FVarId :=
    (terms.foldl (fun found term => collectFVars found term) {}).fvarIds
  let named (declaration : LocalDecl) : Term := mkIdent declaration.userName
  -- Hygienic constant names make every step's simp measurably slower than `_root_` names.
  let global (name : Lean.Name) : Term := mkIdent (`_root_ ++ name)
  -- Lemmas are named canonically: they live in modules this one does not import.
  let applied (name : Lean.Name) (arguments : Array Term) : Term :=
    Syntax.mkApp (mkCIdent (`CIL.Safety ++ name)) arguments
  -- Each candidate: its base name, term, the variables it is about, the memories it reads
  -- and the variables it produces.
  let mut candidates :
    Array (Lean.Name × Term × Array FVarId × Array Expr × Array FVarId) := #[]
  let scope ← loopGoalScope target
  -- Facts at a memory no state holds, nor a kept step produces, describe memory no step reads.
  let isLive (memory : Expr) : Bool := scope.memories.all (·.contains memory)
  let mut live := scope.memories
  let asTerms (ids : Array FVarId) : Array Expr := ids.map .fvar
  let mut reached := variables scope.parts
  let mut known : Array Expr := #[]
  for (declaration, type) in typed do
    let fact := named declaration
    if explicitNames.contains declaration.userName then
      reached := reached ++ variables #[type]
      live := live.map (· ++ asTerms (variables #[type]))
      known := known.push type
      constants := constants ++ type.getUsedConstants
    else if let some (subject, produced) ← loopFactSides? type then
      let memories ← loopFactMemories type
      candidates := candidates.push (.anonymous, fact, subject, memories, produced)
    let arguments := type.getAppArgs
    if type.isAppOfArity `CIL.Safety.CheckedSpan 5 then
      let subject := variables #[arguments[0]!, arguments[1]!]
      if isLive arguments[0]! then
        candidates := candidates.push
          (`spanFacts, applied `CheckedSpan.facts #[fact], subject, #[], #[])
      let values := type.appArg!.consumeMData
      if values.isAppOfArity ``List.nil 1 then
        candidates := candidates.push
          (`spanLength, applied `CheckedSpan.length_nil #[fact], subject, #[], #[])
      else if values.isAppOfArity ``List.cons 3 then
        candidates := candidates.push
          (`spanLength, applied `CheckedSpan.length_cons #[fact], subject, #[], #[])
      for (frame, frameType) in typed do
        unless frameType.isAppOfArity ``EntryMemory 2 && frameType.getArg! 0 == arguments[0]! &&
          isLive (frameType.getArg! 1) do continue
        for (formed, formedType) in typed do
          unless formedType.isAppOfArity ``Memory.WellFormed 1 &&
            formedType.appArg! == arguments[0]! do continue
          let within := applied `CheckedSpan.within #[fact, named formed, named frame]
          candidates := candidates.push (`spanFacts,
            applied `CheckedSpan.facts #[← `(($within))],
            variables #[frameType.getArg! 1, arguments[1]!], #[], #[])
    else if type.isAppOfArity `CIL.Safety.SpanContents 4 then
      candidates := candidates.push (`elementWidth, applied `SpanContents.elementWidth #[fact],
        variables #[arguments[1]!], #[], #[])
    else if type.isAppOfArity ``NumericEntryHome 5 && isLive arguments[1]! then
      if let some value ← homeValue? arguments[2]! arguments[3]! then
        let load := mkCIdent `CIL.Safety.NumericEntryHome.load
        candidates := candidates.push (`homeLoad, ← `($load $fact (value := $value) rfl),
          variables #[arguments[1]!, arguments[4]!], #[], #[])
    else if type.isAppOfArity ``EntryMemory 2 && scope.returns && isLive arguments[1]! then
      for (setup, setupType) in typed do
        let some (_, entry, _) := setupType.eq? | continue
        unless entry.isAppOfArity ``enterFrame 3 && entry.appArg! == arguments[0]! do continue
        candidates := candidates.push (`frameLeave,
          applied `EntryMemory.leave #[named setup, fact], variables #[arguments[1]!], #[],
          #[])
  -- Kept equations extend what is reached; derived facts need what the goal itself names,
  -- since a value only a step produces may never reach the goal.
  let direct := reached
  let mut kept : Array Bool := candidates.map fun _ => false
  let mut changed := true
  while changed do
    changed := false
    for index in [:candidates.size] do
      let (base, _, subject, memories, produced) := candidates[index]!
      let visible := if base.isAnonymous then reached else direct
      if !kept[index]! && subject.all visible.contains &&
          memories.all fun memory => live.all (·.contains memory) then
        kept := kept.set! index true
        reached := reached ++ produced
        live := live.map (· ++ asTerms produced)
        changed := changed || !produced.isEmpty
  let mut literalWidth := false
  let mut homeLoads := false
  for ((base, fact, _, _, _), keep) in candidates.zip kept do
    unless keep && base.isAnonymous do continue
    gathered := gathered.push fact
    if let some declaration := context.findFromUserName? fact.raw.getId then
      let type ← instantiateMVars declaration.type
      literalWidth := literalWidth || loadsAtLiteralWidth type
      constants := constants ++ type.getUsedConstants
      known := known.push type.consumeMData
  for ((base, fact, _, _, _), keep) in candidates.zip kept do
    unless keep && !base.isAnonymous do continue
    if let some (asserted, type) ← assertLoopFact base fact known then
      gathered := gathered.push asserted
      known := known.push type
      homeLoads := homeLoads || base == `homeLoad
  if homeLoads && !explicitNames.contains ``localResult then
    gathered := gathered.push (global ``localResult)
  if literalWidth then
    for name in [`CIL.Safety.numericOfWidth, ``BitVec.ofNat_toNat] do
      unless explicitNames.contains name do gathered := gathered.push (global name)
  let unfolds ← reachableLoopUnfolds constants
  let unfolds := unfolds.filter (!explicitNames.contains ·)
  return facts ++ unfolds.map global ++ gathered

end CIL.Safety
