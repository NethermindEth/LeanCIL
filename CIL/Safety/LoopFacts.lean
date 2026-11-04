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
    memory loads and stores, span element, slice, validity, width and mode checks, formed
    references and `Unsafe.Add` results. -/
def loopFactHeads : List Lean.Name :=
  [``CIL.Safety.step, ``CIL.Safety.instruction, ``CIL.Safety.memoryInstruction,
    ``CIL.Safety.staticInstruction, ``CIL.Safety.loadLocal, ``CIL.Safety.storeLocal,
    ``CIL.Safety.loadValue, ``CIL.Safety.storeValue, ``CIL.Safety.SpanView.element,
    ``CIL.Safety.SpanView.slice, ``CIL.Safety.SpanView.validate, ``CIL.Safety.SpanView.width,
    ``CIL.Safety.SpanView.writable, ``CIL.Safety.form, ``CIL.Safety.add]

/-- The facts about caller storage that read only allocations, so a loop frame carries them from
    its caller's memory to its own (`CIL.Safety.LoopCallerFacts`), with the lemma that does. -/
def loopCallerFacts : List (Lean.Name × Lean.Name) :=
  [(``CIL.Safety.form, `LoopFrame.caller_form), (``CIL.Safety.add, `LoopFrame.caller_add),
    (``CIL.Safety.SpanView.validate, `LoopFrame.caller_valid),
    (``CIL.Safety.SpanView.element, `LoopFrame.caller_element),
    (``CIL.Safety.SpanView.slice, `LoopFrame.caller_slice)]

open Lean Meta in
/-- For an equation `f memory ... = .ok result` with `f` among `loopCallerFacts`, the carrying
    lemma, the memory and the reference `form` of the result would state, when the result is a
    reference that forms: an `add` or `element` result, or a formed reference. -/
def loopCallerFact? (type : Expr) : MetaM (Option (Lean.Name × Expr × Option Expr)) := do
  let some (_, lhs, rhs) := type.consumeMData.eq? | return none
  let some head := lhs.getAppFn.constName? | return none
  let some (_, carry) := loopCallerFacts.find? (·.1 == head) | return none
  let memory? ← lhs.getAppArgs.findM? fun argument => do
    return (← instantiateMVars (← inferType argument)).isConstOf ``Memory
  let some memory := memory? | return none
  let rhs := rhs.consumeMData
  let result := if rhs.isAppOfArity ``Except.ok 3 then some rhs.appArg! else none
  let formed := if [``CIL.Safety.form, ``CIL.Safety.add, ``CIL.Safety.SpanView.element].contains
    head then result else none
  return some (carry, memory, formed)

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
/-- A case split's negative side, `a ≠ b` or `¬a = b` over data: it decides a branch the loop
    tactics reach, and as a rewrite to `False` it cannot loop. -/
def isCaseDisequality (type : Expr) : MetaM Bool := do
  let type := type.consumeMData
  if type.isAppOfArity ``Ne 3 then return !(← isProp type.appFn!.appFn!.appArg!)
  unless type.isAppOfArity ``Not 1 do return false
  let some (carrier, _, _) := type.appArg!.consumeMData.eq? | return false
  return !(← isProp carrier)

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

/-- Whether `type` is a `LoopFrame` whose footprint is empty, so the caller's memory is kept. -/
def confinedToNone (type : Lean.Expr) : Bool :=
  type.isAppOfArity `CIL.Safety.LoopFrame 6 && (type.getArg! 0).isAppOfArity ``List.nil 1

open Lean Meta in
/-- The positions of the `some` entries of `list` up to reduction, reading cons cells until one is
    not: the locals a `knownLocals` list remembers. -/
partial def rememberedIndices (list : Lean.Expr) (index : Nat := 0) : MetaM (Array Nat) := do
  let cell ← whnf list
  unless cell.isAppOfArity ``List.cons 3 do return #[]
  let rest ← rememberedIndices cell.appArg! (index + 1)
  if (← whnf (cell.getArg! 1)).isAppOfArity ``Option.some 2 then return #[index] ++ rest
  return rest

open Lean Meta in
/-- The entries of `list` up to reduction with their positions, reading cons cells until one is
    not. -/
partial def listEntries (list : Lean.Expr) (index : Nat := 0) :
    MetaM (Array (Nat × Lean.Expr)) := do
  let cell ← whnf list
  unless cell.isAppOfArity ``List.cons 3 do return #[]
  return #[(index, cell.getArg! 1)] ++ (← listEntries cell.appArg! (index + 1))

open Lean Meta in
/-- The layout and field values of a remembered struct, `some (.aggregate (layout.encode
    values))`, reading the entry only through reducible definitions. -/
def encodedStruct? (entry : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let entry ← whnfR (← instantiateMVars entry)
  unless entry.isAppOfArity ``Option.some 2 do return none
  let value ← whnfR entry.appArg!
  unless value.isAppOfArity ``CIL.Value.aggregate 1 do return none
  let bytes := value.appArg!.headBeta.consumeMData
  unless bytes.isAppOfArity `CIL.AggregateLayout.encode 2 do return none
  return some (bytes.appFn!.appArg!, bytes.appArg!)

open Lean Elab Meta in
/-- A proof of `layout.Valid`: the extraction's `<layout>_valid` theorem when `layout` is a
    constant that has one, else a kernel decision. -/
def layoutValidity (layout : Lean.Expr) : MetaM Term := do
  if let some name := layout.constName? then
    let theoremName := name.appendAfter "_valid"
    if let some info := (← getEnv).find? theoremName then
      if ← isDefEq info.type (mkApp (mkConst `CIL.AggregateLayout.Valid) layout) then
        return mkCIdent theoremName
  `(by decide +kernel)

open Lean Meta in
/-- Whether `type` mentions `numericOfWidth` at a literal width, which unfolds to one value. -/
def loadsAtLiteralWidth (type : Expr) : Bool :=
  (type.find? fun e => e.isAppOfArity `CIL.Safety.numericOfWidth 2 &&
    (e.appFn!.appArg!.nat? <|> e.appFn!.appArg!.rawNatLit?).isSome).isSome

/-- The facts a loop tactic steps with: `core` at every instruction, and groups that speak only
    to some instructions, so each step's simp set holds only facts it can use. -/
structure LoopFacts where
  /-- The explicit facts, unfolds and gathered facts for every instruction. -/
  core : Array Lean.Syntax.Term
  /-- Each byte home's `form` with `localAddress`, which only taking a local's address reads;
      derived facts are proof terms, asserted by `assertLoopFacts` when first read. -/
  addresses : Array Lean.Syntax.Term := #[]
  /-- The field reads of remembered structs, which only `fieldAt` reads, as proof terms. -/
  fields : Array Lean.Syntax.Term := #[]
  /-- The negative sides of case splits, which only instructions testing or computing on data
      read. -/
  cases : Array Lean.Syntax.Term := #[]
  /-- The `form`, `add`, element and slice facts a frame carries from its caller, the `form` of
      each reference they or an `access` check give, and the facts of a span only a step
      produces, which only instructions using references or spans read, as proof terms. -/
  references : Array Lean.Syntax.Term := #[]
  /-- The statements of the explicit and gathered facts, which no group asserts again. -/
  known : Array Lean.Expr := #[]

/-- Every fact, for a tactic that does not step instruction by instruction. -/
def LoopFacts.all (facts : LoopFacts) : Array Lean.Syntax.Term :=
  facts.core ++ facts.addresses ++ facts.fields ++ facts.cases ++ facts.references

open Lean Elab Tactic Meta in
/-- `facts`, followed by the facts a loop proof's context determines, each at most once:
    * the declarations in scope with `cil_loop_unfold` that `reachableLoopUnfolds` finds from
      the goal and the facts;
    * hypotheses `loopFactSides?` recognizes;
    * for `span : CheckedSpan`, `span.facts`, `span.length_nil` or `span.length_cons` when its
      values are `[]` or a cons, and `span.valid_within wellFormed frame` for each
      `frame : LoopFrame` from its memory with that memory's `wellFormed` in context;
    * for a formed reference, `Unsafe.Add` result, or span validity, element or slice equation at
      the caller memory of a `frame : LoopFrame` with that memory's `wellFormed` in context, the
      equation at the frame's memory (`LoopFrame.caller_form` and its kind), and for an `add`
      result or an `access` check, the `form` of the reference it gives; these, and the facts of
      a span only a kept equation produces, are read only by instructions that use a reference
      or span (`loopReadsReferences`);
    * for `contents : SpanContents`, `contents.elementWidth`;
    * for `frame : LoopFrame` over `knownLocals` of a list, the load of each remembered local, with
      `localResult`;
    * for `frame : LoopFrame []` and the entry's `setup` equation, `frame.leave_kept setup` when
      the goal can return;
    * `numericOfWidth` and `BitVec.ofNat_toNat` when a gathered fact loads at a literal width.
    Only hypotheses reachable by name are read, so shadowed and hygienic ones are skipped. A
    fact is kept only when the goal reaches every variable it is about: those of the scope
    `loopGoalScope` gives and of the explicit facts, then the right side of each kept equation;
    a derived fact must be about variables reached without an equation. An equation is kept only
    at a memory that a state of the goal holds or a kept equation or explicit fact mentions, and
    a derived fact only at a state's memory. Derived facts are asserted as hygienic hypotheses,
    skipping any statement already gathered. Home forms, field reads and the negative sides of
    case splits are grouped apart from the rest, for the instructions that read them. -/
def gatherLoopFactGroups (facts : Array Term) : TacticM LoopFacts := withMainContext do
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
  -- An explicit proof term's statement is not derived again from the frames in scope.
  for fact in facts do
    if fact.raw.isIdent then continue
    let saved ← saveState
    let type? ← try
        let proof ← Term.withoutErrToSorry <| Term.elabTerm fact none
        Term.synthesizeSyntheticMVarsNoPostponing
        pure (some (← instantiateMVars (← inferType proof)))
      catch _ => pure none
    saved.restore
    if let some type := type? then
      unless type.hasMVar do known := known.push type.consumeMData
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
    else if ← isCaseDisequality type then
      candidates := candidates.push (`caseSplit, fact, variables #[type], #[], #[])
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
        unless frameType.isAppOfArity `CIL.Safety.LoopFrame 6 &&
          frameType.getArg! 1 == arguments[0]! && isLive (frameType.getArg! 2) do continue
        for (formed, formedType) in typed do
          unless formedType.isAppOfArity ``Memory.WellFormed 1 &&
            formedType.appArg! == arguments[0]! do continue
          candidates := candidates.push (`spanFacts,
            applied `CheckedSpan.valid_within #[fact, named formed, named frame],
            variables #[frameType.getArg! 2, arguments[1]!], #[], #[])
    -- A reference check or address, or a caller fact a frame carries to its own memory. The
    -- caller's memory can be live too, since a frame's activation names its watermark.
    let hole : Term ← `(_)
    let carriers (memory : Expr) : Array (LocalDecl × LocalDecl) := Id.run do
      let mut found := #[]
      for (frame, frameType) in typed do
        unless frameType.isAppOfArity `CIL.Safety.LoopFrame 6 && frameType.getArg! 1 == memory &&
          frameType.getArg! 2 != memory && isLive (frameType.getArg! 2) do continue
        for (formed, formedType) in typed do
          if formedType.isAppOfArity ``Memory.WellFormed 1 && formedType.appArg! == memory then
            found := found.push (frame, formed)
      return found
    let formTerms (memory : Expr) (proof : Term) : Array Term :=
      (if isLive memory then #[proof] else #[]) ++ (carriers memory).map fun (frame, formed) =>
        applied `LoopFrame.caller_form #[named frame, named formed, proof]
    if let some (_, checked, _) := type.eq? then
      if checked.isAppOfArity `CIL.Safety.access 5 then
        for proof in formTerms (checked.getArg! 0) (applied `access_reference_valid
            #[hole, hole, hole, hole, hole, fact]) do
          candidates := candidates.push (`referenceFact, proof, #[], #[], #[])
    if let some (carry, memory, formedResult) ← loopCallerFact? type then
      -- An `Unsafe.Add` result forms; a span element's load needs no `form` of its own.
      if formedResult.isSome && (type.consumeMData.eq?.any fun (_, lhs, _) =>
          lhs.isAppOf ``CIL.Safety.add) then
        for proof in formTerms memory (applied `add_formed #[fact]) do
          candidates := candidates.push (`referenceFact, proof, #[], #[], #[])
      -- A span fact is carried only for a span the goal names; each produces its result.
      if let some (_, lhs, rhs) := type.consumeMData.eq? then
        let subject := if formedResult.isSome then #[]
          else (variables lhs.getAppArgs).filter (· != memory.fvarId!)
        -- A span's validity stays with every step, since loading a span local reads it.
        let base := if carry == `LoopFrame.caller_valid then `callerFact else `referenceFact
        for (frame, formed) in carriers memory do
          candidates := candidates.push (base,
            applied carry #[named frame, named formed, fact], subject, #[], variables #[rhs])
    if type.isAppOfArity `CIL.Safety.SpanContents 4 then
      candidates := candidates.push (`elementWidth, applied `SpanContents.elementWidth #[fact],
        variables #[arguments[1]!], #[], #[])
    -- An entry frame for every footprint gives the frame facts at the empty one.
    let entered ← match type with
      | .forallE _ domain body _ =>
        if body.isAppOfArity `CIL.Safety.LoopFrame 6 && body.getArg! 0 == .bvar 0 then
          let empty ← mkAppOptM ``List.nil #[domain.appArg!]
          pure (some (← `(($fact [])), body.instantiate1 empty))
        else pure none
      | _ => pure none
    let framed := if type.isAppOfArity `CIL.Safety.LoopFrame 6 then some (fact, type) else entered
    if let some (frameTerm, frameType) := framed then
      let frameArguments := frameType.getAppArgs
      -- Facts at a frame's memory are kept once a state holds it or a kept step produces it.
      let memory := #[frameArguments[2]!]
      let subject := variables #[frameArguments[4]!]
      let numeral (index : Nat) : Term := ⟨Syntax.mkNumLit (toString index)⟩
      -- Each byte home forms, so `localAddr` of it steps.
      for (index, slot) in ← listEntries frameArguments[4]! do
        if (← whnf slot).isAppOfArity ``LocalSlot.bytes 2 then
          candidates := candidates.push (`homeForm,
            applied `LoopFrame.form_home #[frameTerm, numeral index], subject, memory, #[])
      let remembered := frameArguments[5]!.consumeMData
      if remembered.isAppOfArity `CIL.Safety.knownLocals 1 then
        for (index, entry) in ← listEntries remembered.appArg! do
          unless (← whnf entry).isAppOfArity ``Option.some 2 do continue
          candidates := candidates.push (`homeLoad,
            applied `LoopFrame.load #[frameTerm, numeral index], subject, memory, #[])
          -- A struct remembered by its field values reads each field by value and by address.
          let some (layout, values) ← encodedStruct? entry | continue
          let valid ← layoutValidity layout
          -- The literal list after the simprocs, such as a nested `List.replicate` spelled out, is
          -- the form stepping leaves on the stack.
          let entries ← listEntries values
          let literal ← mkListLit (mkConst ``CIL.Value) (entries.toList.map (·.2))
          let (spelled, _) ←
            simp literal (← Simp.mkContext { bitVecOfNat := false }) #[← Simp.getSimprocs]
          let valuesTerm ← Term.exprToSyntax spelled.expr
          let fields ← listEntries (mkApp (mkConst `CIL.AggregateLayout.fields) layout)
          for (field, fieldLayout) in fields do
            -- A 1- or 2-byte field reads back truncated, through `narrowLoad`.
            let width ← whnf (mkApp (mkConst `CIL.FieldLayout.width) fieldLayout)
            let narrow := (← getNatValue? width) matches some 1 | some 2
            let (base, read, load) := if narrow then
                (`narrowRead, `step_fieldAt_encode_narrow, `LoopFrame.load_narrow_field)
              else (`fieldRead, `step_fieldAt_encode, `LoopFrame.load_field)
            candidates := candidates.push (base, applied read
              #[valid, numeral field, valuesTerm], subject, memory, #[])
            candidates := candidates.push (base, applied load
              #[frameTerm, numeral index, valid, numeral field], subject, memory, #[])
    if type.isAppOfArity `CIL.Safety.LoopFrame 6 && isLive arguments[2]! then
      if confinedToNone type && scope.returns then
        for (setup, setupType) in typed do
          let some (_, entry, _) := setupType.eq? | continue
          unless entry.isAppOfArity ``enterFrame 3 && entry.appArg! == arguments[1]! do continue
          candidates := candidates.push (`frameLeave,
            applied `LoopFrame.leave_kept #[named setup, fact], variables #[arguments[2]!], #[],
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
      -- A span's validity is read where a kept equation, such as a slice, produced the span.
      let visible := if base.isAnonymous || base == `caseSplit || base == `spanFacts then reached
        else direct
      if !kept[index]! && subject.all visible.contains &&
          memories.all fun memory => live.all (·.contains memory) then
        kept := kept.set! index true
        reached := reached ++ produced
        live := live.map (· ++ asTerms produced)
        changed := changed || !produced.isEmpty
  let mut literalWidth := false
  let mut homeLoads := false
  let mut addresses : Array Term := #[]
  let mut fields : Array Term := #[]
  let mut cases : Array Term := #[]
  let mut references : Array Term := #[]
  let mut narrowReads := false
  for ((base, fact, _, _, _), keep) in candidates.zip kept do
    if keep && base == `caseSplit then cases := cases.push fact
    unless keep && base.isAnonymous do continue
    gathered := gathered.push fact
    if let some declaration := context.findFromUserName? fact.raw.getId then
      let type ← instantiateMVars declaration.type
      literalWidth := literalWidth || loadsAtLiteralWidth type
      constants := constants ++ type.getUsedConstants
      known := known.push type.consumeMData
  for ((base, fact, subject, _, _), keep) in candidates.zip kept do
    unless keep && !base.isAnonymous && base != `caseSplit do continue
    -- Home forms and field reads are asserted only once an instruction reads them.
    if base == `homeForm then addresses := addresses.push fact; continue
    -- A span only a step produces, such as a slice, is read by the instructions that use it.
    if base == `spanFacts && !subject.all direct.contains then
      references := references.push fact; continue
    if base == `fieldRead then fields := fields.push fact; continue
    if base == `narrowRead then fields := fields.push fact; narrowReads := true; continue
    if base == `referenceFact then references := references.push fact; continue
    if let some (asserted, type) ← assertLoopFact base fact known then
      -- A derived fact can name a frame the goal no longer does, such as the entry frame's owner.
      constants := constants ++ type.getUsedConstants
      known := known.push type
      gathered := gathered.push asserted
      homeLoads := homeLoads || base == `homeLoad
  if homeLoads && !explicitNames.contains ``localResult then
    gathered := gathered.push (global ``localResult)
  if !addresses.isEmpty && !explicitNames.contains ``localAddress then
    addresses := addresses.push (global ``localAddress)
  -- A narrow read leaves `narrowLoad` on the stack; it must reduce to a literal for a later
  -- branch or return to compare it.
  if narrowReads then
    for name in [`CIL.Safety.narrowLoad, ``BitVec.reduceSetWidth, ``BitVec.reduceSignExtend] do
      unless explicitNames.contains name do gathered := gathered.push (global name)
  if literalWidth then
    for name in [`CIL.Safety.numericOfWidth, ``BitVec.ofNat_toNat] do
      unless explicitNames.contains name do gathered := gathered.push (global name)
  let unfolds ← reachableLoopUnfolds constants
  let unfolds := unfolds.filter (!explicitNames.contains ·)
  let core := facts ++ unfolds.map global ++ gathered
  return { core, addresses, fields, cases, references, known }

open Lean Elab Tactic in
/-- `terms` with each proof term asserted as a hygienic hypothesis named from `base`, skipping
    any that do not elaborate to a closed proposition or state one of `known`; names stay as
    given. -/
def assertLoopFacts (base : Name) (terms : Array Term) (known : Array Expr := #[]) :
    TacticM (Array Term) := do
  let mut asserted := #[]
  let mut known := known
  for term in terms do
    if term.raw.isIdent then asserted := asserted.push term; continue
    if let some (name, type) ← assertLoopFact base term known then
      asserted := asserted.push name
      known := known.push type
  return asserted

open Lean Elab Tactic in
/-- `gatherLoopFactGroups` as one list, for a tactic that does not step instruction by
    instruction. -/
def gatherLoopFacts (facts : Array Term) : TacticM (Array Term) :=
  return (← gatherLoopFactGroups facts).all

end CIL.Safety
