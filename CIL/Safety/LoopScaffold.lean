import CIL.Safety.LoopAutomation
import CIL.Safety.FrameProgress
import CIL.Safety.NumericLocals
import Lean

/-!
# Checked loop scaffolding

Proof-local generators derive entry frames and cutpoints from extracted methods. Generated
equations are checked by the kernel; no frame layout or instruction position is assumed.
Only proofs requesting the scaffold elaborate it, so extraction certificates stay unchanged.
-/

namespace CIL.Safety
open Lean Elab Command

/-- A successful checked entry's projections describe exactly the returned frame and memory. -/
theorem entry_result_checked (result : ExecutionResult (Frame × Memory))
    (success : result.toOption.isSome = true) : result = .ok (result.toOption.get success) := by
  cases result with
  | error fault => cases success
  | ok pair => rfl
#print axioms entry_result_checked

/-- Existing frame-validity premises justify symbolic entry without evaluating caller storage. -/
theorem enterFrame_isSome (body : CIL.Method) (args : List Value) (memory : Memory)
    (wellFormed : memory.WellFormed) (valid : ValuesValid memory args)
    (fits : FrameSetupFits body args) : (enterFrame body args memory).toOption.isSome = true := by
  obtain ⟨frame, entered, checked⟩ := enterFrame_succeeds body args memory wellFormed valid fits
  rw [checked]
  rfl
#print axioms enterFrame_isSome

/-- Derive parameterized frames, memory and numeric homes from checked allocation.
    Entry must reduce to success or have an explicit proof; no failure receives a default. -/
syntax "bind_entry " ident bracketedBinder* " := " term:max
  " with " term:max " from " term:max (" using " term:max)? (" allocating " term:max)?
  (" simplifying " "[" term,* "]")? : command

/-- Normalize frame setup with explicit storage facts, retaining checked allocation semantics. -/
private def entrySimplifier {m : Type → Type} [Monad m] [MonadQuotation m]
    (body : TSyntax `term) (facts : Array (TSyntax `term)) : m (TSyntax `tactic) := do
  let facts := (if body.raw.isIdent then #[body] else #[]) ++ facts
  `(tactic| (simp [enterFrame, makeSelectedLocals, makeLocals,
    makeArgumentHomes, makeParameterHomes, makeLocal, storeLocal, Value.hasUnspecified,
    checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    $[$facts:term],*]; try rfl))

/-- Rewrite each numeric local by its allocation equation before `makeLocal` is unfolded, then
    normalize the rest of frame setup; an unmatched equation leaves allocation unresolved. -/
private def allocationSimplifier {m : Type → Type} [Monad m] [MonadQuotation m]
    (body : TSyntax `term) (facts made : Array (TSyntax `term)) : m (TSyntax `tactic) := do
  let unfolded := (if body.raw.isIdent then #[body] else #[]) ++ facts ++ made
  let normalizer ← entrySimplifier body (facts ++ made)
  `(tactic| ((simp only [enterFrame, makeSelectedLocals, makeLocals, List.isEmpty, ite_true,
    Bind.bind, Except.bind, Pure.pure, Except.pure, $[$unfolded:term],*]) <;> $normalizer:tactic))

/-- A local slot's generated facts: its index and slot, typed load and store facts for span and
    root slots, the address of a byte home, and whether the storage kind mentions binders. -/
private abbrev SlotFacts :=
  Nat × Term × Option Term × Option Term × Option Term × Bool

/-- Read the generated facts for each local of a frame whose local list reduces. -/
private def frameSlots (frame : Expr) : TermElabM (Array SlotFacts) := do
  let mut locals := mkApp (mkConst ``Frame.locals) frame
  let mut homes := #[]
  let mut index := 0
  repeat
    match (← Meta.whnf locals).getAppFnArgs with
    | (``List.cons, #[_, slot, tail]) =>
      let slotValue ← Meta.whnf slot
      let (loaded, stored, address) ← match slotValue.getAppFnArgs with
      | (``LocalSlot.bytes, #[_, address]) =>
        pure (none, none, some (← PrettyPrinter.delab address))
      | (``LocalSlot.span, #[width, writable, _]) =>
        let width ← PrettyPrinter.delab width
        let writable ← PrettyPrinter.delab writable
        pure (some (← `(loadLocal_span (width := $width) (writable := $writable))),
          some (← `(storeLocal_span (width := $width) (writable := $writable))), none)
      | (``LocalSlot.root, _) =>
        pure (some (← `(loadLocal_root)), some (← `(storeLocal_root)), none)
      | (``LocalSlot.readOnlyRoot, _) =>
        pure (some (← `(loadLocal_readOnlyRoot)),
          some (← `(storeLocal_readOnlyRoot_readOnly)), none)
      | _ => pure (none, none, none)
      let symbolic := match slotValue.getAppFnArgs with
        | (``LocalSlot.span, #[width, writable, _]) => width.hasFVar || writable.hasFVar
        | _ => false
      homes := homes.push (index, ← PrettyPrinter.delab slot, loaded, stored, address, symbolic)
      locals := tail
      index := index + 1
    | _ => break
  return homes

/-- Emit `homeN` for byte homes when `addresses` holds, and `slotN`, `loadN` and `storeN` for
    span and root slots. -/
private def emitSlots (name : Ident)
    (binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder)
    (slots : Array SlotFacts) (addresses : Bool) : CommandElabM Unit := do
  for (index, slot, loaded, stored, address, symbolic) in slots do
    if let some address := address then
      if addresses then
        let home := mkIdent (name.getId ++ Name.mkSimple s!"home{index}")
        elabCommand (← `(abbrev $home $binders* : Reference := $address))
    if let (some loaded, some stored) := (loaded, stored) then
      let slotName := mkIdent (name.getId ++ Name.mkSimple s!"slot{index}")
      elabCommand (← `(abbrev $slotName $binders* : LocalSlot := $slot))
      let loadedName := mkIdent (name.getId ++ Name.mkSimple s!"load{index}")
      let storedName := mkIdent (name.getId ++ Name.mkSimple s!"store{index}")
      let factBinders := if symbolic then binders else #[]
      elabCommand (← `(abbrev $loadedName $factBinders* := $loaded))
      elabCommand (← `(abbrev $storedName $factBinders* := $stored))

/-- A numeric local of the entered method: its index, storage kind, initializer and the number
    its home stores. -/
private structure NumericLocal where
  index : Nat
  kind : Term
  value : Term
  number : Term

/-- The kinds `makeLocal` creates without allocating memory. -/
private def unallocatedKinds : List Name :=
  [``CIL.LocalKind.span, ``CIL.LocalKind.reference, ``CIL.LocalKind.array,
    ``CIL.LocalKind.methodPointer, ``CIL.LocalKind.methodTable]

/-- Find the numeric locals of `body`. Every other local must be created without allocating, so
    each allocation of the entered frame is a numeric home. -/
private def numericLocals (body : Term) : TermElabM (Array NumericLocal) := do
  let kinds ← Term.elabTerm (← `(CIL.Method.localKinds $body)) none
  let values ← Term.elabTerm (← `(CIL.Method.locals $body)) none
  Term.synthesizeSyntheticMVarsNoPostponing
  let mut kinds ← instantiateMVars kinds
  let mut values ← instantiateMVars values
  let mut found := #[]
  let mut index := 0
  repeat
    match (← Meta.whnf kinds).getAppFnArgs, (← Meta.whnf values).getAppFnArgs with
    | (``List.cons, #[_, kind, kindTail]), (``List.cons, #[_, value, valueTail]) =>
      let outcome ← Meta.whnf (mkApp2 (mkConst ``localNumber) kind value)
      match outcome.getAppFnArgs with
      | (``Except.ok, #[_, _, number]) =>
        found := found.push ⟨index, ← PrettyPrinter.delab kind, ← PrettyPrinter.delab value,
          ← PrettyPrinter.delab (← Meta.reduce number)⟩
      | _ =>
        let storage ← Meta.whnf kind
        unless unallocatedKinds.any storage.isAppOf do
          throwError "Local {index} allocates a home without a checked numeric initializer"
      kinds := kindTail
      values := valueTail
      index := index + 1
    | (``List.nil, _), (``List.nil, _) => break
    | _, _ => throwError "Local kinds and initializers must reduce to lists of equal length"
  return found

/-- Introduce each numeric home, the memory after it and its allocation equation, passing them
    to `continuation` in that order, three per home. -/
private partial def withNumericHomes {α : Type} (memory : Term) (homes : Array NumericLocal)
    (position : Nat) (current : Term) (introduced : Array Expr)
    (continuation : Array Expr → Term → TermElabM α) : TermElabM α := do
  if h : position < homes.size then
    let home := homes[position]
    let reference := mkIdent (Name.mkSimple s!"home{home.index}")
    let allocated := mkIdent (Name.mkSimple s!"allocated{home.index}")
    Meta.withLocalDeclD reference.getId (mkConst ``Reference) fun referenceVar =>
    Meta.withLocalDeclD allocated.getId (mkConst ``Memory) fun allocatedVar => do
      let made ← Term.elabTerm (← `(makeLocal ($memory).nextIdentity $(home.kind) $(home.value)
        $current = Except.ok (LocalSlot.bytes $(home.kind) $reference, [($reference).allocation],
          $allocated))) (some (mkSort .zero))
      Term.synthesizeSyntheticMVarsNoPostponing
      Meta.withLocalDeclD (Name.mkSimple s!"made{home.index}") (← instantiateMVars made)
        fun madeVar => withNumericHomes memory homes (position + 1) allocated
          (introduced ++ #[referenceVar, allocatedVar, madeVar]) continuation
  else continuation introduced current

/-- Add the theorem `name : ∀ context, statement` proved by `proof`, both closed over the
    local `context`; frame setup is normalized once and this proof reused, not re-simplified. -/
private def addClosedTheorem (name : Name) (context : Array Expr) (statement proof : Expr) :
    TermElabM Unit := do
  -- Binder types keep assigned universe metavariables until the abstraction is instantiated.
  let type ← instantiateMVars (← Meta.mkForallFVars context (← instantiateMVars statement))
  let value ← instantiateMVars (← Meta.mkLambdaFVars context (← instantiateMVars proof))
  if type.hasMVar || value.hasMVar then
    throwError "Entry normalization left metavariables in its setup proof"
  addDecl (.thmDecl { name, levelParams := [], type, value })

/-- Introduce the numeric home references alone. -/
private partial def withHomeReferences {α : Type} (homes : List NumericLocal)
    (continuation : TermElabM α) : TermElabM α :=
  match homes with
  | [] => continuation
  | home :: rest =>
    Meta.withLocalDeclD (Name.mkSimple s!"home{home.index}") (mkConst ``Reference) fun _ =>
      withHomeReferences rest continuation

/-- Derive an entry whose numeric locals allocate homes in symbolic memory. The frame is
    explicit in opaque home references, and the checked theorem yields them existentially. -/
private def elabAllocatingEntry (name : Ident)
    (binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder)
    (body args memory wellFormed : Term) (facts : Array Term) : CommandElabM Unit := do
  let indexed (base : String) (index : Nat) := mkIdent (Name.mkSimple s!"{base}{index}")
  let kept := mkIdent `kept
  let setupName := (← getCurrNamespace) ++ name.getId ++ `setup
  let (homes, frameBinders, frameParameters, frameValue, parameters) ←
      liftTermElabM <| Term.elabBinders binders fun variables => do
    let homes ← numericLocals body
    withNumericHomes memory homes 0 memory #[] fun introduced final => do
      let references := (List.range homes.size).toArray.map (introduced[3 * ·]!)
      let finalValue ← Term.elabTerm final (some (mkConst ``Memory))
      let keptType ← Term.elabTerm (← `(MemoryBelow ($memory).nextIdentity $memory $final))
        (some (mkSort .zero))
      Term.synthesizeSyntheticMVarsNoPostponing
      Meta.withLocalDeclD kept.getId (← instantiateMVars keptType) fun keptVar => do
        -- Caller span validity survives earlier frame allocations; other facts are kept as is.
        let mut transported := #[]
        for fact in facts do
          let candidate ← `(SpanView.validate_below _ $fact $wellFormed $kept)
          let saved ← saveState
          let accepted ← try
              let _ ← Term.withoutErrToSorry <| Term.elabTerm candidate none
              Term.synthesizeSyntheticMVarsNoPostponing
              pure true
            catch _ => pure false
          saved.restore
          if accepted then transported := transported.push candidate
        let made := homes.map fun home => indexed "made" home.index
        let normalizer ← allocationSimplifier body (facts ++ transported) made
        let outcome ← Term.elabTermEnsuringType (← `(enterFrame $body $args $memory)) none
        Term.synthesizeSyntheticMVarsNoPostponing
        let pair ← Meta.mkFreshExprMVar (← Term.elabTerm (← `(Frame × Memory)) none)
        let success ← Meta.mkAppOptM ``Except.ok
          #[some (mkConst ``ExecutionFault), some (← Meta.inferType pair), some pair]
        let equality ← Meta.mkFreshExprMVar (← Meta.mkEq (← instantiateMVars outcome) success)
        let remaining ← Tactic.run equality.mvarId! (Tactic.evalTactic normalizer)
        unless remaining.isEmpty do
          throwError "Entry facts do not establish a successful allocation"
        let pair ← instantiateMVars pair
        let (``Prod.mk, #[_, _, frame, entered]) := pair.getAppFnArgs
          | throwError "Entry facts leave the allocated frame unresolved"
        if frame.hasMVar then throwError "Entry facts leave the allocated frame unresolved"
        unless entered == (← instantiateMVars finalValue) do
          throwError "Frame entry allocates storage other than its numeric homes"
        let homeIds := references.map Expr.fvarId!
        let userIds := variables.map Expr.fvarId!
        let mentioned := (collectFVars {} frame).fvarIds
        for fvar in mentioned do
          unless homeIds.contains fvar || userIds.contains fvar do
            throwError "The entered frame depends on intermediate allocation state"
        -- The frame takes only the binders its layout mentions, with their dependencies.
        let mut needed := mentioned.filter userIds.contains
        for binder in variables.reverse do
          if needed.contains binder.fvarId! then
            let dependencies := (collectFVars {} (← binder.fvarId!.getType)).fvarIds
            needed := needed ++ dependencies.filter userIds.contains
        let selected := variables.filter (needed.contains ·.fvarId!)
        let frameBinders ← selected.mapM fun selection => do
          let declaration ← selection.fvarId!.getDecl
          let type ← PrettyPrinter.delab declaration.type
          `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent declaration.userName) : $type))
        let frameParameters ← selected.mapM fun selection => do
          return mkIdent (← selection.fvarId!.getDecl).userName
        addClosedTheorem setupName (variables ++ introduced.push keptVar)
          (← equality.mvarId!.getType) equality
        let parameters ← variables.mapM fun binder => do
          return mkIdent (← binder.fvarId!.getDecl).userName
        return (homes, frameBinders, frameParameters, ← PrettyPrinter.delab frame, parameters)
  let frameName := mkIdent (name.getId ++ `frame)
  let homeNames := homes.map fun home => indexed "home" home.index
  let homeBinders ← homeNames.mapM fun home =>
    `(Lean.Parser.Term.bracketedBinderF| ($home : Reference))
  let allBinders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder :=
    (frameBinders ++ homeBinders).map (⟨·.raw⟩)
  elabCommand (← `(def $frameName $allBinders* : Frame := $frameValue))
  let frameApplied ← `($frameName $(frameParameters ++ homeNames)*)
  let entered := mkIdent `entered
  let final := match homes.back? with
    | some home => indexed "allocated" home.index
    | none => memory
  let mut statement ← `(EntryMemory $memory $entered)
  for home in homes.reverse do
    statement ← `(NumericEntryHome $memory $entered $(home.kind) $(home.number)
      $(indexed "home" home.index) ∧ $statement)
  statement ← `(enterFrame $body $args $memory = .ok ($frameApplied, $entered) ∧ $statement)
  statement ← `(∃ $entered:ident : Memory, $statement)
  for home in homes.reverse do
    statement ← `(∃ $(indexed "home" home.index):ident : Reference, $statement)
  let mut progress := mkIdent `entryMemory
  let mut steps : Array (TSyntax `tactic) :=
    #[← `(tactic| have $progress:ident := EntryMemory.start $wellFormed)]
  for home in homes do
    let step := indexed "step" home.index
    steps := steps.push (← `(tactic| obtain ⟨$(indexed "home" home.index):ident,
      $(indexed "allocated" home.index):ident, $(indexed "made" home.index):ident,
      $(indexed "numeric" home.index):ident, $step:ident⟩ :=
        make_numeric_entry_local $progress ($memory).nextIdentity $(home.kind) $(home.value)
          $(home.number) rfl))
    let next := indexed "entryMemory" home.index
    steps := steps.push (← `(tactic| have $next:ident := EntryMemory.trans $progress $step))
    progress := next
  steps := steps.push (← `(tactic| have $kept:ident := ($progress).kept))
  let setup := mkIdent `setup
  let mut setupArguments : Array Term := parameters
  for home in homes do
    setupArguments := setupArguments ++ #[indexed "home" home.index,
      indexed "allocated" home.index, indexed "made" home.index]
  steps := steps.push (← `(tactic| have $setup:ident :
    enterFrame $body $args $memory = .ok ($frameApplied, $final) :=
      @$(mkCIdent setupName) $(setupArguments.push kept)*))
  let mut witnesses : Array Term := homeNames.map (⟨·.raw⟩) ++ #[final, setup]
  for (home, position) in homes.zipIdx do
    let mut fact : Term := indexed "numeric" home.index
    for later in homes.extract (position + 1) homes.size do
      fact ← `(NumericEntryHome.after $fact $(indexed "step" later.index))
    witnesses := witnesses.push fact
  witnesses := witnesses.push progress
  steps := steps.push (← `(tactic| exact ⟨$witnesses,*⟩))
  let checked := mkIdent (name.getId ++ `checked)
  elabCommand (← `(theorem $checked $binders* : $statement := by $steps*))
  elabCommand (← `(#print axioms $checked))
  let slots ← liftTermElabM <| Term.elabBinders binders fun _ =>
    withHomeReferences homes.toList do
      frameSlots (← Term.elabTerm frameApplied (some (mkConst ``Frame)))
  emitSlots name binders slots false

elab_rules : command
  | `(bind_entry $name $binders* := $body with $args from $memory $[using $witness]?
      $[allocating $wellFormed]? $[simplifying [$facts,*]]?) => do
    if let some wellFormed := wellFormed then
      if witness.isSome then throwError "Choose a success witness or allocation, not both"
      return ← elabAllocatingEntry name binders body args memory wellFormed
        (facts.map (·.getElems) |>.getD #[])
    if witness.isSome && facts.isSome then
      throwError "Choose a success witness or simplifying facts, not both"
    let normalizer ← entrySimplifier body (facts.map (·.getElems) |>.getD #[])
    let (parameters, computed) ← liftTermElabM <| Term.elabBinders binders fun variables => do
      let outcome ← Term.elabTermEnsuringType (← `(enterFrame $body $args $memory)) none
      Term.synthesizeSyntheticMVarsNoPostponing
      let computed ← if facts.isSome then do
        let pair ← Meta.mkFreshExprMVar (← Term.elabTerm (← `(Frame × Memory)) none)
        let success ← Meta.mkAppOptM ``Except.ok
          #[some (mkConst ``ExecutionFault), some (← Meta.inferType pair), some pair]
        let equality ← Meta.mkFreshExprMVar (← Meta.mkEq outcome success)
        let remaining ← Tactic.run equality.mvarId! (Tactic.evalTactic normalizer)
        unless remaining.isEmpty do
          throwError "Entry facts do not establish a successful allocation"
        let pair ← instantiateMVars pair
        if pair.hasMVar then throwError "Entry facts leave the allocated frame unresolved"
        let proof ← Meta.mkLambdaFVars variables (← instantiateMVars equality)
        pure (some (← PrettyPrinter.delab pair, proof))
      else pure none
      unless computed.isSome || witness.isSome ||
          (← Meta.whnf (← instantiateMVars outcome)).isAppOf ``Except.ok do
        throwError "Frame entry must reduce to a successful checked allocation"
      let parameters ← variables.mapM fun parameter => do
        return mkIdent (← parameter.fvarId!.getDecl).userName
      return (parameters, computed)
    let result := mkIdent (name.getId ++ `result)
    let frame := mkIdent (name.getId ++ `frame)
    let entered := mkIdent (name.getId ++ `memory)
    let equation := mkIdent (name.getId ++ `checked)
    let success ← match witness with
      | some proof => pure proof
      | none => `(by rfl)
    let resultValue ← match computed with
      | some (pair, _) => pure pair
      | none => `(((enterFrame $body $args $memory).toOption).get $success)
    elabCommand (← `(def $result $binders* : Frame × Memory := $resultValue))
    let frameValue ← if witness.isSome && computed.isNone then `((@$result $parameters*).1) else
      liftTermElabM <| Term.elabBinders binders fun _ => do
        let value ← Term.elabTerm (← `((@$result $parameters*).1)) (some (mkConst ``Frame))
        PrettyPrinter.delab (← Meta.reduce (← instantiateMVars value))
    elabCommand (← `(def $frame $binders* : Frame := $frameValue))
    elabCommand (← `(def $entered $binders* : Memory := (@$result $parameters*).2))
    let statement ← `(enterFrame $body $args $memory =
      .ok (@$frame $parameters*, @$entered $parameters*))
    if let some (_, proof) := computed then
      -- The kernel unfolds the frame and memory definitions to the normalized pair.
      let equationName := (← getCurrNamespace) ++ equation.getId
      liftTermElabM <| Term.elabBinders binders fun variables => do
        let type ← Term.elabType statement
        Term.synthesizeSyntheticMVarsNoPostponing
        addClosedTheorem equationName variables type (proof.beta variables)
    else
      elabCommand (← `(theorem $equation $binders* : $statement :=
        entry_result_checked _ $success))
    elabCommand (← `(#print axioms $equation))
    let slots ← liftTermElabM <| Term.elabBinders binders fun _ => do
      frameSlots (← Term.elabTerm (← `(@$frame $parameters*)) none)
    emitSlots name binders slots true

/-- Derive the unique matching cutpoint and a state constructor from the extracted body.
    Ambiguous or missing matches fail the kernel-checked uniqueness obligation. -/
syntax "bind_cutpoint " ident " := " term:max " matching " term:max
  " with " term:max : command

/-- Select an instruction explicitly, including a structural label in a multi-loop method.
    The requested instruction must exist and satisfy the supplied predicate. -/
syntax "bind_cutpoint " ident bracketedBinder* " := " term:max " at " term:max
  " matching " term:max " with " term:max : command

elab_rules : command
  | `(bind_cutpoint $name $binders* := $body at $location matching $predicate with $frame) => do
    liftTermElabM do
      let selected ← Term.elabTermEnsuringType
        (← `(if ($body).code[$location]?.map $predicate = some true then 1 else 0))
        (some (mkConst ``Nat))
      Term.synthesizeSyntheticMVarsNoPostponing
      unless (← (Meta.evalNat (← Meta.reduce (← instantiateMVars selected))).run) == some 1 do
        throwError "Selected cutpoint must exist and match the instruction predicate"
    let pc := mkIdent (name.getId ++ `pc)
    let checked := mkIdent (name.getId ++ `checked)
    elabCommand (← `(@[cil_code] def $pc : Nat := $location))
    elabCommand (← `(theorem $checked :
      ($body).code[$pc]?.map $predicate = some true := by decide +kernel))
    elabCommand (← `(#print axioms $checked))
    elabCommand (← `(def $name $binders* (stack : List Value) (memory : Memory) : LoopState :=
      ⟨$pc, $frame, stack, memory⟩))

elab_rules : command
  | `(bind_cutpoint $name := $body matching $predicate with $frame) => do
    let pc := mkIdent (name.getId ++ `pc)
    let checked := mkIdent (name.getId ++ `checked)
    let location ← liftTermElabM do
      let count ← Term.elabTermEnsuringType (← `((($body).code.filter $predicate).length))
        (some (mkConst ``Nat))
      Term.synthesizeSyntheticMVarsNoPostponing
      unless (← (Meta.evalNat (← Meta.reduce (← instantiateMVars count))).run) == some 1 do
        throwError "Cutpoint must match exactly one instruction"
      let value ← Term.elabTermEnsuringType (← `(instructionLocation $body $predicate))
        (some (mkConst ``Nat))
      Term.synthesizeSyntheticMVarsNoPostponing
      let some location ← (Meta.evalNat (← Meta.reduce (← instantiateMVars value))).run
        | throwError "Cutpoint must reduce to an instruction index"
      return location
    elabCommand (← `(@[cil_code] def $pc : Nat := $(quote location)))
    elabCommand (← `(theorem $checked :
      ($body).code[$pc]?.map $predicate = some true ∧
        (($body).code.filter $predicate).length = 1 := by decide +kernel))
    elabCommand (← `(#print axioms $checked))
    elabCommand (← `(def $name (stack : List Value) (memory : Memory) : LoopState :=
      ⟨$pc, $frame, stack, memory⟩))

end CIL.Safety
