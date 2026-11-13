import CIL.SymbolicExecution
import CIL.StepEquations
import CIL.Safety.Equations
import CIL.Safety.StepComposition
import CIL.Safety.ValueSteps
import CIL.Safety.MemorySteps
import CIL.Safety.ObjectSteps
import CIL.Safety.InstructionSteps
import CIL.Safety.CallComposition
import CIL.Safety.CodeAt
import CIL.Safety.CheckedSide
import CIL.Safety.CheckedMemoryFacts
import CIL.Safety.AggregateMemorySteps
import CIL.Safety.LoopFacts
import CIL.TermAccess
import CIL.Safety.NormalNodes

/-!
# Checked symbolic execution

The stepping tactics for the checked interpreter. `cil_checked_steps [facts]` proves an
`invoke` or `run` goal about a method by fetching each instruction, closing its lookup with
`cil_lookup`, rewriting the step with the `@[cil_step]` equations and the facts, and composing
steps through `run_next`, `run_return` and `run_call_of_invoke`, or `run_fault` toward a stated
fault. Facts are normalised once, at entry, to the form stepping leaves goals in. The contract
and loop tactics, the automation tests and downstream proofs all build on these;
`docs/PROOFS.md` describes their use.
-/

namespace CIL.Safety

/-- Checked local loads use the slot's kind; the opcode annotation adds no second conversion. -/
theorem step_local_annotation (body : CIL.Method) (index : Nat)
    (narrow : Option CIL.NarrowKind) (pc : Nat) (args : List Value) (frame : Frame)
    (stack : List Value) (memory : Memory) :
    step body (.local index narrow) pc args frame stack memory =
      step body (.local index) pc args frame stack memory := rfl

#print axioms step_local_annotation

/-- Checked local stores use the slot's kind independently of the opcode annotation. -/
theorem step_setLocal_annotation (body : CIL.Method) (index : Nat)
    (narrow : Option CIL.NarrowKind) (pc : Nat) (args : List Value) (frame : Frame)
    (stack : List Value) (memory : Memory) :
    step body (.setLocal index narrow) pc args frame stack memory =
      step body (.setLocal index) pc args frame stack memory := by
  cases stack <;> rfl

#print axioms step_setLocal_annotation

open Lean Elab Tactic Conv in
/-- Replaces the focused term by its full reduction; stepping applies it to the goal's fuel. -/
elab "cil_reduce_fuel" : conv => do
  changeLhs (← Meta.reduce (← getLhs))

open Lean Elab Tactic in
/-- Runs `tactic` so that a failed candidate proof fails and can backtrack, rather than be
    recovered as an admitted term. Only the candidate's own errors count, so an earlier failed
    tactic cannot reject it. -/
elab "cil_strict " tactic:tactic : tactic =>
  Meta.withAssignableSyntheticOpaque <| Term.withoutErrToSorry <| withoutRecover do
    let errors := fun (log : MessageLog) =>
      log.reportedPlusUnreported.foldl
        (fun count m => if m.severity matches .error then count + 1 else count) 0
    let earlier := errors (← Core.getMessageLog)
    evalTactic tactic
    if errors (← Core.getMessageLog) > earlier then throwError "Checked step candidate failed"

/-- The projections of a method contract that stepping unfolds in a goal: its argument and
    result encodings, precondition, footprint and postcondition. -/
def contractProjections : List Lean.Name :=
  [`CIL.Safety.MethodContract.args, `CIL.Safety.MethodContract.results,
    `CIL.Safety.MethodContract.pre, `CIL.Safety.MethodContract.footprint,
    `CIL.Safety.MethodContract.post]

open Lean Meta in
/-- `term` with each projection of a defined contract replaced by what the contract's
    definition states for its arguments. A contract that is a variable, as in a rule stated for
    every contract, is left folded, and so is `Returns`, which a proof may restate. -/
def unfoldContractProjections (term : Expr) : MetaM Expr := do
  let named (e : Expr) : Bool := e.getAppFn.constName?.any contractProjections.contains
  -- Most goals name no contract, and are returned without being rebuilt.
  if (term.find? named).isNone then return term
  Meta.transform term (pre := fun e => do
    unless named e do return .continue
    let arguments := e.getAppArgs
    let some contract := arguments[2]? | return .continue
    let defined ← whnf contract
    unless defined.isAppOf `CIL.Safety.MethodContract.mk do return .continue
    let some projection := e.getAppFn.constName? | return .continue
    let some info ← getProjectionFnInfo? projection | return .continue
    let some field := defined.getAppArgs[info.numParams + info.i]? | return .continue
    return .visit (← whnfCore (mkAppN field (arguments.extract 3 arguments.size)).headBeta))

open Lean Elab Tactic Meta in
/-- State the goal with the projections of each defined contract unfolded, as
    `unfoldContractProjections` gives them; a goal that names none is left as it is. -/
elab "cil_unfold_contracts" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let unfolded ← unfoldContractProjections target
  unless unfolded == target do replaceMainGoal [← goal.replaceTargetDefEq unfolded]

open Lean Elab Tactic Meta in
/-- State the goal with `leaveFrame frame memory` as `memory` wherever `frame` is a literal
    frame that owns no allocation; nothing else in the goal changes. -/
elab "cil_frame_exit" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let leaves (e : Expr) : Bool := e.isAppOfArity `CIL.Safety.leaveFrame 2
  if (target.find? leaves).isNone then return
  let exited ← Meta.transform target (pre := fun e => do
    unless leaves e do return .continue
    let #[frame, memory] := e.getAppArgs | return .continue
    let frame ← whnfR frame
    let some #[_, _, owned, _] := argumentsOf? frame `CIL.Safety.Frame.mk 4
      | return .continue
    unless (← whnfR owned).isAppOfArity ``List.nil 1 do return .continue
    return .visit memory)
  unless exited == target do replaceMainGoal [← goal.replaceTargetDefEq exited]

open Lean Elab Tactic Meta in
/-- Open an existential execution budget. Invocation uses the program's execution bound;
    a `run` uses the remaining code of a body identified by a lookup hypothesis. Every
    checked proof must establish that the candidate suffices. A stated fuel term stays fixed. -/
elab "cil_supply_fuel" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOfArity ``Exists 2 do return
  let some (.lam _ _ body _) := lastArgument? target | return
  let some (_, invocation, _) := body.consumeMData.eq? | return
  if let some #[program, .bvar 0, method, pc, _, _, _, _] :=
      argumentsOf? invocation `CIL.Safety.run 8 then
    if program.hasLooseBVars || method.hasLooseBVars || pc.hasLooseBVars then return
    let programTerm ← Term.exprToSyntax program
    let methodTerm ← Term.exprToSyntax method
    let lookup ← Term.elabTerm (← `(term| $programTerm[$methodTerm]?)) none
    for declaration in ← getLCtx do
      let some (_, found, result) := declaration.type.consumeMData.eq? | continue
      let some #[_, definition] := argumentsOf? result ``Option.some 2 | continue
      unless ← withNewMCtxDepth <| isDefEq lookup found do continue
      for placement in ← getLCtx do
        let placed := placement.type.consumeMData
        let some #[placedBody, start, code] := argumentsOf? placed ``CodeAt 3 | continue
        unless ← withNewMCtxDepth <| isDefEq placedBody definition do continue
        unless ← withNewMCtxDepth <| isDefEq start pc do continue
        let segment ← Term.exprToSyntax code
        evalTactic (← `(tactic| refine ⟨(List.length $segment) + 1, ?_⟩))
        return
      let methodBody ← Term.exprToSyntax definition
      let position ← Term.exprToSyntax pc
      evalTactic (← `(tactic| refine ⟨(CIL.Method.code $methodBody).length - $position + 1, ?_⟩))
      return
    return
  let some #[program, fuel, method, _, _] := argumentsOf? invocation `CIL.Safety.invoke 5
    | return
  unless fuel == .bvar 0 && !program.hasLooseBVars && !method.hasLooseBVars do return
  let bound := mkApp2 (mkConst ``CIL.executionBound) program method
  let witness ← Term.exprToSyntax bound
  evalTactic (← `(tactic| refine ⟨$witness, ?_⟩))

/-- `cil_fact_simp (config) [lemmas] [facts]` runs `simp (config) [lemmas, facts]`, adding each
    local fact normalised by the default simp set and the non-local facts. -/
syntax "cil_fact_simp" Lean.Parser.Tactic.optConfig " [" term,* "]" " [" term,* "]" : tactic

-- `trace.CIL.factNormalize` names each local fact that `normaliseStepFacts` normalises.
initialize Lean.registerTraceClass `CIL.factNormalize

open Lean in
/-- Whether `value` is a literal operand the checked state normalizer evaluates. -/
def closedLiteralOperand (value : Expr) : Bool :=
  let literal (value : Expr) := value.isRawNatLit || value.isAppOfArity ``OfNat.ofNat 3
  let numeral (value : Expr) := literal value ||
    (value.isAppOfArity ``BitVec.ofNat 2 && (lastArgument? value).any literal) ||
    (value.isAppOfArity ``BitVec.ofFin 2 && (lastArgument? value).any fun finite =>
      finite.isAppOfArity ``Fin.ofNat 3 && (lastArgument? finite).any literal)
  -- The simprocs need the new width as a literal too, and `ofInt` an integer literal.
  let integer (value : Expr) := literal value || (value.isAppOfArity ``Int.ofNat 1 &&
    (lastArgument? value).any literal) || (value.isAppOfArity ``Neg.neg 3 &&
    (lastArgument? value).any literal)
  (value.isAppOfArity ``BitVec.ofFin 2 && numeral value) ||
    ((value.isAppOfArity ``BitVec.signExtend 3 || value.isAppOfArity ``BitVec.setWidth 3 ||
      value.isAppOfArity ``BitVec.zeroExtend 3) && (argument? value 1).any literal &&
      (lastArgument? value).any numeral) ||
    (value.isAppOfArity ``BitVec.toNat 2 && (lastArgument? value).any numeral) ||
    (value.isAppOfArity ``BitVec.ofInt 2 && (argument? value 0).any literal &&
      (argument? value 1).any integer) ||
    (value.isAppOfArity ``HMod.hMod 6 && (argument? value 5).any numeral &&
      (argument? value 4).any numeral)

open Lean in
/-- Whether an expression contains a literal operand the checked state normalizer evaluates. -/
private def hasClosedLiteralOperand (expression : Expr) : Bool :=
  (expression.find? closedLiteralOperand).isSome

open Lean Meta in
/-- `type` with each closed natural-number argument of a `step` opcode evaluated to a numeral,
    such as the local index `↑(6 : Fin 10) + 1`; a fetched opcode carries numerals, which a
    fact matches only up to instances. The result is definitionally equal to `type`. -/
def evaluateOpcodeIndices (type : Expr) : MetaM Expr := do
  let natType := mkConst ``Nat
  -- Most facts state no step, and are returned without being rebuilt.
  if (type.find? (·.isConstOf ``CIL.Safety.step)).isNone then return type
  Meta.transform type (pre := fun term => do
    unless term.isAppOfArity ``CIL.Safety.step 7 do return .continue
    let some opcode := argument? term 1 | return .continue
    unless opcode.getAppFn.isConst do return .continue
    let mut arguments := opcode.getAppArgs
    for position in [:arguments.size] do
      let some argument := arguments[position]? | continue
      if argument.hasLooseBVars || argument.hasFVar || argument.hasMVar then continue
      if argument.isRawNatLit || (argument.isAppOfArity ``OfNat.ofNat 3 &&
          (argument? argument 1).any Expr.isRawNatLit) then continue
      unless ← isDefEq (← inferType argument) natType do continue
      let some value ← (Lean.Meta.evalNat (← reduce argument)).run | continue
      arguments := arguments.set! position (mkNatLit value)
    if arguments == opcode.getAppArgs then return .continue
    return .continue (mkAppN term.getAppFn
      (term.getAppArgs.set! 1 (mkAppN opcode.getAppFn arguments))))

open Lean Meta in
/-- `term` with each `localResult kind value` that its constructors decide replaced by the value
    a load of that kind pushes, so a loaded `localResult .vector128 (.v128 bits)` reads
    `.v128 bits` as the next fact states it. The result is definitionally equal to `term`, and
    the nodes `leaveAlone` selects, which name no local result, are not entered. -/
def reduceLocalResults (term : Expr) (leaveAlone : Expr → Bool := fun _ => false) :
    MetaM Expr := do
  -- Most goals and facts name no local result, and are returned without being rebuilt.
  let names (candidate : Expr) : Expr.FindStep :=
    if leaveAlone candidate then .done
    else if candidate.isConstOf ``CIL.Safety.localResult then .found else .visit
  if (term.findExt? names).isNone then return term
  Meta.transform term (pre := fun candidate => do
    if leaveAlone candidate then return .done candidate
    unless candidate.isAppOfArity ``CIL.Safety.localResult 2 do return .continue
    let some unfolded ← unfoldDefinition? candidate | return .continue
    let reduced ← whnfCore unfolded
    if lastArgument? candidate == some reduced || reduced.isAppOfArity ``CIL.Value.i32 1 then
      return .visit reduced
    return .continue)

open Lean Elab Tactic Meta in
/-- `proof` and, for a fact over `Fin n` (n <= 64) or over every `Feature`, its instance at
    each value: the profile fields and indexed lemmas are reached only through concrete
    arguments. -/
def factInstances (proof : Expr) : TermElabM (Array Expr) := do
  let mut instances := #[proof]
  if let .forallE _ domain _ _ := ← whnf (← instantiateMVars (← inferType proof)) then
    let domain ← whnf domain
    if let some #[limit] := argumentsOf? domain ``Fin 1 then
      if let some size ← (Lean.Meta.evalNat (← reduce limit)).run then
        if size <= 64 then
          -- Concrete instances avoid simplifying dependent finite binders a second time.
          instances := #[]
          for index in [:size] do
            let numeral : Term := ⟨Syntax.mkNumLit (toString index)⟩
            let bound : Term := ⟨Syntax.mkNumLit (toString size)⟩
            let value ← Term.elabTerm (← `(term| ($numeral : Fin $bound))) (some domain)
            instances := instances.push (mkApp proof value)
    else if domain.isConstOf ``CIL.Feature then
      for ctor in (← getConstInfoInduct ``CIL.Feature).ctors do
        instances := instances.push (mkApp proof (mkConst ctor))
  return instances

open Lean Elab Tactic Meta in
/-- `facts`, followed by hypotheses in default simp and closed-literal normal forms.
    The closed-literal form retains symbolic arithmetic around evaluated literal conversions.
    The goal's subterms
    reach simp-normal form before a hypothesis can rewrite them, so a fact stated in another
    form would never fire; the originals stay in the simp set. Local facts are normalised with
    the supplied non-local facts, and a proof term, or a global theorem about `evaluate` or a
    method's profile, with the other supplied facts. -/
def normaliseStepFacts (config : TSyntax `Lean.Parser.Tactic.optConfig)
    (facts : Array Term) : TacticM (Array Term) := withMainContext do
    let isLocal (fact : Term) : TacticM Bool :=
      return fact.raw.isIdent && ((← getLCtx).findFromUserName? fact.raw.getId).isSome
    let locals ← facts.filterM isLocal
    let supplied ← facts.filterM fun fact => return !(← isLocal fact)
    let mut unfoldNames : Array Name := #[]
    let mut unfolds : Array Term := #[]
    for fact in supplied do
      unless fact.raw.isIdent do continue
      if let some name ← observing? <| realizeGlobalConstNoOverloadWithInfo fact.raw then
        if let .defnInfo _ ← getConstInfo name then
          unfoldNames := unfoldNames.push name
          unfolds := unfolds.push fact
    let mut normalised : Array Term := #[]
    -- Asserts each instance of `proof` in the normaliser's form; the unchanged original is
    -- already a fact.
    let assertInstances (proof : Expr) (base : Name) (ctx : Simp.Context)
        (simprocs : Simp.SimprocsArray) : TacticM (Array Term) := withMainContext do
      let mut names := #[]
      for instanceProof in ← factInstances proof do
        let type ← instantiateMVars (← inferType instanceProof)
        let (result, _) ← simp type ctx simprocs
        let mut results := #[result]
        -- Literal conversions in operation facts must match the state without distributing
        -- symbolic arithmetic, such as the `toNat` of a sum, into the default simp form.
        if hasClosedLiteralOperand type then
          let { ctx := literalContext, simprocs := literalProcs, .. } ←
            mkSimpContext (← `(tactic| simp only [cil_literal])) (eraseLocal := false)
          let (literalResult, _) ← simp type literalContext literalProcs
          if literalResult.expr != type && literalResult.expr != result.expr then
            results := results.push literalResult
        -- Explicit value definitions can expose an operation's symbolic payload without
        -- applying unrelated arithmetic simp lemmas to that payload.
        if (type.find? fun term => term.constName?.any unfoldNames.contains).isSome then
          let { ctx := explicitContext, simprocs := explicitProcs, .. } ←
            mkSimpContext (← `(tactic| simp only [cil_literal, $[$unfolds:term],*]))
              (eraseLocal := false)
          let (explicitResult, _) ← simp type explicitContext explicitProcs
          if explicitResult.expr != type && !results.any (·.expr == explicitResult.expr) then
            results := results.push explicitResult
        -- A step fact is also stated at the numeral of a closed opcode index and at the value
        -- of a decided local result, the forms a stepped goal has.
        for result in results do
          let indexed ← reduceLocalResults (← evaluateOpcodeIndices result.expr)
          if indexed != result.expr && !results.any (·.expr == indexed) then
            let restated ← result.proof?.mapM fun equation => do
              mkExpectedTypeHint equation (← mkEq type indexed)
            results := results.push { expr := indexed, proof? := restated }
        for result in results do
          if result.expr.consumeMData.isConstOf ``True then continue
          if result.expr == type && instanceProof == proof then continue
          let normalisedProof ← match result.proof? with
            | some eq => mkEqMP eq instanceProof
            | none => mkExpectedTypeHint instanceProof result.expr
          let name ← mkFreshUserName base
          let (_, goal) ← (← (← getMainGoal).assert name result.expr normalisedProof).intro1P
          replaceMainGoal [goal]
          names := names.push (mkIdent name)
      return names
    if !locals.isEmpty then
      -- `cil_step` reduces a pushed `evaluate` and a method's profile projection, so facts
      -- must land there too.
      let normaliser ← `(tactic| simp $config:optConfig [cil_guard, CIL.fin_val_three,
        CIL.fin_mk_ofNat, cil_feature, CIL.Safety.reduceMethodProfile, $[$supplied:term],*])
      let { ctx, simprocs, .. } ← mkSimpContext normaliser (eraseLocal := false)
      for fact in locals do
        let some decl := (← getLCtx).findFromUserName? fact.raw.getId | continue
        unless ← isProp (← instantiateMVars decl.type) do continue
        trace[CIL.factNormalize] "{decl.userName}"
        normalised := normalised ++ (← assertInstances decl.toExpr decl.userName ctx simprocs)
    -- A proof term such as `(show p from h)` is normalised like a local fact, without itself
    -- as a lemma, which would rewrite its own statement to `True`. Global names stay as given
    -- (most are unfolds), except theorems about `evaluate` or a method's profile, which
    -- `cil_step` rewrites past.
    for fact in supplied do
      if fact.raw.isIdent then
        let some name ← observing? <| realizeGlobalConstNoOverloadWithInfo fact.raw | continue
        let info ← getConstInfo name
        let mentions := (info.type.find? fun e =>
          e.isConstOf ``CIL.FeatureProfile.evaluate || e.isConstOf ``CIL.Method.profile).isSome
        unless mentions && (← isProp info.type) do continue
      let saved ← saveState
      let some proof ← (try
          let proof ← Term.withoutErrToSorry <| Term.elabTerm fact none
          Term.synthesizeSyntheticMVarsNoPostponing
          let proof ← instantiateMVars proof
          pure (if proof.hasMVar then none else some proof)
        catch _ => pure none) | saved.restore; continue
      unless ← isProp (← instantiateMVars (← inferType proof)) do saved.restore; continue
      let others := supplied.filter (· != fact)
      let normaliser ← `(tactic| simp $config:optConfig [cil_guard, CIL.fin_val_three,
        CIL.fin_mk_ofNat, cil_feature, CIL.Safety.reduceMethodProfile, $[$others:term],*])
      let { ctx, simprocs, .. } ← mkSimpContext normaliser (eraseLocal := false)
      let names ← assertInstances proof `supplied ctx simprocs
      if names.isEmpty then saved.restore; continue
      normalised := normalised ++ names
    return facts ++ normalised

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_fact_simp $config:optConfig [$lemmas:term,*] [$facts:term,*]) => do
    let prepared ← normaliseStepFacts config facts.getElems
    let all := lemmas.getElems ++ #[← `(term| cil_guard), ← `(term| CIL.fin_val_three),
      ← `(term| CIL.fin_mk_ofNat)] ++ prepared
    withMainContext <| evalTactic (← `(tactic| simp $config:optConfig [$[$all:term],*]))

/-- Run `tactic` once, failing with `message` when it does not apply, then repeat it. -/
macro "cil_steps_from " message:str tactic:tacticSeq : tactic =>
  `(tactic| ((first | $tactic | fail $message); repeat $tactic))

/-- Close a method or instruction lookup by evaluation for an extraction, else from a lookup
    hypothesis, else by rewriting feature tests in a profile-dependent body with the supplied
    facts. -/
syntax "cil_lookup" "[" term,* "]" : tactic

open Lean in
/-- The collection and position of the indexed lookup `collection[position]?`; `none` when
    `lookup` is no `GetElem?.getElem?` application with both. -/
private def indexedLookup? (lookup : Expr) : Option (Expr × Expr) :=
  if lookup.isAppOf ``GetElem?.getElem? then
    let arguments := lookup.getAppArgs
    match arguments[arguments.size - 2]?, arguments.back? with
    | some collection, some position => some (collection, position)
    | _, _ => none
  else none

open Lean Elab Tactic Meta in
/-- Reuse a generated equation directly for a named body and a closed instruction position. -/
elab "cil_lookup_equation" : tactic => withMainContext do
  let some (_, lookup, _) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
    | throwError "Expected an instruction lookup"
  let some (code, index) := indexedLookup? lookup | throwError "Expected an indexed lookup"
  unless code.isAppOfArity ``CIL.Method.code 1 do throwError "Expected a named method body"
  let body ← lastArgument "cil_lookup_equation" code
  let some name := body.getAppFn.constName? | throwError "Expected a named method body"
  let some position ← getNatValue? index | throwError "Expected a closed position"
  let equation := name.appendAfter s!"_instruction{position}"
  unless (← getEnv).contains equation do throwError "No generated equation at this position"
  let proof := mkAppN (← mkConstWithFreshMVarLevels equation) body.getAppArgs
  let type ← inferType proof
  let some (_, _, found) := type.eq? | throwError "Expected an instruction equation"
  unless found.isAppOfArity ``Option.some 2 do throwError "Expected a successful lookup"
  let operation ← whnfD (← lastArgument "cil_lookup_equation" found)
  let some (.ctorInfo constructor) := operation.getAppFn.constName?.bind (← getEnv).find?
    | throwError "Instruction needs profile facts"
  unless constructor.induct == instructionTypeName do
    throwError "Expected an instruction constructor"
  let some (_, _, pending) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
    | throwError "Expected an instruction lookup"
  unless ← isDefEq pending (← mkAppM ``Option.some #[operation]) do
    throwError "The instruction equation finds another opcode"
  let goals ← (← getMainGoal).apply proof
  unless goals.isEmpty do throwError "The instruction equation left premises"
  replaceMainGoal []

/-- Close a lookup goal `lookup = result` with a hypothesis, up to reducible unfolding, trying
    only hypotheses that are equations whose left side has the goal's head; fails otherwise. -/
syntax "cil_lookup_assumption" : tactic

open Lean in
/-- The head of the left side of the equation `type` states, under any quantifiers. -/
private def equationHead? : Expr → Option Expr
  | .forallE _ _ body _ => equationHead? body
  | .mdata _ body => equationHead? body
  | type => type.eq?.map fun (_, lhs, _) => lhs.consumeMData.getAppFn

open Lean Elab Tactic Meta in
/-- The hypotheses that state an equation, in context order, with the head of each left side.
    A stepping step reads the list the record holds for its local context, which is found once
    per record; any other call scans the context. -/
private def equationHypotheses : TacticM (Array (FVarId × Expr)) := do
  let usable ← usableNormalNodes
  if let some record := usable then
    if let some found := record.equations then return found
  let mut found := #[]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    if let some head := equationHead? (← instantiateMVars declaration.type) then
      found := found.push (declaration.fvarId, head)
  if let some record := usable then
    setNormalNodes { record with equations := some found }
  return found

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_lookup_assumption) => withMainContext do
    let goal ← getMainGoal
    let some wanted := equationHead? (← instantiateMVars (← goal.getType))
      | throwError "cil_lookup_assumption: the goal is not an equation"
    for (hypothesis, found) in ← equationHypotheses do
      -- A head that is not a constant may unify with anything, so every hypothesis is tried.
      unless !wanted.isConst || !found.isConst || found == wanted do continue
      let declaration ← hypothesis.getDecl
      let saved ← saveState
      if declaration.type.isForall then
        try
          let remaining ← withReducible <| goal.apply declaration.toExpr
          if remaining.isEmpty then replaceMainGoal []; return
        catch _ => pure ()
        saved.restore
        continue
      if ← withReducible (isDefEq (← goal.getType) declaration.type) then
        goal.assign declaration.toExpr
        replaceMainGoal []
        return
      saved.restore
    throwError "cil_lookup_assumption: no hypothesis states this lookup"

/-- A lookup that finds `a` finds every `b` equal to it. -/
theorem lookup_eq_some_of_eq {α : Type u} {lookup : Option α} {a b : α}
    (found : lookup = some a) (reduced : a = b) : lookup = some b := by subst reduced; exact found

#print axioms lookup_eq_some_of_eq

/-- Close `l[i]? = some x`, or a lookup a `@[cil_code]` equation already rewrote to
    `some op = some x`, by `rfl`, deciding a fetched feature `if` with `facts` first so the
    op is a constructor and its step equation applies. -/
syntax "cil_lookup_rfl" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_lookup_rfl [$facts:term,*]) => withMainContext do
    let goal ← getMainGoal
    let saved ← saveState
    evalTactic (← `(tactic| rfl))
    let some (_, lookup, found) := (← instantiateMVars (← goal.getType)).eq? | return
    let some #[_, instruction] := argumentsOf? found ``Option.some 2 | return
    let op ← whnfR instruction
    let isFeatureTest (e : Expr) := e.isAppOf ``ite || e.isAppOf ``dite || e.isAppOf ``cond
    unless isFeatureTest op do return
    let fetched ← saveState
    saved.restore
    -- Built as a term: `refine` cannot assign the caller's op metavariable inside a term-mode
    -- `by`.
    try
      let decide ← `(tactic| simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self_iff_true,
        ite_true, ite_false, dite_true, dite_false, Bool.cond_true, Bool.cond_false, ↓reduceIte,
        ↓reduceDIte, $[$facts:term],*])
      let { ctx, simprocs, .. } ← mkSimpContext decide (eraseLocal := false)
      let (reduced, _) ← simp op ctx simprocs
      if isFeatureTest (← whnfR reduced.expr) then throwError "The feature test was not decided"
      let some (_, _, pending) := (← instantiateMVars (← goal.getType)).eq?
        | throwError "Unexpected lookup"
      unless ← isDefEq pending (← mkAppM ``Option.some #[reduced.expr]) do
        throwError "Unexpected lookup"
      let fetchedOp ← mkExpectedTypeHint (← mkEqRefl lookup)
        (← mkEq lookup (← mkAppM ``Option.some #[op]))
      goal.assign (← mkAppM ``CIL.Safety.lookup_eq_some_of_eq #[fetchedOp, ← reduced.getProof])
      replaceMainGoal []
    catch _ => fetched.restore

/-- Close an instruction lookup from a placed segment, without unfolding the abstract body. -/
syntax "cil_lookup_placed" "[" term,* "]" : tactic

open Lean Meta in
/-- Recognize a natural-number position as a literal offset after a segment's start. -/
private partial def placementOffset (start position : Expr) : MetaM Nat := do
  if ← isDefEq position start then return 0
  if let some positionValue ← getNatValue? position then
    if let some startValue ← getNatValue? start then
      if startValue ≤ positionValue then return positionValue - startValue
  if position.isAppOf ``HAdd.hAdd || position.isAppOfArity ``Nat.add 2 then
    let arguments := position.getAppArgs
    if let (some base, some offset) := (arguments[arguments.size - 2]?, arguments.back?) then
      if let some amount ← getNatValue? offset then
        return (← placementOffset start base) + amount
  throwError "The position is not a literal offset from this placement"

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_lookup_placed [$facts:term,*]) => withMainContext do
    let original ← saveState
    let mut placements : Array Expr := #[]
    for declaration in ← getLCtx do
      if declaration.type.isAppOfArity ``CodeAt 3 then
        placements := placements.push declaration.toExpr
    for fact in facts.getElems do
      let saved ← saveState
      try
        let proof ← Term.withoutErrToSorry <| Term.elabTerm fact none
        let type ← instantiateMVars (← inferType proof)
        if type.isAppOfArity ``CodeAt 3 then placements := placements.push proof
        else saved.restore
      catch _ => saved.restore
    for placement in placements do
      let saved ← saveState
      try
        -- A fact from an untyped `have` states its type through an assigned metavariable.
        let type ← instantiateMVars (← inferType placement)
        let start ← argumentAt "cil_lookup_placed" type 1
        let some (_, lookup, _) := (← getMainTarget).consumeMData.eq?
          | throwError "Expected an instruction lookup"
        let position ← lastArgument "cil_lookup_placed" lookup
        let index ← placementOffset start position
        let placedTerm ← Term.exprToSyntax placement
        let indexTerm : Term := ⟨Syntax.mkNumLit (toString index)⟩
        evalTactic (← `(tactic| cil_strict
          (simpa only [Nat.add_assoc, Nat.add_zero, Nat.reduceAdd] using
            (CodeAt.lookup $placedTerm $indexTerm rfl))))
        return
      catch _ => saved.restore
    original.restore
    throwError "No placed segment contains this instruction"

/-- Resolve a computed lookup by checking each value of a bounded finite index. -/
syntax "cil_lookup_finite" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_lookup_finite [$facts:term,*]) => withMainContext do
    let some (_, lookup, _) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
      | throwError "Expected a lookup equation"
    let some (_, position) := indexedLookup? lookup | throwError "Expected an indexed lookup"
    for declaration in ← getLCtx do
      unless (position.find? (· == declaration.toExpr)).isSome do continue
      let type ← whnf declaration.type
      let some #[limit] := argumentsOf? type ``Fin 1 | continue
      let some size ← (Lean.Meta.evalNat (← reduce limit)).run | continue
      unless size > 0 && size <= 64 do continue
      let index ← Term.exprToSyntax declaration.toExpr
      let value ← `(term| ($index).val)
      let rec splitAt (offset : Nat) (remaining : Nat) : TacticM (TSyntax `tactic) := do
        let numeral : Term := ⟨Syntax.mkNumLit (toString offset)⟩
        let equal := mkIdent (← mkFreshUserName `positionCase)
        let close ← `(tactic| (
          simp only [$equal:term, Nat.reduceMul, Nat.reduceAdd]
          all_goals first | cil_lookup_equation | cil_lookup [$[$facts:term],*]))
        match remaining with
        | 0 => `(tactic| (
            have $equal : $value = $numeral := by omega
            $close:tactic))
        | rest + 1 =>
          let tail ← splitAt (offset + 1) rest
          `(tactic| (by_cases $equal : $value = $numeral
                     · ($close:tactic)
                     · ($tail:tactic)))
      evalTactic (← splitAt 0 (size - 1))
      return
    throwError "No computed position with a finite bound of at most 64"

open Lean Elab Tactic Meta in
/-- Report a closed position outside a concrete instruction list without hiding its bounds. -/
elab "cil_lookup_failure" : tactic => do
  if (← getGoals).isEmpty then return
  withMainContext do
  if let some (_, lookup, _) := (← instantiateMVars (← getMainTarget)).consumeMData.eq? then
    if let some (collection, index) := indexedLookup? lookup then
      if let some position ← (Lean.Meta.evalNat (← reduce index)).run then
        let length ← mkAppM ``List.length #[collection]
        if let some count ← (Lean.Meta.evalNat (← reduce length)).run then
          if count <= position then
            throwError "cil_lookup: position {position} is outside body length {count}"
  evalTactic (← `(tactic| rfl))

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_lookup [$facts:term,*]) => withMainContext do
    let attempt (tactic : TSyntax `tactic) : TacticM Bool := do
      let saved ← saveState
      try evalTactic tactic; return true
      catch _ => saved.restore; return false
    if ← attempt (← `(tactic| cil_lookup_assumption)) then return
    if ← attempt (← `(tactic| cil_lookup_equation)) then return
    let some (_, lookup, _) := (← instantiateMVars (← getMainTarget)).consumeMData.eq?
      | throwError "Expected a lookup equation"
    if !lookup.hasFVar && !lookup.hasMVar then
      evalTactic (← `(tactic| cil_try_simp_only [cil_code, Nat.reduceAdd, Nat.reduceMul]))
      pruneSolvedGoals
      if (← getGoals).isEmpty then return
      if ← attempt (← `(tactic| cil_lookup_rfl [$facts:term,*])) then return
      evalTactic (← `(tactic| cil_lookup_failure))
      return
    if let some (_, position) := indexedLookup? lookup then
      let mut finite := false
      let mut placed := false
      for declaration in ← getLCtx do
        placed := placed || (declaration.type.find? (·.isAppOfArity ``CodeAt 3)).isSome
        if (position.find? (· == declaration.toExpr)).isSome then
          finite := finite || (← whnf declaration.type).isAppOfArity ``Fin 1
      if placed && (← attempt (← `(tactic| cil_lookup_placed [$facts:term,*]))) then return
      if finite && (← attempt (← `(tactic| cil_lookup_finite [$facts:term,*]))) then return
    evalTactic (← `(tactic| cil_try_simp_only [cil_code, Nat.reduceAdd, Nat.reduceMul,
      bne_iff_ne, ne_eq, not_false_eq_true, Bool.false_eq_true, ite_true, ite_false,
      ↓reduceIte, $[$facts:term],*]))
    pruneSolvedGoals
    if (← getGoals).isEmpty then return
    -- No instruction is fetched at a branch the facts left undecided; evaluating the lookup
    -- there would unfold the condition's decision procedure on symbolic operands.
    if let some (_, pending, _) := (← instantiateMVars (← getMainTarget)).consumeMData.eq? then
      if let some (_, position) := indexedLookup? pending then
        let position := position.consumeMData
        if (position.isAppOfArity ``ite 5 || position.isAppOfArity ``dite 5) &&
            (argument? position 1).any Expr.hasFVar then
          throwError "cil_lookup: undecided branch {position}; split on its condition"
    if ← attempt (← `(tactic| cil_lookup_rfl [$facts:term,*])) then return
    evalTactic (← `(tactic| cil_lookup_failure))

-- The closed literal operands every stepping tactic evaluates, so a state reads the same
-- whichever tactic produced it. Each is a simproc that fires on numerals only.
open Lean Meta in
/-- Restore a closed bit-vector constructor to the numeral form used by Lean's simprocs. -/
dsimproc_decl closedBitVecConstructor (BitVec.ofFin _) := fun expression => do
  let some widthTerm := argument? expression 0 | return .continue
  let some width ← getNatValue? widthTerm | return .continue
  let some finite := lastArgument? expression | return .continue
  let some #[_, _, valueTerm] := argumentsOf? finite ``Fin.ofNat 3 | return .continue
  let some value ← getNatValue? valueTerm | return .continue
  return .done (mkApp2 (mkConst ``BitVec.ofNat) (toExpr width) (toExpr value))

attribute [cil_literal_proc] closedBitVecConstructor
attribute [cil_literal_proc] BitVec.reduceSignExtend BitVec.reduceSetWidth
  BitVec.reduceZeroExtend BitVec.reduceToNat BitVec.reduceOfInt Nat.reduceMod

open Lean Elab Tactic Meta in
/-- Evaluate the closed literal operands of the goal with the `cil_literal` set: a width
    conversion, sign extension or `toNat` of a bit-vector numeral, and a remainder of numerals,
    as a masked shift count is. A goal with none is left untouched, so a step pays for the
    normalisation only when its state has such an operand; never fails. -/
elab "cil_literal_operands" : tactic => do
  -- A step that closed its goal leaves nothing to normalise.
  if (← getGoals).isEmpty then return
  withMainContext do
  let name := "cil_literal_operands"
  let target ← instantiateMVars (← getMainTarget)
  let found ← if (← usableNormalNodes).isNone then pure (hasClosedLiteralOperand target)
    else do
      let (found, (_, clean)) :=
        (cleanWalk closedLiteralOperand (← normalNodesFor name) target).run ({}, #[])
      -- The terms below which no operand occurs stay so, whatever the step does next.
      recordNormalNodes name clean
      pure found
  if found then evalTactic (← `(tactic| cil_try_simp_only [cil_literal]))

open Lean Elab Tactic Meta in
/-- State the goal with each decided `localResult` as the value it loads as
    (`reduceLocalResults`); a goal with none is left untouched. Never fails. -/
elab "cil_local_results" : tactic => do
  if (← getGoals).isEmpty then return
  withMainContext do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let name := "cil_local_results"
    let known ← normalNodesFor name
    let isLocalResult (term : Expr) := term.isConstOf ``CIL.Safety.localResult
    let found ← if (← usableNormalNodes).isNone then pure (target.find? isLocalResult).isSome
      else do
        let (found, (_, clean)) := (cleanWalk isLocalResult known target).run ({}, #[])
        recordNormalNodes name clean
        pure found
    if found then
      let reduced ← reduceLocalResults target known.contains
      unless reduced == target do replaceMainGoal [← goal.replaceTargetDefEq reduced]

/-- Normalises the literal `take`, `drop`, `reverse` and `++` a step leaves on the stack,
    evaluates its closed literal operands (`cil_literal_operands`) and states each decided local
    result as its value (`cil_local_results`); never fails. -/
macro "cil_stack_cleanup" : tactic =>
  `(tactic| (
    cil_try_simp_only [List.drop_succ_cons, List.drop_zero, List.drop_nil,
      List.take_succ_cons, List.take_zero, List.take_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.append_nil]
    cil_literal_operands
    cil_local_results))

/-- Closes a checked `step` goal by rewriting with the `@[cil_step]` and
    `@[cil_instruction_step]` equations, failing if nothing rewrites, then by the checked-value
    definitions and `facts`, constructors and `rfl`. -/
macro "cil_checked_step_by_equations " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       cil_simp_only [cil_instruction_step, cil_step, cil_guard, CIL.Safety.instructionStep]
       cil_try_simp_only [cil_guard, cil_checked, cil_side, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

/-- A matching instruction fact closes a step through its generic `@[cil_step]` equation.
    Keeping the step at `instruction` lets the supplied fact apply before a per-shape equation
    rewrites past it; the opcode need not have a per-shape `@[cil_instruction_step]` equation. -/
macro "cil_checked_instruction_from_fact " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       cil_simp_only [cil_step, cil_guard, CIL.Safety.instructionStep]
       cil_try_simp_only [cil_guard, cil_checked, cil_side, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

/-- `cil_checked_step_by_equations` for a `.memory` step, also rewriting `referenceAt` on
    `.null` and `.address`. Only memory equations expose `referenceAt`; its equations in the
    generic list would slow every other step. -/
macro "cil_checked_memory_by_equations " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       cil_simp_only [cil_step, cil_guard, CIL.Safety.instructionStep]
       cil_try_simp_only [cil_guard, cil_checked, cil_side, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

/-- Normalize checked conditions with the shared closed rules, retaining unresolved goals. -/
macro "cil_checked_normalize " "[" facts:term,* "]" : tactic =>
  `(tactic| cil_try_simp_only [cil_checked, cil_guard, cil_side, $[$facts:term],*])

/-- Closes frame-entry and return premises with the closed checked-value rules and supplied
    facts. Returned objects retain formation when the exiting frame does not own them. -/
macro "cil_checked_side " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       try rfl
       all_goals cil_frame_exit
       all_goals cil_checked_normalize [$[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

open Lean Meta in
/-- Spell a literal `BitVec.ofNat n k` as the numeral `k`, as an evaluation fact with a literal
    operand states it; a symbolic `BitVec.ofNat n x` keeps its spelling so later facts on it
    still match. -/
dsimproc_decl bitVecOfNatLiteral (BitVec.ofNat _ _) := fun e => do
  let_expr BitVec.ofNat width operand ← e | return .continue
  let some value ← getNatValue? operand | return .continue
  return .done (← mkNumeral (mkApp (mkConst ``BitVec) width) value)

/-- Succeed only when the goal still mentions intrinsic evaluation. -/
elab "cil_intrinsic_pending" : tactic => Lean.Elab.Tactic.withMainContext do
  let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
  unless (target.find? fun e =>
      e.isConstOf ``CIL.evalIntrinsic || e.isConstOf ``CIL.Safety.checkedIntrinsic).isSome do
    Lean.throwError "No pending intrinsic evaluation"

/-- Closes a checked step through the opcode equations without recovering failed subproofs. -/
macro "cil_checked_step_equations " "[" facts:term,* "]" : tactic =>
  `(tactic| cil_strict (cil_checked_step_by_equations [$[$facts:term],*]))

/-- Closes a memory step with a matching supplied operation fact. Memory-dispatch facts
    select the static dispatch equation explicitly before this tactic runs. -/
macro "cil_checked_memory_from_fact " "[" facts:term,* "]" : tactic =>
  `(tactic| (
       rw [CIL.Safety.step_memory_eq]
       cil_try_simp_only [cil_guard]
       cil_try_simp_only [cil_guard, cil_checked, cil_side, $[$facts:term],*]
       all_goals ((repeat constructor) <;> rfl)))

open Lean Elab Tactic Meta in
/-- Whether a supplied fact's type satisfies `test`: a hypothesis, a constant, or an applied
    term that is elaborated, tested and then discarded, since `test` may meet its fresh
    metavariables. -/
def suppliedFactSatisfies (fact : Term) (test : Expr → MetaM Bool) : TacticM Bool := do
  if fact.raw.isIdent then
    match (← getLCtx).findFromUserName? fact.raw.getId with
    | some decl => test (← instantiateMVars decl.type)
    | none =>
      try test (← getConstInfo (← resolveGlobalConstNoOverload fact.raw)).type
      catch _ => return false
  else
    let saved ← saveState
    try test (← instantiateMVars (← inferType (← Term.withoutErrToSorry (Term.elabTerm fact none))))
    catch _ => return false
    finally saved.restore

open Lean Meta in
/-- Whether `e` contains a numeral whose type reduces to `BitVec n`, such as `(27 : W32)`. -/
partial def hasBitVecNumeral (e : Expr) : MetaM Bool := do
  if let some #[type, _, _] := argumentsOf? e ``OfNat.ofNat 3 then
    if !type.hasLooseBVars then
      if (← whnfR type).isAppOf ``BitVec then return true
  e.foldlM (fun found child => if found then pure true else hasBitVecNumeral child) false

/-- Succeed only when a supplied fact concludes `evalIntrinsic ... = _` with a numeral `BitVec`
    operand. -/
syntax "cil_numeral_eval_fact" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_numeral_eval_fact [$facts:term,*]) => withMainContext do
    for fact in facts.getElems do
      let found ← suppliedFactSatisfies fact fun type => forallTelescope type fun _ conclusion => do
        let some (_, lhs, _) := conclusion.eq? | return false
        unless lhs.isAppOf ``CIL.evalIntrinsic || lhs.isAppOf ``CIL.Safety.checkedIntrinsic do
          return false
        hasBitVecNumeral lhs
      if found then return
    throwError "No supplied evaluation fact with a numeral operand"

/-- Closes a checked intrinsic step: decides availability and the operand count, evaluates
    with the `@[cil_eval]` lemmas and `facts`, then closes the residue by `rfl` or the step
    equations. When a supplied evaluation fact has a numeral operand, the goal's literal
    operands are respelled as numerals to match it. -/
macro "cil_checked_intrinsic " "[" facts:term,* "]" : tactic =>
  `(tactic| (
    cil_simp_only [cil_step, cil_guard, CIL.Intrinsic.available, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceLT, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ite_false, ite_true, List.take_succ_cons, List.take_zero, List.take_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.append_nil,
      List.drop_succ_cons, List.drop_zero, List.drop_nil, CIL.Safety.scalars,
      CIL.Safety.numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure,
      BitVec.ofInt_ofNat, cil_eval, $[$facts:term],*]
    -- A fact that makes the intrinsic fault leaves no result for this pass to check.
    all_goals cil_try_simp_only [CIL.Safety.checkedIntrinsic, cil_guard, cil_eval,
      List.any_cons, List.any_nil, Bool.false_or, Bool.true_or, Bool.or_false,
      Bool.false_eq_true, ite_false, CIL.Safety.checkedValue, CIL.Safety.numericValue, ite_true,
      Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
    -- `rfl` would evaluate a residue definitionally and push a value no later fact matches.
    -- Operands arrive as `BitVec.ofNat n k`, which only a supplied fact stated with a numeral
    -- `k` needs respelled; facts are splice-last.
    all_goals try (
         cil_numeral_eval_fact [$[$facts:term],*]
         cil_intrinsic_pending
         cil_simp_only [bitVecOfNatLiteral, CIL.Safety.checkedIntrinsic, cil_guard, cil_eval,
           List.any_cons, List.any_nil, Bool.false_or, Bool.true_or, Bool.or_false,
           Bool.false_eq_true, ite_false, CIL.Safety.checkedValue, CIL.Safety.numericValue,
           ite_true, Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
         fail_if_success cil_intrinsic_pending)
    all_goals cil_checked_side [$[$facts:term],*]))

open Lean Meta in
/-- The opcode constructor `op` denotes, when its head reduces to one: a body that picks an
    opcode with a decided `if` would otherwise match no step equation and unfold the whole
    dispatcher. -/
def cilReducedOp? (op : Expr) : MetaM (Option Expr) := do
  let reduced ← whnfD (← instantiateMVars op)
  let some name := reduced.getAppFn.constName? | return none
  let some (.ctorInfo info) := (← getEnv).find? name | return none
  return if info.induct == instructionTypeName then some reduced else none

/-- One checked `step` goal, with facts already normalised: a supplied step fact for the
    fetched op, as given or with its `@[cil_code]` bodies unfolded, or else a strategy chosen
    by opcode and the kind of its supplied operation facts. -/
syntax "cil_checked_step_normalized" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
/-- Equations selected inside quantified conjunctions retain their original binders. -/
private partial def equationConjuncts (select : Expr → Bool) (proof : Expr) :
    MetaM (Array Expr) := do
  -- A hypothesis from `have name := term` states its type through an assigned metavariable.
  forallTelescope (← instantiateMVars (← inferType proof)) fun variables conclusion => do
    if conclusion.isAppOfArity ``And 2 then
      let applied := mkAppN proof variables
      let left ← equationConjuncts select (← mkAppM ``And.left #[applied])
      let right ← equationConjuncts select (← mkAppM ``And.right #[applied])
      (left ++ right).mapM (mkLambdaFVars variables)
    else
      let some (_, lhs, _) := conclusion.consumeMData.eq? | return #[]
      return if select lhs then #[proof] else #[]

open Lean Elab Tactic Meta in
/-- The supplied facts that state a `step` result for the goal's op, or for any op. -/
def stepFacts (target : Expr) (facts : Array Term) : TacticM (Array Term) := do
  -- A tactic `have` leaves the target under `mdata`, which `Expr.eq?` does not see through.
  let target := (← instantiateMVars target).consumeMData
  let some (_, lhs, _) := target.eq? | return #[]
  let some #[body, opcode, _, _, _, _, _] := argumentsOf? lhs ``CIL.Safety.step 7 | return #[]
  let head := (← whnfR opcode).getAppFn.constName?
  let states (type : Expr) : MetaM Bool := withNewMCtxDepth do
    let openParameters := type.hasMVar
    let (_, _, conclusion) ← forallMetaTelescopeReducing type
    let some (_, factLhs, _) := conclusion.eq? | return false
    let some #[_, factOpcode, _, _, _, _, _] := argumentsOf? factLhs ``CIL.Safety.step 7
      | return false
    match (← whnfR factOpcode).getAppFn.constName?, head with
    | some factHead, some goalHead => unless factHead == goalHead do return false
    | _, _ => pure ()
    if openParameters then return true
    -- A named body may need its generated equation unfolded before application.
    let mut arguments := factLhs.getAppArgs |>.set! 0 body
    let operation ← whnfR factOpcode
    if operation.isAppOfArity ``CIL.Instruction.local 2 ||
        operation.isAppOfArity ``CIL.Instruction.setLocal 2 then
      let some index := argument? operation 0 | return false
      arguments := arguments.set! 1
        (mkApp2 operation.getAppFn index
          (mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``CIL.NarrowKind)))
    withTransparency .instances <| isDefEq (mkAppN factLhs.getAppFn arguments) lhs
  let mut matching := #[]
  for fact in facts do
    if ← suppliedFactSatisfies fact states then
      matching := matching.push fact
    else if ← suppliedFactSatisfies fact (fun type => forallTelescope type fun _ conclusion =>
        pure (conclusion.isAppOfArity ``And 2)) then
      let proof ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm fact none
      for part in ← equationConjuncts (·.isAppOfArity ``CIL.Safety.step 7) proof do
        if ← states (← inferType part) then
          matching := matching.push (← Term.exprToSyntax part)
  return matching

open Lean Elab Tactic Meta in
/-- Close the goal with `fact` after normalizing named bodies and local annotations in its type.
    Fails when the supplied normalization does not change the type. -/
def applyUnfoldedStepFact (unfold : Simp.Context) (simprocs : Simp.SimprocsArray) (fact : Term) :
    TacticM Unit := withMainContext do
  let proof ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm fact none
  let type ← instantiateMVars (← inferType proof)
  let (result, _) ← simp type unfold simprocs
  if result.expr == type then throwError "The step fact needs no body or annotation normalization"
  let proof ← match result.proof? with
    | some eq => mkEqMP eq proof
    | none => mkExpectedTypeHint proof result.expr
  let goals ← withTransparency .instances <| (← getMainGoal).apply proof
  unless goals.isEmpty do throwError "The step fact left goals"
  replaceMainGoal []

open Lean Elab Tactic Meta in
/-- Match one dispatch equation, retaining quantified facts and conjunction-wrapped facts. -/
private partial def dispatchFactMatches (wanted : Expr) (function : Name) (type : Expr) :
    MetaM Bool := withNewMCtxDepth do
  let (_, _, conclusion) ← forallMetaTelescopeReducing type
  if let some #[left, right] := argumentsOf? conclusion ``And 2 then
    return (← dispatchFactMatches wanted function left) ||
      (← dispatchFactMatches wanted function right)
  let some (_, lhs, _) := conclusion.consumeMData.eq? | return false
  unless lhs.isAppOf function do return false
  withTransparency .instances <| isDefEq lhs wanted

open Lean Elab Tactic Meta in
/-- Supplied dispatch facts for this operation, stack and memory, including facts inside a
    conjunction. Matching fresh quantified variables never instantiates the caller's goal. -/
def dispatchFacts (step : Expr) (function : Name) (facts : Array Term) :
    TacticM (Array Term) := do
  let arguments := step.getAppArgs
  let (some body, some opcode, some pc, some stack, some memory) :=
      (arguments[0]?, arguments[1]?, arguments[2]?, arguments[5]?, arguments[6]?)
    | return #[]
  let operation ← whnfR opcode
  let wanted ← if function == ``CIL.Safety.instruction then
      mkAppM function #[operation, stack, memory]
    else if let some operand := lastArgument? operation then
      if function == ``CIL.Safety.staticInstruction then
        mkAppM function #[body, pc, operand, stack, memory]
      else mkAppM function #[operand, stack, memory]
    else return #[]
  facts.filterM (suppliedFactSatisfies · (dispatchFactMatches wanted function))

open Lean Meta in
/-- Expose a concrete stack spine without reducing the values carried by its cells. -/
private partial def exposeStackSpine (stack : Expr) : MetaM Expr := withIncRecDepth do
  let reduced ← whnfD stack
  if reduced.isAppOfArity ``List.nil 1 then return reduced
  unless reduced.isAppOfArity ``List.cons 3 do return stack
  let .app withHead tail := reduced | return stack
  return mkApp withHead (← exposeStackSpine tail)

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_checked_step_normalized [$facts:term,*]) => withMainContext do
    let initial := (← instantiateMVars (← getMainTarget)).consumeMData
    let mut localOperation := false
    if let some (_, step, _) := initial.eq? then
      if step.isAppOfArity ``CIL.Safety.step 7 &&
          (argument? step 1).any (·.isConstOf ``CIL.Instruction.nop) then
        evalTactic (← `(tactic| exact step_nop_eq ..))
        return
      if let some #[_, opcode, _, _, _, _, _] := argumentsOf? step ``CIL.Safety.step 7 then
        let operation ← whnfR opcode
        localOperation := operation.isAppOfArity ``CIL.Instruction.local 2 ||
          operation.isAppOfArity ``CIL.Instruction.setLocal 2
        if localOperation then
          let narrow ← lastArgument "cil_checked_step_normalized" operation
          unless (← whnfR narrow).isAppOf ``Option.none do
            evalTactic (← `(tactic|
              cil_simp_only [step_local_annotation, step_setLocal_annotation]))
            if (← getGoals).isEmpty then return
    -- A body reached through a lookup hypothesis stays named; one reached by unfolding a
    -- `cil_code` program is already a literal, so a fact on the named body needs its own
    -- `cil_code` unfolded to match it.
    let candidates ← stepFacts (← getMainTarget) facts.getElems
    for fact in candidates do
      let saved ← saveState
      try
        evalTactic (← `(tactic| cil_strict ((with_reducible_and_instances apply $fact); done)))
        return
      catch _ => saved.restore
    if !candidates.isEmpty then
      let normalize ← if localOperation then
          `(tactic| simp only [cil_code, step_local_annotation, step_setLocal_annotation])
        else `(tactic| simp only [cil_code])
      let { ctx, simprocs, .. } ← mkSimpContext normalize (eraseLocal := false)
      for fact in candidates do
        let saved ← saveState
        try
          applyUnfoldedStepFact ctx simprocs fact
          return
        catch _ => saved.restore
    if let some (_, pending, _) := (← instantiateMVars (← getMainTarget)).consumeMData.eq? then
      let opcodeHead := (argument? pending 1).bind (·.getAppFn.constName?)
      if pending.isAppOfArity ``CIL.Safety.step 7 &&
          opcodeHead.any
            ([``CIL.Instruction.brfalse, ``CIL.Instruction.brtrue, ``CIL.Instruction.beq,
              ``CIL.Instruction.bne_un, ``CIL.Instruction.blt, ``CIL.Instruction.blt_un,
              ``CIL.Instruction.ble, ``CIL.Instruction.ble_un, ``CIL.Instruction.bgt,
              ``CIL.Instruction.bgt_un, ``CIL.Instruction.bge,
              ``CIL.Instruction.bge_un].contains ·) then
        -- A matching truth equation must rewrite before its definition can erase that head.
        let mut truthDefinitions : Array Term := #[← `(term| CIL.truth)]
        if opcodeHead.any ([``CIL.Instruction.brfalse, ``CIL.Instruction.brtrue].contains ·) then
          let stackTerm ← argumentAt "cil_checked_step_normalized" pending 5
          let stack ← whnfD stackTerm
          if let some #[_, value, _] := argumentsOf? stack ``List.cons 3 then
            if let some #[scalar] := argumentsOf? value ``Value.scalar 1 then
              let wanted ← mkAppM ``CIL.truth #[scalar]
              for fact in facts.getElems do
                if ← suppliedFactSatisfies fact (dispatchFactMatches wanted ``CIL.truth) then
                  truthDefinitions := #[]
                  break
        let branchFacts := truthDefinitions ++ facts.getElems
        -- Decide a branch before reflexivity can assign its unknown next pc a conditional.
        -- Numerals use the same spelling as the normalized branch facts, and a comparison of
        -- two numerals is decided, so a literal operand leaves a numeral pc.
        evalTactic (← `(tactic| cil_strict (
          cil_simp_only [cil_code, Nat.reduceAdd, cil_step, cil_guard, cil_checked, cil_side,
            BitVec.ofNat_eq_ofNat, BitVec.setWidth_ofNat_of_le, Nat.reduceLeDiff,
            BitVec.reduceEq, ↓reduceIte, $[$branchFacts:term],*]
          all_goals ((repeat constructor) <;> rfl))))
        return
    evalTactic (← `(tactic| cil_try_simp_only [cil_code, Nat.reduceAdd]))
    if (← getGoals).isEmpty then return
    -- A tactic `have` leaves the target under `mdata`, which `Expr.eq?` does not see through.
    let mut target := (← instantiateMVars (← getMainTarget)).consumeMData
    let some (_, lhs, rhs) := target.eq? | throwError "Expected a checked step equality"
    let mut args := lhs.getAppArgs
    let mut operation := Name.anonymous
    if let some #[_, opcode, _, _, _, stack, _] := argumentsOf? lhs ``CIL.Safety.step 7 then
      -- Contract result projections may hide the stack constructor needed by a step equation.
      args := args.set! 5 (← exposeStackSpine stack)
      if let some op ← cilReducedOp? opcode then
        let .const name _ := op.getAppFn
          | throwError "cil_checked_step_normalized: expected an opcode constructor, but \
              found{indentExpr op}"
        operation := name
        args := args.set! 1 op
      unless args == lhs.getAppArgs do
        target ← mkEq (mkAppN lhs.getAppFn args) rhs
        replaceMainGoal [← (← getMainGoal).replaceTargetDefEq target]
    let checkedArithmetic := [``CIL.Instruction.add_ovf, ``CIL.Instruction.add_ovf_un,
      ``CIL.Instruction.sub_ovf, ``CIL.Instruction.sub_ovf_un, ``CIL.Instruction.mul_ovf,
      ``CIL.Instruction.mul_ovf_un].contains operation
    let checkedOperation := if checkedArithmetic then
        some (``CIL.checkedValues, ``CIL.Safety.step_checked_result)
      else if operation == ``CIL.Instruction.checkedConvert then
        some (``CIL.convertInteger, ``CIL.Safety.step_checkedConvert_result)
      else none
    if let some (function, bridge) := checkedOperation then
      for fact in facts.getElems do
        unless ← suppliedFactSatisfies fact (fun type => forallTelescope type fun _ conclusion => do
            let some (_, left, _) := conclusion.eq? | return false
            return left.isAppOf function) do continue
        let saved ← saveState
        try
          let lemma := mkIdent bridge
          -- The goal fixes the constructor, so its flags are decided once `apply` unifies.
          let bridged ← if checkedArithmetic then
              `(tactic| (apply $lemma (calculated := $fact); case selected => rfl))
            else `(tactic| apply $lemma $fact)
          evalTactic (← `(tactic| cil_strict (
            $bridged:tactic
            all_goals cil_checked_side [])))
          return
        catch _ => saved.restore
    let scalar := #[``CIL.Instruction.neg, ``CIL.Instruction.cgt, ``CIL.Instruction.conv_i1,
      ``CIL.Instruction.conv_i2, ``CIL.Instruction.conv_u2, ``CIL.Instruction.conv_i8,
      ``CIL.Instruction.conv_i4, ``CIL.Instruction.conv_u1, ``CIL.Instruction.conv_u4,
      ``CIL.Instruction.conv_u8, ``CIL.Instruction.conv_u, ``CIL.Instruction.not,
      ``CIL.Instruction.add, ``CIL.Instruction.sub, ``CIL.Instruction.mul,
      ``CIL.Instruction.and, ``CIL.Instruction.or, ``CIL.Instruction.xor,
      ``CIL.Instruction.shl, ``CIL.Instruction.shr, ``CIL.Instruction.shr_un,
      ``CIL.Instruction.clt, ``CIL.Instruction.clt_un, ``CIL.Instruction.cgt_un,
      ``CIL.Instruction.ceq, ``CIL.Instruction.div, ``CIL.Instruction.div_un,
      ``CIL.Instruction.rem, ``CIL.Instruction.rem_un, ``CIL.Instruction.add_ovf,
      ``CIL.Instruction.add_ovf_un, ``CIL.Instruction.sub_ovf, ``CIL.Instruction.sub_ovf_un,
      ``CIL.Instruction.mul_ovf, ``CIL.Instruction.mul_ovf_un].contains operation
    if scalar && lhs.isAppOfArity ``CIL.Safety.step 7 then
      -- Reuse the selected value equation without rewriting its symbolic arithmetic result.
      let mut widths := #[]
      let stackTerm ← entryAt "cil_checked_step_normalized" args 5
      let mut stack ← whnfR stackTerm
      for _ in [:2] do
        let some #[_, value, rest] := argumentsOf? stack ``List.cons 3 | break
        let some #[scalar] := argumentsOf? value ``Value.scalar 1 | break
        if scalar.isAppOfArity ``CIL.Value.i32 1 then widths := widths.push "_i32"
        else if scalar.isAppOfArity ``CIL.Value.i64 1 then widths := widths.push "_i64"
        else break
        stack ← whnfR rest
      let .str _ opcodeName := operation
        | throwError "cil_checked_step_normalized: expected an opcode name, but found {operation}"
      for count in [0, 1, 2] do
        if count > widths.size then continue
        let suffix := String.join (widths.toList.take count)
        let name := `CIL.Safety ++ Name.mkSimple s!"step_{opcodeName}{suffix}_eq"
        unless (← getEnv).contains name do continue
        let saved ← saveState
        try
          let remaining ← withTransparency .instances <|
            (← getMainGoal).apply (← mkConstWithFreshMVarLevels name)
          if remaining.isEmpty then replaceMainGoal []; return
        catch _ => pure ()
        saved.restore
      if rhs.isAppOfArity ``Except.error 3 then
        let saved ← saveState
        try
          evalTactic (← `(tactic| cil_strict (
            apply step_unspecified
            cil_simp_only [observerCount, cil_guard, cil_side, $[$facts:term],*]
            done)))
          return
        catch _ => saved.restore
    let strategy ← if operation == ``CIL.Instruction.intrinsic then
        `(tactic| cil_checked_intrinsic [$facts:term,*])
      else if operation == ``CIL.Instruction.memory then
        let matchingStatic :=
          !(← dispatchFacts lhs ``CIL.Safety.staticInstruction facts.getElems).isEmpty
        let matchingMemory :=
          !(← dispatchFacts lhs ``CIL.Safety.memoryInstruction facts.getElems).isEmpty
        -- A supplied operation fact retains its abstraction; otherwise select its equation.
        if matchingStatic then
          `(tactic| cil_strict (cil_checked_memory_from_fact [$facts:term,*]))
        else if matchingMemory then
          `(tactic| cil_strict (
            cil_checked_memory_from_fact [CIL.Safety.staticInstruction, $facts:term,*]))
        else
          `(tactic| cil_strict (cil_checked_memory_by_equations [$facts:term,*]))
      -- A fact about `instruction` keeps its abstraction only if tried before a per-shape
      -- equation rewrites past it.
      else if !(← dispatchFacts lhs ``CIL.Safety.instruction facts.getElems).isEmpty then
        `(tactic| cil_strict (cil_checked_instruction_from_fact [$facts:term,*]))
      else
        `(tactic| cil_checked_step_equations [$facts:term,*])
    evalTactic strategy

/-- One checked `step` goal: normalises `facts`, then runs `cil_checked_step_normalized`. -/
syntax "cil_checked_step" "[" term,* "]" : tactic

open Lean Meta in
/-- The `numericValue value` a fact's conclusion tests, when `value` is no constructor. -/
private def opaqueNumericTest? (conclusion : Expr) : MetaM (Option Expr) := do
  let some (_, tested, _) := conclusion.consumeMData.eq? | return none
  let some #[value] := argumentsOf? tested ``CIL.Safety.numericValue 1 | return none
  if ← isConstructorApp (← whnfR value) then return none
  return some tested

open Lean Elab Tactic Meta in
/-- Each fact `numericValue value = result` about a value that is no constructor, restated over
    the unfolded definition: stepping unfolds `numericValue` before a fact can rewrite it, so
    only this form meets the checked value test. Quantified facts retain their binders. -/
def numericValueFacts (facts : Array Term) : TacticM (Array Term) := withMainContext do
  let mut restated := #[]
  for fact in facts do
    unless ← suppliedFactSatisfies fact (fun type => forallTelescope type fun _ conclusion =>
        return (← opaqueNumericTest? conclusion).isSome) do continue
    let saved ← saveState
    try
      let proof ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm fact none
      let unfolded ← forallTelescope (← instantiateMVars (← inferType proof))
        fun variables conclusion => do
          let some tested ← opaqueNumericTest? conclusion
            | throwError "Not a numeric value test"
          let some definition ← unfoldDefinition? tested
            | throwError "The numeric value test does not unfold"
          let statement := conclusion.consumeMData.replace fun term =>
            if term == tested then some definition.headBeta else none
          mkLambdaFVars variables (← mkExpectedTypeHint (mkAppN proof variables) statement)
      let unfolded ← instantiateMVars unfolded
      if unfolded.hasMVar then saved.restore
      else restated := restated.push (← Term.exprToSyntax unfolded)
    catch _ => saved.restore
  return restated

open Lean Elab Tactic Meta in
/-- Derive checked load and store facts from byte operations once, before stepping. The
    byte width selects the existing bridge; quantified facts retain their binders. A numeric
    value test of an opaque value is also stated in its unfolded form (`numericValueFacts`). -/
def prepareOperationFacts (facts : Array Term) : TacticM (Array Term) := withMainContext do
  let operationEquation (operation : Expr) :=
    operation.isAppOfArity ``CIL.Safety.read 4 ||
      operation.isAppOfArity ``CIL.Safety.readSnapshot 4 ||
      operation.isAppOfArity ``CIL.Safety.write 4
  let mut prepared := facts
  for fact in facts do
    unless ← suppliedFactSatisfies fact (fun type => forallTelescope type fun _ conclusion => do
        if conclusion.isAppOfArity ``And 2 then return true
        let some (_, operation, _) := conclusion.consumeMData.eq? | return false
        return operationEquation operation) do continue
    let saved ← saveState
    try
      let proof ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm fact none
      for part in ← equationConjuncts operationEquation proof do
        let stated ← instantiateMVars (← inferType part)
        let derived ← forallTelescope stated fun variables conclusion => do
          let some (_, operation, _) := conclusion.consumeMData.eq? | return #[]
          let reading := operation.isAppOfArity ``CIL.Safety.read 4
          let snapshot := operation.isAppOfArity ``CIL.Safety.readSnapshot 4
          let mut applied := mkAppN part variables
          -- A read stated at a closed width such as `localWidth (.aggregate 32)` derives its
          -- load at the numeral an opcode carries.
          if reading || snapshot then
            let width ← argumentAt "prepareOperationFacts" operation 2
            unless width.hasFVar || width.hasMVar || (← getNatValue? width).isSome do
              if let some value ← (Lean.Meta.evalNat (← reduce width)).run then
                let stated := mkAppN operation.getAppFn
                  (operation.getAppArgs.set! 2 (mkNatLit value))
                applied ← mkExpectedTypeHint applied
                  (conclusion.consumeMData.replace fun term =>
                    if term == operation then some stated else none)
          let mut candidates : Array (Name × Array Expr) := #[]
          if reading then
            candidates := candidates.push (``loadSnapshot_aggregate_of_read, #[applied])
          if snapshot then
            candidates := candidates.push (``loadSnapshot_aggregate_of_readSnapshot, #[applied])
          if !snapshot then
            let arguments := operation.getAppArgs
            let width := if reading then arguments[2]? else
              arguments[2]?.bind fun bytes =>
                if bytes.isAppOfArity ``numberBytes 2 then lastArgument? bytes else none
            if let some width := width then
              if let some width ← (Lean.Meta.evalNat (← reduce width)).run then
                if reading && [1, 2, 4].contains width then
                  let scalar ← mkDecideProof (mkApp (mkConst ``ScalarWidth) (mkNatLit width))
                  candidates := candidates ++ #[(``load_scalar_of_read, #[scalar, applied]),
                    (``load_scalar_signed_of_read, #[scalar, applied])]
                else
                  let bridge := match reading, width with
                    | true, 8 => ``load_word64_of_read
                    | true, 16 => ``load_vector128_of_read
                    | true, 32 => ``load_vector256_of_read
                    | true, 64 => ``load_vector512_of_read
                    | false, 8 => ``step_store64_of_write
                    | false, 1 | false, 2 | false, 4 => ``step_storeScalar_of_write
                    | false, 16 => ``step_store128_of_write
                    | false, 32 => ``step_store256_of_write
                    | false, 64 => ``step_store512_of_write
                    | _, _ => Name.anonymous
                  unless bridge.isAnonymous do candidates := candidates.push (bridge, #[applied])
          let mut results := #[]
          for (bridge, arguments) in candidates do
            let before ← getMCtx
            try
              let result ← mkAppM bridge arguments
              let result ← instantiateMVars (← mkLambdaFVars variables result)
              if result.hasMVar then setMCtx before
              else results := results.push result
            catch _ => setMCtx before
          return results
        for result in derived do
          prepared := prepared.push (← Term.exprToSyntax result)
    catch _ => saved.restore
  return prepared ++ (← numericValueFacts facts)

open Lean Elab Tactic in
/-- `CIL.truth` and `facts` normalised once for a stepping loop; per-step normalisation would
    re-simp every local fact on every instruction. -/
def cilNormalisedFacts (facts : Array Term) : TacticM (Array Term) :=
  withMainContext do
    normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|))
      (← prepareOperationFacts (#[← `(CIL.truth)] ++ facts))

open Lean Elab Tactic in
/-- Normalise `facts` with `cilNormalisedFacts`, then build a stepping loop's tactic from the
    raw and normalised facts. -/
def cilWithNormalisedFacts (facts : Array Term)
    (body : Array Term → Array Term → TacticM Syntax) : TacticM Unit :=
  withMainContext do
    let prepared ← cilNormalisedFacts facts
    withMainContext <| evalTactic (← body facts prepared)

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_step [$facts:term,*]) => do
    let config ← `(Lean.Parser.Tactic.optConfig|)
    let prepared ← normaliseStepFacts config (← prepareOperationFacts facts.getElems)
    withMainContext <| evalTactic (← `(tactic| cil_checked_step_normalized [$[$prepared:term],*]))

open Lean Elab Tactic in
/-- What a stepping tactic outside a loop steps with: `facts` and the object evidence facts its
    context gives (`gatherEvidenceFacts`), each normalised once. -/
def prepareStepFacts (facts : Array Term) : TacticM (Array Term) := do
  normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|))
    (← prepareOperationFacts (← gatherEvidenceFacts facts))

/-- `cil_checked_steps` with facts already normalised: enters an `invoke` goal through
    `cil_checked_entry`, then takes checked `run` steps until the goal closes or a step fails,
    leaving that goal. Fails if it takes no step. -/
syntax "cil_checked_steps_normalized" "[" term,* "]" : tactic

/-- Takes a fetched `ret` through `run_return`, given the method and instruction lookups, and
    leaves the equation between the returned state and the stated result unless frame cleanup,
    `rfl` or simp with `facts` closes it. -/
macro "cil_checked_return_at " methodFound:term:max instructionFound:term:max
    "[" facts:term,* "]" : tactic =>
  `(tactic| (
    cil_strict refine Eq.trans (CIL.Safety.run_return $methodFound $instructionFound
      (by cil_checked_step_normalized [$[$facts:term],*])
      (by cil_checked_side [$[$facts:term],*])) ?_
    try simp only [CIL.Safety.leaveFrame, List.foldl_nil, List.nil_append, List.append_nil,
      CIL.NarrowKind.extend_ite_one_zero, CIL.NarrowKind.extend_ite_ofNat_one_zero,
      List.reverse_cons, List.reverse_nil, cil_literal, BitVec.isValue,
      Bool.false_eq_true, ite_true, ite_false]
    try with_reducible rfl
    try (with_reducible simp [$[$facts:term],*]; done)))

/-- Takes a fetched step that continues in the same method through `run_next`, given the
    lookups, leaving the `run` goal at the next state. The step proof is elaborated before the
    continuation goal exists, so step facts can still assign reference and frame metavariables. -/
macro "cil_checked_next_at " methodFound:term:max instructionFound:term:max
    "[" facts:term,* "]" : tactic =>
  `(tactic| (
    cil_strict refine Eq.trans (CIL.Safety.run_next $methodFound $instructionFound
      (by cil_checked_step_normalized [$[$facts:term],*])) ?_
    cil_stack_cleanup))

/-- Takes a fetched step that faults through `run_fault`, given the lookups; the goal's
    located fault fixes the fault the step must raise. -/
macro "cil_checked_fault_at " methodFound:term:max instructionFound:term:max
    "[" facts:term,* "]" : tactic =>
  `(tactic| cil_strict exact CIL.Safety.run_fault $methodFound $instructionFound
    (by cil_checked_step_normalized [$[$facts:term],*]))

/-- Close a child invocation with supplied exact-run or invocation-certificate evidence. -/
syntax "cil_checked_child" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_checked_child [$facts:term,*]) => withMainContext do
    let mut candidates := facts.getElems
    for declaration in ← getLCtx do
      unless declaration.isImplementationDetail do
        let type := declaration.type.consumeMData
        if type.isAppOf `CIL.Safety.InvocationCertificate ||
            (type.eq?.any fun (_, left, _) => left.isAppOf ``CIL.Safety.invoke) then
          candidates := candidates.push (← Term.exprToSyntax declaration.toExpr)
    let mut attempted : Array Expr := #[]
    let target ← instantiateMVars (← getMainTarget)
    for candidate in candidates do
      let saved ← saveState
      try
        let proof ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm candidate none
        if attempted.contains proof then
          throwError "Already considered this invocation fact"
        attempted := attempted.push proof
        let type := (← instantiateMVars (← inferType proof)).consumeMData
        let invocationType ← if type.isAppOf `CIL.Safety.InvocationCertificate then
          inferType (← mkAppM ``And.left #[proof])
        else pure type
        if let some (_, provided, _) := invocationType.eq? then
          if let some (_, requested, _) := target.eq? then
            if provided.isAppOf ``CIL.Safety.invoke && requested.isAppOf ``CIL.Safety.invoke then
              let providedBudget ← argumentAt "cil_checked_child" provided 1
              let requestedBudget ← argumentAt "cil_checked_child" requested 1
              let providedFuel ← getNatValue? providedBudget
              let requestedFuel ← getNatValue? requestedBudget
              -- An abstract program cannot reduce to reconcile different concrete budgets.
              let program ← argumentAt "cil_checked_child" requested 0
              -- Only a local program has a declaration; a nested `←` would also run on a constant.
              let abstract ← match program with
                | .fvar programVariable => pure (← programVariable.getDecl).value?.isNone
                | _ => pure false
              if abstract && argument? provided 0 == some program then
                if let some supplied := providedFuel then
                  if let some needed := requestedFuel then
                    if supplied != needed then
                      throwError "Child invocation has a different concrete fuel budget"
        if type.isAppOf `CIL.Safety.InvocationCertificate then
          evalTactic (← `(tactic| cil_strict exact ($candidate).1))
        else if type.eq?.any (fun (_, left, _) => left.isAppOf ``CIL.Safety.invoke) then
          evalTactic (← `(tactic| cil_strict exact $candidate))
        else throwError "Not an invocation fact"
        return
      catch _ => saved.restore
    throwError "No child invocation evidence matches the requested fuel and state"

/-- Takes a fetched call through `run_call_of_invoke`, given the lookups: the callee runs to its
    return, and the caller's continuation, on the returned values, stays open as the goal. -/
macro "cil_checked_call_open_at " methodFound:term:max instructionFound:term:max
    "[" facts:term,* "]" : tactic =>
  `(tactic| (
    cil_strict refine CIL.Safety.run_call_of_invoke $methodFound $instructionFound
      (by cil_checked_step_normalized [$[$facts:term],*])
      (by first | cil_checked_child [$[$facts:term],*]
                | (cil_checked_steps_normalized [$[$facts:term],*]; done)) ?_
    cil_stack_cleanup))

open Lean Elab Tactic Meta in
/-- Instantiate `lemma` against the goal through `select`, close its method and instruction
    lookups (the premises `lookups` places from the end) with `cil_lookup`, and return both
    proofs as syntax with the fetched opcode's constructor. -/
def cilFetchedOp (lemma : Lean.Name) (select : Lean.Expr → Option Lean.Expr) (lookups : Nat)
    (facts : Array Lean.Term) : Lean.Elab.Tactic.TacticM (Lean.Term × Lean.Term × Lean.Name) := do
  -- A tactic `have` leaves the target under `mdata`, which `select` (`Expr.eq?`) does not see
  -- through.
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let (premises, _, conclusion) ←
    forallMetaTelescopeReducing (← inferType (← mkConstWithFreshMVarLevels lemma))
  let some goalPart := select target | throwError "The goal does not have the shape of {lemma}"
  let some lemmaPart := select conclusion | throwError "Unexpected statement of {lemma}"
  unless ← isDefEq lemmaPart goalPart do throwError "The goal does not have the shape of {lemma}"
  let methodFound ← entryAt "cilFetchedOp" premises (premises.size - lookups)
  let instructionFound ← entryAt "cilFetchedOp" premises (premises.size - lookups + 1)
  for proof in [methodFound, instructionFound] do
    let .mvar lookupGoal := proof
      | throwError "cilFetchedOp: expected a lookup premise, but found{indentExpr proof}"
    let remaining ← Tactic.run lookupGoal (evalTactic (← `(tactic| cil_lookup [$facts,*])))
    unless remaining.isEmpty do throwError "The method or instruction lookup did not close"
  let fetched ← instantiateMVars (← inferType instructionFound)
  let some (_, _, found) := fetched.eq? | throwError "Unexpected instruction lookup"
  let fetchedOp ← lastArgument "cilFetchedOp" found
  let operation :=
    ((← cilReducedOp? fetchedOp).bind (·.getAppFn.constName?)).getD Name.anonymous
  let lookupSyntax (proof : Expr) : TacticM Term := do
    let expected ← instantiateMVars (← inferType proof)
    let proof ← instantiateMVars proof
    let actual ← instantiateMVars (← inferType proof)
    -- Reflexivity may infer `code[pc]? = code[pc]?`; consumers need the fetched `some op`.
    Term.exprToSyntax (if actual == expected then proof else mkExpectedPropHint proof expected)
  return (← lookupSyntax methodFound, ← lookupSyntax instructionFound, operation)

open Lean Elab Tactic Meta in
/-- Derive current argument facts once for a write's continuation, retaining old snapshots only
    at their original memory. The marker names let later steps reuse them without re-simping. -/
private def cilRememberOutputFacts (call : Term) : TacticM Unit := withMainContext do
  let proof ← Term.elabTerm call none
  let facts := (← validCallArgumentFacts call (← inferType proof)).map (·.2.1)
  let prepared ← normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|))
    (← prepareOperationFacts facts)
  for fact in prepared do
    discard <| assertLoopFact `cilOutputFact fact #[]

open Lean Elab Tactic Meta in
/-- Reuse current-memory argument facts after a write, deriving them once when its continuation
    needs them. An empty-stack return consumes no argument evidence. -/
def cilOutputFacts (operation : Name) : TacticM (Array Term) := withMainContext do
  let mut retained := #[]
  let mut calls := #[]
  for declaration in ← getLCtx do
    let name := declaration.userName.eraseMacroScopes
    if name == `cilOutputFact then retained := retained.push declaration
    if name == `cilOutputCall then calls := calls.push declaration
  if retained.isEmpty && calls.isEmpty then return #[]
  let some execution := (← instantiateMVars (← getMainTarget)).find?
      (·.isAppOfArity ``run 8) | return #[]
  let #[_, _, _, _, _, _, stack, memory] := execution.getAppArgs | return #[]
  if operation == ``CIL.Instruction.ret && (← whnfD stack).isAppOf ``List.nil then return #[]
  -- Facts remembered below join the context after `retained` was collected, so they are
  -- found by a second scan.
  let currentFacts (markers : Array LocalDecl) : TacticM (Array Term) := withMainContext do
    let mut facts := #[]
    for declaration in markers do
      if (← loopFactMemories declaration.type).contains memory then
        facts := facts.push (← Term.exprToSyntax declaration.toExpr)
    return facts
  let facts ← currentFacts retained
  unless facts.isEmpty do return facts
  for declaration in calls do
    let type ← instantiateMVars declaration.type
    if type.isAppOfArity `CIL.Safety.ValidCall 3 && argument? type 0 == some memory then
      cilRememberOutputFacts (← Term.exprToSyntax declaration.toExpr)
      let remembered ← withMainContext do
        return (← getLCtx).foldl (init := #[]) fun found declaration =>
          if declaration.userName.eraseMacroScopes == `cilOutputFact then found.push declaration
          else found
      return ← currentFacts remembered
  return #[]

open Lean Elab Tactic Meta in
/-- Input formation and read equations supply no checked write. Any other supplied fact keeps
    the ordinary store attempt first, including whole-step facts and custom normalization. -/
def cilOnlyInputFacts (operation : Name) (facts : Array Term) : TacticM Bool :=
  facts.allM fun fact => suppliedFactSatisfies fact fun type => do
    let some (_, left, _) := type.getForallBody.consumeMData.eq? | return false
    if left.isAppOf ``form || left.isAppOf ``read then return true
    let some #[_, op, _, _, _, _, _] := argumentsOf? left ``step 7 | return false
    -- Only known reads are excluded; a generic or custom step retains its priority.
    return op.isAppOf ``CIL.Instruction.fieldAt && operation != ``CIL.Instruction.fieldAt

open Lean Elab Tactic Meta in
/-- Materialize a checked output-word write in the outer continuation. Only the fetched store
    and a `ValidCall` at its current memory are considered; permissions remain real premises. -/
def cilPrepareOutputStore (instructionFound : Term) (operation : Name)
    (facts : Array Term) : TacticM (Array Term) := withMainContext do
  unless [``CIL.Instruction.store64, ``CIL.Instruction.storeScalar,
      ``CIL.Instruction.setFieldAt].contains operation do
    return facts
  unless (← getEnv).contains `CIL.Safety.ValidCall.store_word do return facts
  let some execution := (← instantiateMVars (← getMainTarget)).find?
      (·.isAppOfArity ``run 8) | return facts
  let #[_, _, _, _, _, _, stackTerm, memory] := execution.getAppArgs | return facts
  let stack ← listEntries stackTerm
  let some (_, value) := stack[0]? | return facts
  let some (_, address) := stack[1]? | return facts
  let value ← whnf value
  let address ← whnf address
  let some #[scalar] := argumentsOf? value ``Value.scalar 1 | return facts
  let some #[wordValue] := argumentsOf? scalar ``CIL.Value.i64 1 | return facts
  let some #[target] := argumentsOf? address ``Value.reference 1 | return facts
  let some #[reference] := argumentsOf? target ``ManagedReference.address 1 | return facts
  let word ← Term.exprToSyntax wordValue
  let instruction ← inferType (← Term.elabTerm instructionFound none)
  let some (_, _, found) := instruction.eq? | return facts
  let some fetchedOp := lastArgument? found | return facts
  let opcode ← whnf fetchedOp
  let mut offset := mkNatLit 0
  if operation == ``CIL.Instruction.storeScalar then
    let some width := lastArgument? opcode | return facts
    unless ← isDefEq width (mkNatLit 8) do return facts
  if operation == ``CIL.Instruction.setFieldAt then
    let some width := lastArgument? opcode | return facts
    unless ← isDefEq width (mkNatLit 8) do return facts
    let some fieldOffset := (appliedFunction? opcode).bind lastArgument? | return facts
    offset := fieldOffset
  let offsetTerm ← Term.exprToSyntax offset
  let declarations := (← getLCtx).decls.toArray.filterMap id
  for declaration in declarations do
    let type ← instantiateMVars declaration.type
    let some #[callMemory, _, outputs] := argumentsOf? type `CIL.Safety.ValidCall 3 | continue
    unless ← withNewMCtxDepth <| isDefEq callMemory memory do continue
    for (position, view) in ← listEntries outputs do
      let view ← whnf view
      let some #[viewed, _] := argumentsOf? view `CIL.Safety.ArgumentView.mk 2 | continue
      unless ← withNewMCtxDepth <| isDefEq viewed reference do continue
      let saved ← saveState
      try
        let call ← Term.exprToSyntax declaration.toExpr
        let view ← Term.exprToSyntax view
        let bases := #["stored", "addressed", "written", "readback", "storedCall"]
        let index := firstUnusedSuffix (← getLCtx) bases
        let names := bases.map (fun base => mkIdent (suffixedName index base))
        let #[after, addressed, written, readback, retained] := names
          | throwError "cilPrepareOutputStore: expected a name for each of {bases}"
        let store := Syntax.mkApp (mkCIdent `CIL.Safety.ValidCall.store_word)
          #[call, view, ← `(List.mem_of_getElem? (i := $(quote position)) rfl), offsetTerm,
            ← `(by dsimp only; first | decide | omega), word]
        Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic|
          obtain ⟨$after, $addressed, $written, $readback, $retained⟩ := $store))
        discard <| assertLoopFact `cilOutputCall retained #[]
        -- Reached symbolic values already match the stepper; literal writes need its
        -- evaluated conversions as well.
        let prepared ← prepareOperationFacts #[addressed, written]
        let prepared ← withMainContext do
          let type ← inferType (← Term.elabTerm written none)
          if hasClosedLiteralOperand type then
            normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|)) prepared
          else pure prepared
        return facts ++ prepared
      catch _ =>
        saved.restore
  return facts

open Lean Elab Tactic Meta in
/-- Whether the main goal is an equation whose right side is syntactically `Except.error`. -/
def cilGoalStatesFault : TacticM Bool := withMainContext do
  return (← instantiateMVars (← getMainTarget)).consumeMData.eq?.any
    fun (_, _, result) => result.isAppOf ``Except.error

/-- Enters an `invoke` goal through `invoke_of_run_fault` when it states `.error`, else through
    `invoke_of_run`, and leaves the goal unchanged when entry fails. A goal already about `run`
    tries neither, since unifying an entry lemma against it costs a failed defeq check. -/
syntax "cil_checked_entry" "[" term,* "]" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_checked_entry [$facts:term,*]) => withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    if target.eq?.any (·.2.1.consumeMData.isAppOf ``CIL.Safety.run) then return
    let entry := mkIdent (if ← cilGoalStatesFault then ``CIL.Safety.invoke_of_run_fault
      else ``CIL.Safety.invoke_of_run)
    evalTactic (← `(tactic| try
      (cil_strict apply $entry
       · cil_lookup [$facts,*]
       · cil_checked_side [$facts,*]
       · cil_checked_side [$facts,*])))

/-- Whether an opcode steps to a call action: `call`, or `callvirt` with a non-null receiver. -/
def callsCallee (operation : Lean.Name) : Bool :=
  operation == ``CIL.Instruction.call || operation == ``CIL.Instruction.callInstance ||
    operation == ``CIL.Instruction.callVirtual

open Lean Elab Tactic Meta in
/-- One `run` step: prove the method and instruction lookups once, then apply only the
    composition lemma for the fetched opcode. A call proves its callee and leaves the caller's
    continuation as the goal. Toward a stated fault, a step that raises it ends the run. -/
def cilRunStepNodes (facts : Array Term) : TacticM Unit := withMainContext do
  -- `run_fault` can close only at the pc the stated fault names; elsewhere it only costs.
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let faulting ← match target.eq? with
    | some (_, current, result) =>
      if !result.isAppOf ``Except.error then pure false
      else
        let some located := lastArgument? result | pure true
        let located := located.consumeMData
        if let (some #[_, faultPc, _], some #[_, _, _, pc, _, _, _, _]) :=
            (argumentsOf? located ``CIL.Safety.LocatedFault.mk 3,
              argumentsOf? current ``CIL.Safety.run 8) then
          withNewMCtxDepth <| withTransparency .instances <|
            isDefEq faultPc pc
        else pure true
    | none => pure false
  let (methodSyntax, instructionSyntax, operation) ←
    cilFetchedOp ``CIL.Safety.run_next (fun e => e.eq?.map (·.2.1)) 3 facts
  -- An object construction runs its constructor as a call before continuing in the caller.
  let constructs := operation == ``CIL.Instruction.newObject
  -- These fault before their callee runs: a short heap budget, a null receiver, or a receiver
  -- whose class a dispatch table omits.
  let faultsFirst := constructs || operation == ``CIL.Instruction.callInstance ||
    operation == ``CIL.Instruction.callVirtual
  evalTactic (← if operation == ``CIL.Instruction.ret then
      `(tactic| cil_checked_return_at $methodSyntax $instructionSyntax [$facts,*])
    else if callsCallee operation || constructs then
      let call ← `(tactic| cil_checked_call_open_at $methodSyntax $instructionSyntax [$facts,*])
      if faulting && faultsFirst then
        `(tactic| first
          | cil_checked_fault_at $methodSyntax $instructionSyntax [$facts,*]
          | $call:tactic)
      else pure call
    else if faulting then
      `(tactic| first
        | cil_checked_fault_at $methodSyntax $instructionSyntax [$facts,*]
        | cil_checked_next_at $methodSyntax $instructionSyntax [$facts,*])
    else
      `(tactic| cil_checked_next_at $methodSyntax $instructionSyntax [$facts,*]))

open Lean Elab Tactic in
/-- `cilRunStepNodes` on the record of normal-form nodes of the running driver, so that a
    simplification leaves alone what earlier steps visited and left unchanged. -/
def cilRunStep (facts : Array Term) : TacticM Unit :=
  withNormalNodes facts (cilRunStepNodes facts)

/-- One `run` step of the goal, chosen by the fetched opcode; at a call it proves the callee and
    leaves the caller's continuation. -/
syntax "cil_checked_run_step" "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| cil_checked_run_step [$facts:term,*]) => cilRunStep facts.getElems

macro_rules
  | `(tactic| cil_checked_steps_normalized [$facts:term,*]) =>
  `(tactic| (
    try (conv => lhs; arg 2; cil_reduce_fuel)
    cil_checked_entry [$[$facts:term],*]
    cil_normal_run
      cil_steps_from "cil_checked_steps took no step: the method or instruction lookup, or the \
        first step, did not close; pass the lookup hypothesis, feature facts or step facts"
        cil_checked_run_step [$[$facts:term],*]))

/-- Proves an `invoke` or `run` goal, returning or stating a located fault, by checked
    stepping with `facts` and the object evidence facts of the context, such as `live.formed` of
    a `LiveObject` and the load a scalar field's `Readable` gives, normalised once at entry. A goal
    `∃ fuel, invoke ..` takes the execution bound of its method as the fuel, and the projections
    of a defined contract are unfolded. Stops at the first step it cannot take, leaving that
    goal; fails if it takes none. -/
syntax "cil_checked_steps" "[" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_steps [$facts:term,*]) => do
    evalTactic (← `(tactic| (cil_supply_fuel; cil_unfold_contracts)))
    let prepared ← prepareStepFacts facts.getElems
    withMainContext <| evalTactic (← `(tactic| cil_checked_steps_normalized [$[$prepared:term],*]))

/-- `cil_checked_steps` with no facts. -/
macro "cil_checked_steps" : tactic => `(tactic| cil_checked_steps [])

/-- Exactly `n` fetched steps of the left-hand `run`, for run-to-run goals whose target state
    is not syntactically the stepped one; unbounded stepping would run past it when the fuel is
    a literal. -/
syntax "cil_checked_steps " num " [" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_checked_steps $count:num [$facts:term,*]) => do
    let prepared ← prepareStepFacts facts.getElems
    -- Focus the original goal: an early close must error, not step into an unrelated pending goal.
    focus do
      withNormalRun do
        for taken in [:count.getNat] do
          if (← getGoals).isEmpty then
            throwError "cil_checked_steps {count.getNat}: the goal closed after {taken} steps"
          cilRunStep prepared
      -- Fold the stepped pc (`2 + 1`) so the residual matches a target stated with a numeral.
      unless (← getGoals).isEmpty do
        evalTactic (← `(tactic| try (conv => lhs; arg 4; simp only [Nat.reduceAdd])))

/-- `cil_checked_steps n` with no facts. -/
macro "cil_checked_steps " count:num : tactic => `(tactic| cil_checked_steps $count [])

end CIL.Safety
