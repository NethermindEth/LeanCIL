import CIL.Resolution
import CIL.InstructionEquations

/-!
# Return metadata facts

Generated facts and value stepping share a proof-producing return-type chooser. Primitive and
non-candidate heads use storage lemmas, without evaluating code or layout tables.
-/

namespace CIL.Safety.ResolutionFacts

open Lean Meta Elab Command

/-- A recognized runtime primitive, checked by its complete scope and type name. -/
def primitive? (type : Expr) : Option Name := do
  let (``CIL.Extraction.TypeExpr.atom, #[scope, name]) := type.getAppFnArgs | none
  let scopeMatches := scope.isConstOf ``CIL.Extraction.runtimeScope ||
    match scope with
    | .lit (.strVal value) => value == CIL.Extraction.runtimeScope
    | _ => false
  unless scopeMatches do none
  let .lit (.strVal name) := name | none
  let primitive ← #[(`sbyte, "System.SByte"), (`byte, "System.Byte"),
    (`boolean, "System.Boolean"), (`int16, "System.Int16"), (`uint16, "System.UInt16"),
    (`char, "System.Char"), (`int32, "System.Int32"), (`uint32, "System.UInt32"),
    (`int64, "System.Int64"), (`uint64, "System.UInt64"), (`single, "System.Single"),
    (`double, "System.Double"), (`intPtr, "System.IntPtr"), (`uintPtr, "System.UIntPtr")].find?
      (fun entry => entry.2 == name)
  return ``CIL.PrimitiveType ++ primitive.1

/-- A storage lemma for recognized heads, or one of five checked reflexivity results. -/
def declaredProof? (layouts type : Expr) : MetaM (Option Expr) := withDefault do
  let head ← withDefault <| whnf type
  if let some primitive := primitive? head then
    return some (← mkAppM ``CIL.Extraction.declaredNarrow_primitive
      #[layouts, mkConst primitive])
  if let (``CIL.Extraction.TypeExpr.enum, #[identity, underlying]) := head.getAppFnArgs then
    if let some primitive := primitive? (← withDefault <| whnf underlying) then
      return some (← mkAppM ``CIL.Extraction.declaredNarrow_enum
        #[layouts, identity, mkConst primitive])
  let mut terminal := head
  let mut identities := #[]
  repeat
    let (``CIL.Extraction.TypeExpr.enum, #[identity, underlying]) := terminal.getAppFnArgs
      | break
    identities := identities.push identity
    terminal ← withDefault <| whnf underlying
  let candidate := mkApp (mkConst ``CIL.Extraction.TypeExpr.narrowCandidate) terminal
  if (← withDefault <| whnf candidate).isConstOf ``Bool.false then
    let mut proof ← mkAppM ``CIL.Extraction.declaredNarrow_of_not_candidate
      #[layouts, terminal, ← mkEqRefl (mkConst ``Bool.false)]
    for identity in identities.reverse do
      proof ← mkAppM ``CIL.Extraction.declaredNarrow_enum_of_none
        #[layouts, identity, terminal, proof]
      terminal := mkApp2 (mkConst ``CIL.Extraction.TypeExpr.enum) identity terminal
    return some proof
  unless terminal.isAppOf ``CIL.Extraction.TypeExpr.atom do return none
  let narrowType := mkConst ``CIL.NarrowKind
  let choices := #[mkApp (mkConst ``Option.none [.zero]) narrowType] ++
    #[``CIL.NarrowKind.signed8, ``CIL.NarrowKind.unsigned8,
      ``CIL.NarrowKind.signed16, ``CIL.NarrowKind.unsigned16].map
        (fun kind => mkApp2 (mkConst ``Option.some [.zero]) narrowType (mkConst kind))
  let expression := mkApp2 (mkConst ``CIL.Extraction.declaredNarrow) layouts type
  for choice in choices do
    if ← withoutModifyingState <| isDefEq expression choice then
      return some (← mkEqRefl choice)
  return none

/-- Return narrowing from signature facts; unresolved metadata has no selected result. -/
def returnProof? (method returns declared : Expr) : MetaM (Option Expr) := withDefault do
  let some (_, _, value) := (← inferType returns).eq? | return none
  let value ← withDefault <| whnf value
  if value.isConstOf ``Bool.false then
    return some (← mkAppOptM ``CIL.Method.returnNarrow_of_void #[some method, some returns])
  unless value.isConstOf ``Bool.true do return none
  let some (_, _, signature) := (← inferType declared).eq? | return none
  let projection := mkConst ``CIL.DeclaredSignature.returnType
  let type ← withDefault <| whnf (mkApp projection signature)
  let declaredType ← mkCongrArg projection declared
  let layouts := mkApp (mkConst ``CIL.LayoutEnvironment.rawLayouts)
    (mkApp (mkConst ``CIL.Method.environment) method)
  let some resolved ← declaredProof? layouts type | return none
  return some (← mkAppOptM ``CIL.Method.returnNarrow_of_declared
    #[some method, some type, none, some returns, some declaredType, some resolved])

/-- Declares a method's kernel-checked return narrowing from its named signature facts. -/
syntax "cil_resolution_facts " ident : command

elab_rules : command
  | `(cil_resolution_facts $methodSyntax:ident) => liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo methodSyntax
    let info ← getConstInfo name
    let some simpSet ← getSimpExtension? `cil_code
      | throwError "cil_resolution_facts: cil_code is not registered"
    forallTelescope info.type fun parameters result => do
      unless ← isDefEq result (mkConst ``CIL.Method) do
        throwError "cil_resolution_facts: {name} does not define a CIL.Method"
      let body : CIL.InstructionEquations.Body :=
        { name, levelParams := info.levelParams, parameters, syntaxRef := methodSyntax }
      let method := body.constant ""
      let some proof ← returnProof? method (body.constant "_returnsValue")
          (body.constant "_declared")
        | throwError "cil_resolution_facts: return narrowing of {name} is unresolved"
      let some (_, _, result) := (← inferType proof).eq?
        | throwError "cil_resolution_facts: expected a return narrowing equality"
      let result ← withDefault <| whnf result
      body.prove "_returnNarrow" s!"The return narrowing of `{name}`."
        (← mkEq (mkApp (mkConst ``CIL.Method.returnNarrow) method) result) proof
      addSimpTheorem simpSet (name.appendAfter "_returnNarrow") (post := false)
        (inv := false) .global (eval_prio default)

end CIL.Safety.ResolutionFacts
