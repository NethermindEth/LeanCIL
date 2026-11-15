import Lean
import CIL.Instructions
import CIL.SymbolicExecution

/-!
# Instruction equations

`cil_instruction_equations body` states, for a method body that may take parameters, one
equation per pc: `body_instruction{pc} : (body xs).code[pc]? = some op`, tagged
`@[cil_code ↓]`. The extractor writes the command after each `method{n}`, the template emitter
after each generated template, and a hand-written body calls it itself, so `cil_lookup` fetches
from an extracted body and from a parametric one, such as
`def body (sse42 avx2 : Bool) (callee : Nat) : CIL.Method`, by one rewrite instead of unfolding
the body and walking its code list. An instruction that depends on a parameter is stated as
written, for example `if avx2 then op else .unadmitted opcode`, and `cil_lookup` decides it from
the caller's facts or literal flags.

The proofs follow `CIL.CodeSuffix`: the command names the suffix of the code at every
`suffixBlock` instructions as `body_suffix{start}`, proves `body_suffix{start}_placed` from the
suffix before it, and proves each equation from the suffix that starts its block. No proof
walks more than one block, so the equations of a body cost time linear in its length. The
kernel checks every declaration, so the command proves nothing about the body beyond what its
definition says.
-/

namespace CIL.InstructionEquations

open Lean Meta Elab Term Command

/-- Instructions per named code suffix; no proof the command builds walks more cells of a
    body's code than this. -/
def suffixBlock : Nat := 16

/-- The elements of `list`, one per cell and each as written, and whether the cells reached
    end in `[]`. The walk stops early at a cell that does not reduce to `::` or `[]`, as
    when a parameter decides the list's length or the list is irreducible or opaque. -/
def listElements (list : Expr) : MetaM (Array Expr × Bool) := do
  let mut cell := list
  let mut found := #[]
  repeat
    match (← whnf cell).getAppFnArgs with
    | (``List.cons, #[_, element, tail]) =>
      found := found.push (← instantiateMVars element).headBeta
      cell := tail
    | (``List.nil, _) => return (found, true)
    | _ => return (found, false)
  return (found, false)

/-- The instructions of `code`, one per list cell and each as written in the body. Fails when
    a cell cannot be reached by reduction, as when a parameter decides the code's length or
    the body is irreducible or opaque. -/
def instructions (body : Name) (code : Expr) : MetaM (Array Expr) := do
  let (found, complete) ← listElements code
  unless complete do
    throwError "cil_instruction_equations: the instruction at pc {found.size} of \
      {body} is not determined by its parameters, or the body does not unfold; state each \
      feature-dependent instruction as an `if` on the instruction, padding the shorter side \
      with `.unadmitted`, so every profile has the same pcs"
  return found

/-- A body whose equations are being declared: its name, universe parameters, parameters and
    the syntax the declarations are attributed to. -/
structure Body where
  /-- The method-valued definition. -/
  name : Name
  /-- Its universe parameters, which every declaration made for it takes. -/
  levelParams : List Name
  /-- The free variables standing for its parameters. -/
  parameters : Array Expr
  /-- The identifier naming it in the command. -/
  syntaxRef : Syntax

/-- The constant `body{tail}` applied to the body's parameters. -/
def Body.constant (body : Body) (tail : String) : Expr :=
  mkAppN (mkConst (body.name.appendAfter tail) (body.levelParams.map mkLevelParam))
    body.parameters

/-- Adds the kernel-checked declaration `declaration` named `name`, located at the body and
    documented by `doc`. -/
def Body.declare (body : Body) (name : Name) (doc : String) (declaration : Declaration) :
    TermElabM Unit :=
  -- The kernel's budget per declaration is `maxHeartbeats`; resetting the elaborator's window
  -- keeps earlier declarations' kernel work from exhausting a later one's.
  withCurrHeartbeats do
    addDecl declaration
    addDeclarationRangesFromSyntax name (← getRef) body.syntaxRef
    addDocStringCore name doc

/-- Declares the theorem `body{tail} : ∀ xs, statement` with proof `fun xs => proof`. -/
def Body.prove (body : Body) (tail doc : String) (statement proof : Expr) : TermElabM Unit := do
  let name := body.name.appendAfter tail
  body.declare name doc <| .thmDecl {
    name, levelParams := body.levelParams
    type := ← mkForallFVars body.parameters statement
    value := ← mkLambdaFVars body.parameters proof }

/-- The literal list of `elements` of type `elementType` followed by `rest`. -/
def listLiteral (elementType : Expr) (elements : Array Expr) (rest : Expr) : Expr :=
  elements.foldr (init := rest) (mkApp3 (mkConst ``List.cons [.zero]) elementType)

/-- The positions at which `declareSuffixes` names a suffix of a list of `length` elements. -/
def suffixStarts (length : Nat) : List Nat :=
  (List.range ((length + suffixBlock - 1) / suffixBlock)).map (· * suffixBlock)

/-- The suffix of a list of `elements` from `position` on as a literal: the rest of its block,
    then the next named suffix `body{stem}{start}` or `[]`. -/
def suffixFrom (body : Body) (stem : String) (elementType : Expr) (elements : Array Expr)
    (position : Nat) : Expr :=
  let stop := min (position - position % suffixBlock + suffixBlock) elements.size
  let rest := if stop < elements.size then body.constant s!"{stem}{stop}" else
    mkApp (mkConst ``List.nil [.zero]) elementType
  listLiteral elementType (elements.extract position stop) rest

/-- A proof of `list[position]? = some element` from the named suffix that starts the
    position's block; it walks at most one block. -/
def foundAt (body : Body) (stem : String) (elementType list : Expr) (elements : Array Expr)
    (position : Nat) : MetaM Expr := do
  let offset := position % suffixBlock
  let start := position - offset
  let element := elements[position]!
  return mkApp8 (mkConst ``CIL.CodeSuffix.lookup) elementType list
    (body.constant s!"{stem}{start}") (mkNatLit start) element (mkNatLit offset)
    (body.constant s!"{stem}{start}_placed") (← mkEqRefl (← mkAppM ``Option.some #[element]))

/-- Declares `body{stem}{start}`, the elements of `list` from each block boundary on, and
    `body{stem}{start}_placed : list.drop start = body{stem}{start} xs`, each proved from the
    suffix one block earlier; `describe start` names what the suffix at `start` holds. -/
def declareSuffixes (body : Body) (elementType : Expr) (stem : String)
    (describe : Nat → String) (list : Expr) (elements : Array Expr) : TermElabM Unit := do
  let suffix (start : Nat) := body.constant s!"{stem}{start}"
  let listType := mkApp (mkConst ``List [.zero]) elementType
  let refl (value : Expr) := mkApp2 (mkConst ``Eq.refl [.one]) listType value
  let starts := suffixStarts elements.size
  -- Each suffix is its block followed by the next suffix, so the last one is declared first.
  for start in starts.reverse do
    let value ← mkLambdaFVars body.parameters (suffixFrom body stem elementType elements start)
    let name := body.name.appendAfter s!"{stem}{start}"
    body.declare name s!"{describe start}." <| .defnDecl {
      name, levelParams := body.levelParams, value, safety := .safe
      type := ← mkForallFVars body.parameters listType
      hints := .regular (getMaxHeight (← getEnv) value + 1) }
    -- Proofs alone read the suffixes, so they have no compiled code.
    modifyEnv (addNoncomputable · name)
  for start in starts do
    let previous := start - suffixBlock
    let dropped := mkApp3 (mkConst ``List.drop [.zero]) elementType (mkNatLit start) list
    body.prove s!"{stem}{start}_placed"
      s!"{describe start} is `{body.name}{stem}{start}`."
      (mkApp3 (mkConst ``Eq [.one]) listType dropped (suffix start))
      (if start = 0 then refl (suffix start) else
        mkApp8 (mkConst ``CIL.CodeSuffix.advance) elementType list (suffix previous)
          (suffix start) (mkNatLit previous) (mkNatLit suffixBlock)
          (body.constant s!"{stem}{previous}_placed") (refl (suffix start)))

/-- `cil_instruction_equations body` declares `body_instruction{pc}`, the `@[cil_code ↓]`
    equation `∀ xs, (body xs).code[pc]? = some op`, for every pc of the method-valued
    definition `body`, with the named suffixes `body_suffix{start}` its proofs go through. -/
syntax (name := instructionEquations) "cil_instruction_equations " ident : command

elab_rules : command
  | `(cil_instruction_equations $bodySyntax:ident) => do
    liftTermElabM do
      let name ← realizeGlobalConstNoOverloadWithInfo bodySyntax
      let info ← getConstInfo name
      let some simpSet ← getSimpExtension? `cil_code
        | throwError "cil_instruction_equations: the cil_code simp set is not registered"
      -- Elaborated once so each statement uses the instance a written `code[pc]?` elaborates to.
      let lookup ← instantiateMVars (← elabTermAndSynthesize
        (← `(fun (method : CIL.Method) (pc : Nat) => method.code[pc]?)) none)
      forallTelescope info.type fun parameters result => do
        unless ← isDefEq result (mkConst ``CIL.Method) do
          throwError "cil_instruction_equations: {name} does not define a CIL.Method"
        let body : Body :=
          { name, levelParams := info.levelParams, parameters, syntaxRef := bodySyntax }
        let method := body.constant ""
        let code := mkApp (mkConst ``CIL.Method.code) method
        let ops ← instructions name code
        declareSuffixes body (mkConst instructionTypeName) "_suffix"
          (fun start => s!"The code of `{name}` from pc {start} on") code ops
        for inRange : pc in [0:ops.size] do
          -- A window per equation, so a long body's statements do not exhaust the command's.
          withCurrHeartbeats do
            let found ← mkAppM ``Option.some #[ops[pc]]
            body.prove s!"_instruction{pc}" s!"The instruction at pc {pc} of `{name}`."
              (← mkEq (lookup.beta #[method, mkNatLit pc]) found)
              (← foundAt body "_suffix" (mkConst instructionTypeName) code ops pc)
            -- Pre-order, as `@[cil_code ↓]`: simp rewrites the lookup before unfolding the body.
            addSimpTheorem simpSet (name.appendAfter s!"_instruction{pc}") (post := false)
              (inv := false) .global (eval_prio default)

end CIL.InstructionEquations
