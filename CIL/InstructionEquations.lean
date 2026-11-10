import Lean
import CIL.Instructions
import CIL.SymbolicExecution

/-!
# Instruction equations for hand-written bodies

`cil_instruction_equations body` states, for a hand-written method body that may take
parameters, one equation per pc: `body_instruction{pc} : (body xs).code[pc]? = some op`,
tagged `@[cil_code ↓]`. These are the equations the extractor emits as
`method{n}_instruction{pc}` for extracted bodies, so `cil_lookup` fetches from a parametric
body, such as `def body (sse42 avx2 : Bool) (callee : Nat) : CIL.Method`, by one rewrite
instead of unfolding the body and walking its code list. An instruction that depends on a
parameter is stated as written, for example `if avx2 then op else .unsupported ...`, and
`cil_lookup` decides it from the caller's facts or literal flags.

The proofs follow `CIL.CodeSuffix`, as the extractor's do: the command names the suffix of the
code at every `suffixBlock` instructions as `body_suffix{start}`, proves
`body_suffix{start}_placed` from the suffix before it, and proves each equation from the suffix
that starts its block. No proof walks more than one block, so the equations of a body cost
time linear in its length. The kernel checks every declaration, so the command proves nothing
about the body beyond what its definition says.
-/

namespace CIL.InstructionEquations

open Lean Meta Elab Term Command

/-- Instructions per named code suffix; no proof the command builds walks more cells of a
    body's code than this. -/
def suffixBlock : Nat := 16

/-- The instructions of `code`, one per list cell and each as written in the body. Fails when
    a cell cannot be reached by reduction, as when a parameter decides the code's length or
    the body is irreducible or opaque. -/
def instructions (body : Name) (code : Expr) : MetaM (Array Expr) := do
  let mut cell := code
  let mut found := #[]
  repeat
    match (← whnf cell).getAppFnArgs with
    | (``List.cons, #[_, op, tail]) =>
      found := found.push (← instantiateMVars op).headBeta
      cell := tail
    | (``List.nil, _) => break
    | _ => throwError "cil_instruction_equations: the instruction at pc {found.size} of \
        {body} is not determined by its parameters, or the body does not unfold; state each \
        feature-dependent instruction as an `if` on the instruction, padding the shorter side \
        with `.unsupported`, so every profile has the same pcs"
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

/-- `[Op]`, the type of a code list. -/
def codeType : Expr := mkApp (mkConst ``List [.zero]) (mkConst ``CIL.Op)

/-- `Eq.refl list` for a code list. -/
def codeRefl (list : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [.one]) codeType list

/-- Declares `body_suffix{start}`, the code of `body` from each block boundary on, and
    `body_suffix{start}_placed : (body xs).code.drop start = body_suffix{start} xs`, each
    proved from the suffix one block earlier. -/
def declareSuffixes (body : Body) (code : Expr) (ops : Array Expr) : TermElabM Unit := do
  let suffix (start : Nat) := body.constant s!"_suffix{start}"
  let starts := (List.range ((ops.size + suffixBlock - 1) / suffixBlock)).map (· * suffixBlock)
  -- Each suffix is its block followed by the next suffix, so the last one is declared first.
  for start in starts.reverse do
    let stop := min (start + suffixBlock) ops.size
    let rest := if stop < ops.size then suffix stop else
      mkApp (mkConst ``List.nil [.zero]) (mkConst ``CIL.Op)
    let value ← mkLambdaFVars body.parameters <| (ops.extract start stop).foldr (init := rest)
      (mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``CIL.Op))
    let name := body.name.appendAfter s!"_suffix{start}"
    body.declare name s!"The code of `{body.name}` from pc {start} on." <| .defnDecl {
      name, levelParams := body.levelParams, value, safety := .safe
      type := ← mkForallFVars body.parameters codeType
      hints := .regular (getMaxHeight (← getEnv) value + 1) }
    -- Proofs alone read the suffixes, so they have no compiled code.
    modifyEnv (addNoncomputable · name)
  for start in starts do
    let previous := start - suffixBlock
    let dropped := mkApp3 (mkConst ``List.drop [.zero]) (mkConst ``CIL.Op) (mkNatLit start) code
    body.prove s!"_suffix{start}_placed"
      s!"The code of `{body.name}` from pc {start} on is `{body.name}_suffix{start}`."
      (mkApp3 (mkConst ``Eq [.one]) codeType dropped (suffix start))
      (if start = 0 then codeRefl (suffix start) else
        mkApp7 (mkConst ``CIL.CodeSuffix.advance) code (suffix previous) (suffix start)
          (mkNatLit previous) (mkNatLit suffixBlock)
          (body.constant s!"_suffix{previous}_placed") (codeRefl (suffix start)))

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
        declareSuffixes body code ops
        for pc in [0:ops.size] do
          let index := pc % suffixBlock
          let start := pc - index
          -- A window per equation, so a long body's statements do not exhaust the command's.
          withCurrHeartbeats do
            let found ← mkAppM ``Option.some #[ops[pc]!]
            body.prove s!"_instruction{pc}" s!"The instruction at pc {pc} of `{name}`."
              (← mkEq (lookup.beta #[method, mkNatLit pc]) found)
              (mkApp7 (mkConst ``CIL.CodeSuffix.lookup) code (body.constant s!"_suffix{start}")
                (mkNatLit start) ops[pc]! (mkNatLit index)
                (body.constant s!"_suffix{start}_placed") (← mkEqRefl found))
            -- Pre-order, as `@[cil_code ↓]`: simp rewrites the lookup before unfolding the body.
            addSimpTheorem simpSet (name.appendAfter s!"_instruction{pc}") (post := false)
              (inv := false) .global (eval_prio default)

end CIL.InstructionEquations
