import Lean
import CIL.Instructions
import CIL.SymbolicExecution

/-!
# Instruction equations for hand-written bodies

`cil_instruction_equations body` states, for a hand-written method body that may take
parameters, one equation per pc: `body_instruction{pc} : (body xs).code[pc]? = some op`,
proved by `rfl` and tagged `@[cil_code ↓]`. These are the equations the extractor emits as
`method{n}_instruction{pc}` for extracted bodies, so `cil_lookup` fetches from a parametric
body, such as `def body (sse42 avx2 : Bool) (callee : Nat) : CIL.Method`, by one rewrite
instead of unfolding the body and walking its code list. An instruction that depends on a
parameter is stated as written, for example `if avx2 then op else .unsupported ...`, and
`cil_lookup` decides it from the caller's facts or literal flags. The kernel checks every
equation, so the command proves nothing about the body beyond what its definition says.
-/

namespace CIL.InstructionEquations

open Lean Meta Elab Term Command

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

/-- `cil_instruction_equations body` declares `body_instruction{pc}`, the `@[cil_code ↓]`
    equation `∀ xs, (body xs).code[pc]? = some op` proved by `rfl`, for every pc of the
    method-valued definition `body`. -/
syntax (name := instructionEquations) "cil_instruction_equations " ident : command

elab_rules : command
  | `(cil_instruction_equations $body:ident) => do
    liftTermElabM do
      let name ← realizeGlobalConstNoOverloadWithInfo body
      let info ← getConstInfo name
      let levels := info.levelParams.map mkLevelParam
      let some simpSet ← getSimpExtension? `cil_code
        | throwError "cil_instruction_equations: the cil_code simp set is not registered"
      -- Elaborated once so each statement uses the instance a written `code[pc]?` elaborates to.
      let lookup ← instantiateMVars (← elabTermAndSynthesize
        (← `(fun (method : CIL.Method) (pc : Nat) => method.code[pc]?)) none)
      forallTelescope info.type fun parameters result => do
        unless ← isDefEq result (mkConst ``CIL.Method) do
          throwError "cil_instruction_equations: {name} does not define a CIL.Method"
        let method := mkAppN (mkConst name levels) parameters
        let ops ← instructions name (mkApp (mkConst ``CIL.Method.code) method)
        for pc in [0:ops.size] do
          let fetched := lookup.beta #[method, mkNatLit pc]
          let equationName := name.appendAfter s!"_instruction{pc}"
          -- The kernel's budget per equation is `maxHeartbeats`; resetting the elaborator's
          -- window keeps earlier equations' kernel work from exhausting a later one's.
          withCurrHeartbeats do
            addDecl <| .thmDecl {
              name := equationName, levelParams := info.levelParams
              type := ← mkForallFVars parameters
                (← mkEq fetched (← mkAppM ``Option.some #[ops[pc]!]))
              value := ← mkLambdaFVars parameters (← mkEqRefl fetched) }
            addDeclarationRangesFromSyntax equationName (← getRef) body
            addDocStringCore equationName s!"The instruction at pc {pc} of `{name}`."
            -- Pre-order, as `@[cil_code ↓]`: simp rewrites the lookup before unfolding the body.
            addSimpTheorem simpSet equationName (post := false) (inv := false) .global
              (eval_prio default)

end CIL.InstructionEquations
