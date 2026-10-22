import Lean
import CIL.Instructions
import CIL.SymbolicExecution

/-!
Signature-based method identity. Extraction numbers methods by their position in the
reachable call graph, so a helper inserted anywhere renumbers unrelated methods.
`method_named`, `bind_method` and `bind_callee` locate a method by its exact emitted
signature in `Extracted.signatures` instead. Each emits `rfl` theorems that the kernel
checks, so a name only locates a method; the body is still bound by `cil_body` or
`cil_embed` and the extraction certificate.
-/

namespace CIL.MethodIdentity

open Lean Meta Elab Term Command

/-- The string literals of a closed `List String`, reduced one cell at a time. -/
partial def strings (list : Expr) (found : Array String := #[]) : MetaM (Array String) := do
  match (← whnf list).getAppFnArgs with
  | (``List.cons, #[_, head, tail]) =>
    let .lit (.strVal value) ← whnf head | throwError "signature table entry is not a string literal: {head}"
    strings tail (found.push value)
  | (``List.nil, _) => return found
  | _ => throwError "signature table is not a list literal"

/-- The method name between the last `::` and `(`; used only to rank candidates. -/
def methodName (signature : String) : String :=
  (((signature.splitOn "::").getLastD signature).splitOn "(").headD ""

/-- The constant `name` refers to here, preferring the innermost namespace: batch
verification places each extraction in its own namespace. -/
def visible (name : Name) : MetaM Name := do
  let found := (← resolveGlobalName name).filter (·.2.isEmpty) |>.map (·.1)
  let some innermost := found.foldl (fun best n => if best.all (·.getNumParts < n.getNumParts) then some n else best) none
    | throwError "{name} is not in scope; import the extraction"
  return innermost

/-- The index of the method whose signature in `table` is exactly `signature`. -/
def resolveIn (tableName : Name) (signature : String) : MetaM Nat := do
  let table ← strings (mkConst (← visible tableName))
  let indices := List.range table.size
  let listing (shown : List Nat) := "\n".intercalate (shown.map fun i => s!"  [{i}] {table[i]!}")
  match indices.filter (table[·]! == signature) with
  | [index] => return index
  | [] =>
    let named := indices.filter (methodName table[·]! == methodName signature)
    let (label, shown) := if named.isEmpty then ("extracted methods", indices) else (s!"methods named {methodName signature}", named)
    throwError "no extracted method has signature\n  {signature}\n{label}:\n{listing (shown.take 12)}"
  | many => throwError "{many.length} extracted methods have signature\n  {signature}\n{listing many}"

def resolve : String → MetaM Nat := resolveIn `Extracted.signatures

/-- The extraction index of the method with this exact signature, e.g.
`method_named "System.UInt64 Examples.Calls::Twice(System.UInt64)"`. -/
syntax (name := methodNamed) "method_named " str : term

@[term_elab methodNamed] def elabMethodNamed : TermElab := fun stx _ => do
  let some signature := stx[1].isStrLit? | throwUnsupportedSyntax
  return mkNatLit (← resolve signature)

/-- Every `(pc, callee, argc)` call in a method body, reduced one cell at a time so the
cost is linear in the body and the body is never normalized. -/
def calls (method : Expr) : MetaM (Array (Nat × Nat × Nat)) := do
  let mut cell := mkApp (mkConst ``CIL.Method.code) method
  let mut pc := 0
  let mut found := #[]
  repeat
    match (← whnf cell).getAppFnArgs with
    | (``List.cons, #[_, op, tail]) =>
      if let (``CIL.Op.call, #[callee, argc]) := (← whnf op).getAppFnArgs then
        if let (some callee, some argc) := (← (evalNat callee).run, ← (evalNat argc).run) then
          found := found.push (pc, callee, argc)
      cell := tail
      pc := pc + 1
    | _ => break
  return found

def emit (index body : Ident) (signature : StrLit) (method : Nat) : CommandElabM Unit := do
  let extracted := mkIdent (.str `Extracted s!"method{method}")
  let signatures := mkIdent `Extracted.signatures
  let program := mkIdent `Extracted.program
  elabCommand (← `(@[cil_code] def $index : Nat := $(quote method)))
  elabCommand (← `(abbrev $body : CIL.Method := $extracted))
  elabCommand (← `(theorem $(mkIdent (index.getId ++ `signature)) :
    $signatures[$index]? = some $signature := rfl))
  elabCommand (← `(@[cil_code] theorem $(mkIdent (index.getId ++ `found)) :
    $program[$index]? = some $body := rfl))

/-- `bind_method index body := "signature"` defines `index` as the extraction index of
the method with that exact signature and `body` as its extracted body, with
`index.signature` and `index.found` checked by `rfl`. -/
syntax (name := bindMethod) "bind_method " ident ppSpace ident " := " str : command

elab_rules : command
  | `(bind_method $index $body := $signature) => do
    emit index body signature (← liftTermElabM (resolve signature.getString))

/-- `bind_callee index body := "signature" from parent` binds as `bind_method` does and
also requires `parent` to call that method; `index.call` states the instruction at its
first call site. Expected bodies take `index` as a parameter, `.call index argc`, so a
renumbered extraction never changes them. -/
syntax (name := bindCallee) "bind_callee " ident ppSpace ident " := " str " from " term : command

elab_rules : command
  | `(bind_callee $index $body := $signature from $parent) => do
    let (method, site) ← liftTermElabM do
      let method ← resolve signature.getString
      let parentBody ← instantiateMVars (← elabTermEnsuringType parent (some (mkConst ``CIL.Method)))
      let sites ← calls parentBody
      let some site := sites.find? (·.2.1 == method) | do
        let table ← strings (mkConst (← visible `Extracted.signatures))
        let called := sites.toList.map (·.2.1) |>.eraseDups
        throwError "{parent} does not call\n  {signature.getString}\nit calls:\n{"\n".intercalate (called.map fun i => s!"  [{i}] {table[i]?.getD "?"}")}"
      return (method, site)
    emit index body signature method
    let (pc, _, argc) := site
    elabCommand (← `(@[cil_code] theorem $(mkIdent (index.getId ++ `call)) :
      ($parent).code[$(quote pc)]? = some (CIL.Op.call $index $(quote argc)) := rfl))

end CIL.MethodIdentity
