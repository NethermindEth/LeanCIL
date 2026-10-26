import CIL.Interface.Closure
import CIL.Safety.MethodContract

/-! Canonical contract serialization and complete interface dependency discovery. -/

open Lean CIL.Interface

namespace Tests.ContractClosure

inductive Selection where
  | first
  | second

def choose : Selection -> Bool
  | .first => true
  | .second => false

def contract : CIL.Safety.MethodContract Selection Unit where
  args _ := []
  results _ := []
  pre _ _ := True
  footprint _ := []
  post input _ _ _ := choose input = true

run_cmd do
  let first := Expr.lam `first (mkConst ``Nat) (.bvar 0) .default
  let second := Expr.lam `second (mkConst ``Nat) (.bvar 0) .default
  unless (canonicalExpression first).isOk do
    throwError "Closed lambda did not serialize"
  unless (canonicalExpression first).toOption == (canonicalExpression second).toOption do
    throwError "Binder names changed the canonical expression"
  unless (canonicalExpression first).toOption == (canonicalExpression (.mdata {} first)).toOption do
    throwError "Metadata changed the canonical expression"
  unless (canonicalExpression (.sort (.param `u)) [`u]).isOk &&
      (canonicalExpression (.sort (.param `u)) [`u]).toOption == (canonicalExpression (.sort (.param `v)) [`v]).toOption do
    throwError "Universe binder names changed the canonical expression"
  if (canonicalExpression (.bvar 0)).isOk then
    throwError "Unbound de Bruijn index accepted"
  if (canonicalExpression (.fvar (FVarId.mk `unbound))).isOk then
    throwError "Free variable accepted"
  if (canonicalExpression (.mvar (MVarId.mk `unresolved))).isOk then
    throwError "Metavariable accepted"
  if (canonicalExpression (.sort (.param `unbound))).isOk then
    throwError "Unbound universe parameter accepted"
  let embedded := Expr.const (.str .anonymous "A.B") []
  let nested := Expr.const `A.B []
  if (canonicalExpression embedded).toOption == (canonicalExpression nested).toOption then
    throwError "Structural names collapsed to printed names"
  let (kind, canonical) <- match contractClosure (<- getEnv) ``contract with
    | .ok result => pure result
    | .error error => throwError "{error}"
  unless kind == "method" && !canonical.isEmpty do
    throwError "Contract kind or closure missing"
  unless (canonical.splitOn "recursor").length > 1 do
    throwError "Computational recursor metadata omitted from the closure"

end Tests.ContractClosure

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let declared := environment.constants.toList.map fun (name, _) =>
    (name, definingModule environment name)
  for modules in #[#[], #[`CIL.Interface.Closure], #[environment.mainModule],
      #[`CIL.Interface.Closure, `CIL.Safety.MethodContract, environment.mainModule],
      #[`MissingInterfaceModule], #[`CIL.Interface.Closure, `CIL.Interface.Closure]] do
    let expected := declared.filterMap fun (name, moduleName) =>
      if modules.contains moduleName then some name else none
    let indexed := interfaceDeclarations environment modules
    let expectedSet := expected.foldl (fun set name => set.insert name) ({} : NameSet)
    let indexedSet := indexed.foldl (fun set name => set.insert name) ({} : NameSet)
    unless expectedSet.toArray.qsort Name.lt == indexedSet.toArray.qsort Name.lt do
      throwError "Indexed interface declarations differ from full environment traversal"
  let shared := Expr.app (.const `first []) (.const `second [])
  let expression := Expr.proj `Container 0 (.app shared shared)
  unless expressionDependencies expression == [`Container, `first, `second] do
    throwError "Shared expression traversal lost a dependency or changed first-occurrence order"
