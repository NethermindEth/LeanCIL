import CIL.Interface.Closure
import CIL.Safety.MethodContract

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
