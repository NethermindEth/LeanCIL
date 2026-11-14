import Tests.MetadataBuilder
import Lean

/-! Scaling checks for metadata generic owner indexing and owner lookups. -/

namespace Tests.GenericOwnerScaling

open CIL.Extraction Tests.MetadataBuilder

set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-- An assembly with one carried parameter for each of `count` distinct owners. -/
private def metadata (count : Nat) : MetadataSlice :=
  let empty := (build (pure ()) (bytesOf "T")
    "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null").1
  let counts := [(Table.assembly, 1), (Table.genericParam, count)]
  { empty with
    assembly := { empty.assembly with
      header := TableHeader.ofCounts 0 counts
      tableHeader := tableHeader counts }
    rows := (List.range count).map fun position =>
      (tokenOf Table.genericParam (position + 1),
        encodeRow Table.genericParam [0, 0, (position + 1) * 2, 0]) }

/-- Build the shared tables once and read every owner's complete parameter run. -/
private def checksOwners (count : Nat) : Bool :=
  match (do
    let metadata := metadata count
    let index ← metadata.indexWith (← metadata.tables) []
    (List.range count).allM fun position => do
      let rows ← index.genericParameters 0 (tokenOf Table.typeDef (position + 1))
      pure (rows.length == 1)) with
  | .ok accepted => accepted
  | .error _ => false

open Lean Meta Elab Command in
run_cmd do
  let allowedFourfoldGrowth := 6
  let mut previous := 0
  for count in [128, 512, 2048] do
    let (statement, proof) ← liftTermElabM do
      let statement ← mkEq (mkApp (mkConst ``checksOwners) (mkNatLit count))
        (mkConst ``Bool.true)
      let proof ← mkEqRefl (mkConst ``Bool.true)
      pure (statement, proof)
    let start ← IO.getNumHeartbeats
    let checked := Expr.letE `checked statement proof (.bvar 0) false
    match Kernel.check (← getEnv) {} checked with
    | .error error => throwKernelException error
    | .ok _ => pure ()
    let cost := (← IO.getNumHeartbeats) - start
    if previous != 0 && cost > previous * allowedFourfoldGrowth then
      throwError "Generic owner cost grew from {previous} to {cost} for four times the owners"
    logInfo m!"Generic owner checks: {count} owners, {cost} heartbeats"
    previous := cost

end Tests.GenericOwnerScaling
