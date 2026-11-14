import Tests.MetadataWorld
import Lean

/-!
# Assembly lookup regressions

Assembly lookups preserve positional links, the first identity match and arbitrary pinned
prefixes. Scaling varies assembly count independently of method instructions and metadata rows.
-/

namespace Tests.MetadataAssemblies

open CIL CIL.Extraction Tests.MetadataBuilder Tests.MetadataWorld

set_option maxRecDepth 32768

/-- Prefix matching agrees with the prefix predicate, including overlapping and empty prefixes. -/
theorem prefixes :
    let stored := [[1], [1, 2, 3], [4, 5], [4, 6]]
    let trie := stored.foldl AssemblyPrefixes.insert {}
    [[1], [1, 2, 4], [4], [4, 5, 6], [4, 6], [4, 7], []].all
      (fun scope => trie.matches scope == stored.any (·.isPrefixOf scope)) = true ∧
      (({} : AssemblyPrefixes).insert []).matches [9] = true := by decide +kernel
#print axioms prefixes

/-- Full version markers, duplicate stems and large byte keys retain exact prefix matching. -/
theorem version_prefixes :
    let stems := [[65] ++ versionMarker, [65, 44] ++ versionMarker, [512, 1], [512, 1]]
    let trie := stems.foldl AssemblyPrefixes.insert {}
    [[65] ++ versionMarker ++ [49], [65, 44] ++ versionMarker ++ [50],
      [65, 44, 32, 86], [66] ++ versionMarker, [512, 1, 2], [512], []].all
      (fun scope => trie.matches scope == stems.any (·.isPrefixOf scope)) = true := by
  decide +kernel
#print axioms version_prefixes

/-- The first complete version marker terminates a stem, even after a partial marker. -/
theorem version_stems :
    assemblyStem ([65, 44] ++ versionMarker ++ [49]) = [65, 44] ++ versionMarker ∧
    assemblyStem [65, 44, 66] = [65, 44, 66] := by decide +kernel
#print axioms version_stems

/-- Resolve the library type with the supplied assembly order and pins. -/
private def resolveLibrary (others : List MetadataSlice) (pins : List (List Nat) := []) := do
  let env := MetadataEnv.ofSlices (← (own.1 :: others).mapM MetadataSlice.index) pins
  typeRefNamed env 0 resolveFuel tokens.boxRef none

/-- Compare the exact error while retaining the successful type separately. -/
private def failedWith (result : Except MetadataError NamedType) (error : MetadataError) : Bool :=
  match result with
  | .error found => found == error
  | .ok _ => false

/-- Duplicate identities retain their first position; a link to a different position is refused. -/
theorem first_identity :
    (resolveLibrary [lib, lib]).isOk = true ∧
    failedWith (resolveLibrary [own.1, lib]) (.unresolvedType tokens.boxRef) = true := by
  decide +kernel
#print axioms first_identity

/-- Missing carried assemblies are external only when no pinned prefix covers their identity. -/
theorem pinned_missing :
    (resolveLibrary []).isOk = true ∧
    failedWith (resolveLibrary [] [assemblyStem (bytesOf libScope)])
      (.missingSlice tokens.boxRef) = true ∧
    failedWith (resolveLibrary [] [[]]) (.missingSlice tokens.boxRef) = true := by decide +kernel
#print axioms pinned_missing

/-- A carried version cannot satisfy a reference to another version of the same pinned name. -/
theorem wrong_version :
    let versioned := (build libWorld (bytesOf "Lib")
      "Lib, Version=2.0.0.0, Culture=neutral, PublicKeyToken=null" 2).1
    failedWith (resolveLibrary [versioned] [assemblyStem (bytesOf libScope)])
      (.missingSlice tokens.boxRef) = true := by decide +kernel
#print axioms wrong_version

/-- Fixed-width identities keep the benchmark's byte count proportional to assembly count. -/
private def identity (position : Nat) : List Nat :=
  [65, position / 256, position % 256, 44]

/-- Construct and query each assembly once, including the pin lookup for a missing version. -/
private def exercise (base : MetadataIndex) (count : Nat) : Bool := Id.run do
  let indexes := (List.range count).map fun position => { base with identity := identity position }
  let env := MetadataEnv.ofSlices indexes (indexes.map (·.identity))
  for position in [:count] do
    let scope := identity position
    if env.identities[scope]? != some position then return false
    if (env.slice position 0).toOption.map (·.identity) != some scope then return false
    if !env.pinned.matches (scope ++ [99]) then return false
  return true

/-- Kernel evaluation includes construction as well as every assembly query. -/
private def checkedExercise (count : Nat) : Bool :=
  match lib.index with
  | .ok base => exercise base count
  | .error _ => false

open Lean Meta Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let mut previous := 0
  for count in [128, 512, 2048] do
    let (statement, proof) ← liftTermElabM do
      let statement ← mkEq (mkApp (mkConst ``checkedExercise) (mkNatLit count))
        (mkConst ``Bool.true)
      pure (statement, ← mkEqRefl (mkConst ``Bool.true))
    let start ← IO.getNumHeartbeats
    match Kernel.check (← getEnv) {} (Expr.letE `checked statement proof (.bvar 0) false) with
    | .error error => throwKernelException error
    | .ok _ => pure ()
    let cost := (← IO.getNumHeartbeats) - start
    logInfo m!"assembly kernel checks: {count} assemblies, {cost} heartbeats"
    if previous != 0 && cost > previous * 6 then
      throwError "assembly kernel cost grew too quickly"
    previous := cost

/-- Median elapsed time includes index construction and all lookups. -/
private def measure (base : MetadataIndex) (count : Nat) : IO Nat := do
  let mut times := #[]
  for _ in [:5] do
    let start ← IO.monoNanosNow
    unless exercise base count do throw (IO.userError "assembly lookup lost an identity")
    times := times.push ((← IO.monoNanosNow) - start)
  return (times.qsort (· < ·))[2]!

#eval do
  let .ok base := lib.index | throw (IO.userError "invalid assembly fixture")
  let _ ← measure base 128
  let small ← measure base 1024
  let large ← measure base 8192
  IO.println s!"assembly lookup median ns: {small}, {large}"
  unless large < small * 24 + 30000000 do
    throw (IO.userError "assembly lookup cost grew faster than indexed construction and queries")

end Tests.MetadataAssemblies
