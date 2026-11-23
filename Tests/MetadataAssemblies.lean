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

/-- Resolve a caller's TypeRef through the facade's physical ExportedType and AssemblyRef rows. -/
private def forwarded (flags := 0x00200000) (typeDefId := 0) (implementation := 5)
    (forwardName := "InvalidOperationException") (targetName := "Core")
    (declaredName := "InvalidOperationException") (visibility := 1)
    (forwarderSlice := 1) (carry := true) (nested := false) (childParent := 6)
    (childFlags := 0) (childVisibility := 2) (childExportName := "Child") : Option (List Nat) := do
  let identity := fun (name : String) => name ++ ", Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
  let make := fun (name : String) (entries : Step Nat) => build entries (bytesOf name) (identity name)
  let (library, definition) := make "Core" do
    let name ← string declaredName
    let ns ← string "System"
    let outer ← row Table.typeDef [visibility, name, ns, 0, 1, 1]
    if !nested then return outer
    let child ← row Table.typeDef [childVisibility, ← string "Child", 0, 0, 1, 1]
    let nesting ← row Table.nestedClass [tokenRow child, tokenRow outer]
    link linkNesting child 2 nesting
    return child
  let (facade, exported) := make "Facade" do
    let dest ← string targetName
    let _ ← row Table.assemblyRef [1, 0, 0, 0, 0, 0, dest, 0, 0]
    let name ← string forwardName
    let ns ← string "System"
    let outer ← row Table.exportedType [flags, typeDefId, name, ns, implementation]
    if !nested then return outer
    row Table.exportedType [childFlags, 0, ← string childExportName, 0, childParent]
  let (caller, reference) := make "Caller" do
    let scope ← string "Facade"
    let _ ← row Table.assemblyRef [1, 0, 0, 0, 0, 0, scope, 0, 0]
    let name ← string "InvalidOperationException"
    let ns ← string "System"
    let outer ← row Table.typeRef [6, name, ns]
    let reference ← if nested then row Table.typeRef [4 * tokenRow outer + 3, ← string "Child", 0]
      else pure outer
    link linkDefinition reference 2 definition
    if carry then link linkForwarder reference forwarderSlice exported
    return reference
  let slices ← [caller, facade, library].mapM fun slice => slice.index.toOption
  let .inl named ← (typeRefTarget (.ofSlices slices) 0 resolveFuel reference).toOption | none
  return named.scope

/-- A top-level forwarder selects the public definition in its named implementation.
    A changed flag, name, implementation tag, assembly, visibility or witness fails. -/
theorem checked_forwarder :
    forwarded = some (bytesOf "Core, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null") ∧
    [forwarded (flags := 0), forwarded (typeDefId := 1), forwarded (implementation := 0),
     forwarded (implementation := 1), forwarded (implementation := 4),
     forwarded (implementation := 6), forwarded (implementation := 7),
     forwarded (forwardName := "Exception"), forwarded (declaredName := "Exception"),
     forwarded (targetName := "Other"), forwarded (visibility := 0),
     forwarded (forwarderSlice := 0), forwarded (carry := false)].all Option.isNone := by
  decide +kernel
#print axioms checked_forwarder

/-- The nested export must point to its enclosing export, whose AssemblyRef reaches a public
    outer and public nested definition. Wrong names, parent tags, cycles and visibility fail. -/
theorem checked_nested_forwarder :
    forwarded (nested := true) = some (bytesOf "Core, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null") ∧
    [forwarded (nested := true) (childParent := 10), forwarded (nested := true) (childParent := 5),
     forwarded (nested := true) (childFlags := 0x00200000), forwarded (nested := true) (visibility := 0),
     forwarded (nested := true) (childVisibility := 3), forwarded (nested := true) (childExportName := "Other"),
     forwarded (nested := true) (targetName := "Other")].all Option.isNone := by decide +kernel
#print axioms checked_nested_forwarder

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

/-- `System.Object`, the base of `Lib.Box`, and `Lib.Box` as the platform class it is when no
    slice carries `Lib`. -/
private def libraryPlatform : PlatformTable := platform_table%
  [runtimeType "Object" .objectRoot,
   { scope := bytesOf libScope, parts := [bytesOf "Lib", bytesOf "Box"], kind := .classType }]

/-- Resolve the library type with the supplied assembly order and pins. -/
private def resolveLibrary (others : List MetadataSlice) (pins : List (List Nat) := []) := do
  let env := MetadataEnv.ofSlices (← (own.1 :: others).mapM MetadataSlice.index)
    (platform := libraryPlatform)
    (pins.foldl AssemblyPrefixes.insert {})
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
  let env := MetadataEnv.ofSlices indexes
    ((indexes.map (·.identity)).foldl AssemblyPrefixes.insert {})
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

/-- Minimum elapsed time includes index construction and all lookups. -/
private def measure (base : MetadataIndex) (count : Nat) : IO Nat := do
  let mut times := #[]
  for _ in [:5] do
    let start ← IO.monoNanosNow
    unless exercise base count do throw (IO.userError "assembly lookup lost an identity")
    times := times.push ((← IO.monoNanosNow) - start)
  return (times.qsort (fun left right => left < right))[0]!

#eval do
  let .ok base := lib.index | throw (IO.userError "invalid assembly fixture")
  let _ ← measure base 128
  let small ← measure base 1024
  let large ← measure base 8192
  IO.println s!"assembly lookup minimum ns: {small}, {large}"
  unless large < small * 24 + 30000000 do
    throw (IO.userError "assembly lookup cost grew faster than indexed construction and queries")

end Tests.MetadataAssemblies
