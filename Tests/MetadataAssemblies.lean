import Tests.MetadataWorld
import Lean

/-!
# Assembly lookup regressions

Assembly lookups preserve positional links, the first identity match and pinned names, and an
`Assembly` row names exactly one assembly. Scaling varies assembly count independently of
method instructions and metadata rows.
-/

namespace Tests.MetadataAssemblies

open CIL CIL.Extraction Tests.MetadataBuilder Tests.MetadataWorld

set_option maxRecDepth 32768

/-- Resolve a caller's TypeRef through the facade's physical ExportedType and AssemblyRef rows. -/
private def forwarded (flags := 0x00200000) (typeDefId := 0) (implementation := 5)
    (forwardName := "InvalidOperationException") (targetName := "Core")
    (declaredName := "InvalidOperationException") (visibility := 1)
    (forwarderSlice := 1) (carry := true) (nested := false) (childParent := 6)
    (facadeCulture := "") (referenceCulture := "")
    (childFlags := 0) (childVisibility := 2) (childExportName := "Child") :
    Except MetadataError (Option AssemblyName) := do
  let make := fun (name : String) (entries : Step Nat) => build entries (bytesOf name)
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
    let culture ← string facadeCulture
    let _ ← row Table.assemblyRef [1, 0, 0, 0, 0, 0, dest, culture, 0]
    let name ← string forwardName
    let ns ← string "System"
    let outer ← row Table.exportedType [flags, typeDefId, name, ns, implementation]
    if !nested then return outer
    row Table.exportedType [childFlags, 0, ← string childExportName, 0, childParent]
  let (caller, reference) := make "Caller" do
    let scope ← string "Facade"
    let culture ← string referenceCulture
    let _ ← row Table.assemblyRef [1, 0, 0, 0, 0, 0, scope, culture, 0]
    let name ← string "InvalidOperationException"
    let ns ← string "System"
    let outer ← row Table.typeRef [6, name, ns]
    let reference ← if nested then row Table.typeRef [4 * tokenRow outer + 3, ← string "Child", 0]
      else pure outer
    link linkDefinition reference 2 definition
    if carry then link linkForwarder reference forwarderSlice exported
    return reference
  let slices ← [caller, facade, library].mapM MetadataSlice.index
  let .inl named ← typeRefTarget (.ofSlices slices) 0 resolveFuel reference
    | throw (.unresolvedType reference)
  return named.assembly

/-- The assembly the forwarders of `forwarded` lead to. -/
private def coreAssembly : AssemblyName := unsignedAssembly name!"Core"

/-- A top-level forwarder selects the public definition in its named implementation.
    A changed flag, name, implementation tag, assembly, visibility or witness fails. -/
theorem checked_forwarder :
    forwarded.toOption = some (some coreAssembly) ∧
    [forwarded (flags := 0), forwarded (typeDefId := 1), forwarded (implementation := 0),
     forwarded (implementation := 1), forwarded (implementation := 4),
     forwarded (implementation := 6), forwarded (implementation := 7),
     forwarded (forwardName := "Exception"), forwarded (declaredName := "Exception"),
     forwarded (targetName := "Other"), forwarded (visibility := 0),
     forwarded (forwarderSlice := 0), forwarded (carry := false)].all (fun result => !result.isOk) := by
  decide +kernel
#print axioms checked_forwarder

/-- The nested export must point to its enclosing export, whose AssemblyRef reaches a public
    outer and public nested definition. Wrong names, parent tags, cycles and visibility fail. -/
theorem checked_nested_forwarder :
    (forwarded (nested := true)).toOption = some (some coreAssembly) ∧
    [forwarded (nested := true) (childParent := 10), forwarded (nested := true) (childParent := 5),
     forwarded (nested := true) (childFlags := 0x00200000), forwarded (nested := true) (visibility := 0),
     forwarded (nested := true) (childVisibility := 3), forwarded (nested := true) (childExportName := "Other"),
     forwarded (nested := true) (targetName := "Other")].all (fun result => !result.isOk) := by decide +kernel
#print axioms checked_nested_forwarder

/-- Empty culture and the literal bytes of "neutral" spell the same display name. A reference
    naming the culture `neutral` names no carried assembly, and a forwarder naming it cannot bind
    the neutral assembly. -/
theorem forwarded_culture_columns :
    let rejects := fun (result : Except MetadataError (Option AssemblyName)) error =>
      match result with
      | .error found => found == error
      | .ok _ => false
    rejects (forwarded (referenceCulture := "neutral")) (.unresolvedType 0x01000001) = true ∧
    rejects (forwarded (facadeCulture := "neutral")) (.operandMismatch 0x01000001) = true ∧
    rejects (forwarded (nested := true) (referenceCulture := "neutral"))
      (.unresolvedType 0x01000002) = true ∧
    rejects (forwarded (nested := true) (facadeCulture := "neutral"))
      (.operandMismatch 0x01000002) = true := by
  decide +kernel
#print axioms forwarded_culture_columns

/-- `System.Object`, the base of `Lib.Box`, and `Lib.Box` as the platform class it is when no
    slice carries `Lib`. -/
private def libraryPlatform : PlatformTable := platform_table%
  [runtimeType "Object" .objectRoot,
   { scope := bytesOf libScope, parts := [bytesOf "Lib", bytesOf "Box"], kind := .classType }]

/-- Resolve the library type with the supplied assembly order and pins. -/
private def resolveLibrary (others : List MetadataSlice) (pins : List AssemblyName := []) := do
  let env := MetadataEnv.ofSlices (← (own.1 :: others).mapM MetadataSlice.index)
    (platform := libraryPlatform) (indexPinNames pins)
  typeRefNamed env 0 resolveFuel tokens.boxRef none

/-- Compare the exact error while retaining the successful type separately. -/
private def failedWith (result : Except MetadataError NamedType) (error : MetadataError) : Bool :=
  match result with
  | .error found => found == error
  | .ok _ => false

/-- `lib`'s `Assembly` row with its culture column naming the string `neutral`. -/
private def neutralLib : AssemblyMetadata :=
  let cultureOffset := 0x200
  { lib.assembly with
    assemblyRow := lib.assembly.assemblyRow.take 20 ++ [cultureOffset % 256, cultureOffset / 256]
    strings := lib.assembly.strings ++ [(cultureOffset, bytesOf "neutral" ++ [0])] }

/-- A row whose culture is the name `neutral` has the display name of the neutral assembly but
    names another assembly, so the neutral pin does not identify it. -/
theorem neutral_culture_is_another_assembly :
    (neutralLib.name.map (·.spelling)).toOption = some libAssembly.spelling ∧
    AssemblyIdentified lib.assembly libAssembly ∧
    ¬ AssemblyIdentified neutralLib libAssembly := by decide +kernel
#print axioms neutral_culture_is_another_assembly

/-- Duplicate identities retain their first position; a link to a different position is refused. -/
theorem first_identity :
    (resolveLibrary [lib, lib]).isOk = true ∧
    failedWith (resolveLibrary [own.1, lib]) (.unresolvedType tokens.boxRef) = true := by
  decide +kernel
#print axioms first_identity

/-- Missing carried assemblies are external only when no pin has their name, at any version. -/
theorem pinned_missing :
    (resolveLibrary []).isOk = true ∧
    failedWith (resolveLibrary [] [libAssembly]) (.missingSlice tokens.boxRef) = true ∧
    failedWith (resolveLibrary [] [unsignedAssembly name!"Lib" 2])
      (.missingSlice tokens.boxRef) = true := by decide +kernel
#print axioms pinned_missing

/-- A carried version cannot satisfy a reference to another version of the same pinned name. -/
theorem wrong_version :
    let versioned := (build libWorld (bytesOf "Lib") 2).1
    failedWith (resolveLibrary [versioned] [libAssembly])
      (.missingSlice tokens.boxRef) = true := by decide +kernel
#print axioms wrong_version

/-- Fixed-width names keep the benchmark's byte count proportional to assembly count. -/
private def identity (position : Nat) : AssemblyName :=
  { unsignedAssembly name!"A" with
    name := ⟨(321 * 256 + position / 255 + 1) * 256 + position % 255 + 1⟩ }

/-- Construct and query each assembly once, including the pin lookup for a missing version. -/
private def exercise (base : MetadataIndex) (count : Nat) : Bool := Id.run do
  let indexes := (List.range count).map fun position => { base with identity := identity position }
  let env := MetadataEnv.ofSlices indexes
    (indexPinNames (indexes.map (·.identity)))
  for position in [:count] do
    let scope := identity position
    if env.identities[scope]? != some position then return false
    if (env.slice position 0).toOption.map (·.identity) != some scope then return false
    if !env.pinned.contains scope.name then return false
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
