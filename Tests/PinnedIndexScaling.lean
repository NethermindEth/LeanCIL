import CIL.Extraction.BodyDecoding
import Lean

/-! Package pin construction and independent method checks have separate cost bounds. -/

namespace Tests.PinnedIndexScaling
open CIL.Extraction
set_option maxHeartbeats 0
set_option maxRecDepth 32768

/-- Fixed-width identities keep total pin bytes proportional to the pin count. -/
private def identities (count : Nat) : List (List Nat) :=
  (List.range count).map fun position => [65, position / 256, position % 256, 44]

/-- One checked package index shared by every small-package method. -/
private def small : PinnedIndex := cil_pin_index identities 128
#print axioms small

/-- One checked package index shared by every medium-package method. -/
private def medium : PinnedIndex := cil_pin_index identities 512
#print axioms medium

/-- One checked package index shared by every large-package method. -/
private def large : PinnedIndex := cil_pin_index identities 2048
#print axioms large

/-- Each independent method has fixed metadata and queries the package's checked pin index. -/
private def methodCheck (pinned : PinnedIndex) (position : Nat) : Bool :=
  let metadata : MethodMetadata := { own := { corlib := position } }
  let tables : IndexTables :=
    { rows := .leaf, strings := .leaf, blobs := .leaf,
      userStrings := .leaf, links := .leaf, instanceBefore := .leaf, instanceTotal := .leaf,
      genericOwners := .leaf }
  match metadata.environmentWith [[88]] [tables] pinned with
  | .error _ => false
  | .ok env => env.pinned.matches [65, 0, 0, 44, 99]

/-- Each batch repeats complete package construction and independent method checks. -/
private def runtimeCost (pinCount methodCount repetitions : Nat) : IO (Nat × Nat) := do
  let start ← IO.monoNanosNow
  let startHeartbeats ← IO.getNumHeartbeats
  for _ in [:repetitions] do
    let pinned := PinnedIndex.ofIdentities (identities pinCount)
    unless (List.range methodCount).all (methodCheck pinned) do
      throw (IO.userError "a package pin disappeared")
  let heartbeats := (← IO.getNumHeartbeats) - startHeartbeats
  return (((← IO.monoNanosNow) - start) / repetitions, heartbeats / repetitions)

#eval do
  let sizes := #[128, 512, 2048]
  let combinations := sizes.flatMap fun pins => sizes.map fun methods => (pins, methods)
  let repetitions := 20
  let rounds := 9
  for (pins, methods) in combinations do
    let _ ← runtimeCost pins methods repetitions
  let mut samples : Array (Array Nat × Array Nat) := combinations.map fun _ => (#[], #[])
  for round in [:rounds] do
    let indices := Array.range combinations.size
    for index in (if round % 2 == 0 then indices else indices.reverse) do
      let (pins, methods) := combinations[index]!
      let (elapsed, heartbeats) ← runtimeCost pins methods repetitions
      let (times, allocations) := samples[index]!
      samples := samples.set! index (times.push elapsed, allocations.push heartbeats)
  let mut previous := 0
  let mut previousHeartbeats := 0
  for index in [:combinations.size] do
    let (pinCount, methodCount) := combinations[index]!
    let (times, allocations) := samples[index]!
    let median := (times.qsort (· < ·))[rounds / 2]!
    let heartbeats := (allocations.qsort (· < ·))[rounds / 2]!
    IO.println s!"pin runtime: {pinCount} pins, {methodCount} methods, {median} ns"
    -- Runtime heartbeats count allocation work, independently of scheduler delays.
    IO.println (s!"pin allocation work: {pinCount} pins, {methodCount} methods, " ++
      s!"{heartbeats} heartbeats")
    if pinCount == methodCount then
      if previous != 0 && median > previous * 6 + 1000000 then
        throw (IO.userError "package pin runtime grew faster than package size")
      if previousHeartbeats != 0 && heartbeats > previousHeartbeats * 6 then
        throw (IO.userError "package pin allocation work grew faster than package size")
      previous := median
      previousHeartbeats := heartbeats

open Lean Meta Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let mut previousQuotation := 0
  let mut previousConstruction := 0
  let mut previousTotal := 0
  for (pinCount, indexName) in ([(128, ``small), (512, ``medium),
      (2048, ``large)] : List (Nat × Name)) do
    let start ← IO.getNumHeartbeats
    let _ ← liftTermElabM do
      let expressionSyntax ← `(cil_pin_index identities $(quote pinCount))
      Term.elabTerm expressionSyntax (some (mkConst ``PinnedIndex))
    let quotation := (← IO.getNumHeartbeats) - start
    logInfo m!"pin quotation: {pinCount} pins, {quotation} heartbeats"
    if previousQuotation != 0 && quotation > previousQuotation * 6 then
      throwError "pin quotation grew faster than package size"
    previousQuotation := quotation
    let index := (← getConstInfo indexName).value!
    let start ← IO.getNumHeartbeats
    match Kernel.check (← getEnv) {}
        (Expr.letE `checked (mkConst ``PinnedIndex) index (.bvar 0) false) with
    | .error error => throwKernelException error
    | .ok _ => pure ()
    let construction := (← IO.getNumHeartbeats) - start
    logInfo m!"pin construction: {pinCount} pins, {construction} heartbeats"
    if previousConstruction != 0 && construction > previousConstruction * 6 then
      throwError "pin construction grew faster than indexed construction"
    previousConstruction := construction
    let mut previousMethods := 0
    for methodCount in [128, 512, 2048] do
      let mut cost := 0
      for position in [:methodCount] do
        let (statement, proof) ← liftTermElabM do
          let statement ← mkEq
            (mkApp2 (mkConst ``methodCheck) (mkConst indexName) (mkNatLit position))
            (mkConst ``Bool.true)
          pure (statement, ← mkEqRefl (mkConst ``Bool.true))
        let start ← IO.getNumHeartbeats
        match Kernel.check (← getEnv) {}
            (Expr.letE `checked statement proof (.bvar 0) false) with
        | .error error => throwKernelException error
        | .ok _ => pure ()
        cost := cost + ((← IO.getNumHeartbeats) - start)
      logInfo m!"pin methods: {pinCount} pins, {methodCount} methods, {cost} heartbeats"
      if previousMethods != 0 && cost > previousMethods * 6 then
        throwError "independent method pin checks grew faster than method count"
      previousMethods := cost
      if methodCount == pinCount then
        let total := construction + cost
        if previousTotal != 0 && total > previousTotal * 6 then
          throwError "package pin checks grew faster than package size"
        previousTotal := total

/-- Materialized indexes retain every complete identity's prefix. -/
theorem materialized_pin_present : small.prefixes.matches [65, 0, 0, 44, 99] = true := by
  decide +kernel
#print axioms materialized_pin_present

/-- An empty trie cannot certify a package containing a nonempty pin. -/
theorem omitted_prefix_rejected :
    ({} : AssemblyPrefixes) ≠ ([([65] : List Nat)].map assemblyStem).foldl
      AssemblyPrefixes.insert {} := by
  intro same
  have query := congrArg (fun trie => trie.matches [65]) same
  have impossible : false = true := query
  cases impossible
#print axioms omitted_prefix_rejected

end Tests.PinnedIndexScaling
