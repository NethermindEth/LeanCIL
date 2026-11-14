import scripts.ProofCost

/-! Regression checks for incremental discovery of kernel constants in the cost frontend. -/

open Lean ProofCost

/-- Synthetic map entries exercise discovery independently of elaboration and kernel checking. -/
def discoveryInfo (name : Name) : ConstantInfo :=
  .defnInfo {
    name, levelParams := [], type := mkConst ``Nat, value := mkNatLit 0
    hints := .abbrev, safety := .safe }

/-- Incremental discovery must return exactly the reference fold's entries, in the same order. -/
unsafe def checkDiscovery (previous current : PHashMap Name ConstantInfo) (known : NameSet) :
    IO Unit := do
  let actual := addedConstants previous current known |>.map (·.1)
  let expected := current.foldl (init := #[]) fun names name _ =>
    if known.contains name then names else names.push name
  unless actual == expected do
    throw <| IO.userError s!"constant discovery differs: {actual} != {expected}"

/-- Discovery remains exact across trie promotions, unchanged commands and restored environments. -/
unsafe def discoveryCases : IO Unit := do
  let mut current : PHashMap Name ConstantInfo := {}
  let mut known : NameSet := {}
  for index in [:1000] do
    let previous := current
    let name := .num `discovery index
    current := current.insert name (discoveryInfo name)
    checkDiscovery previous current known
    known := known.insert name
    checkDiscovery current current known
  let restored : PHashMap Name ConstantInfo := {}
  checkDiscovery current restored known
  checkDiscovery restored current known
  let name := `afterRollback
  let resumed := restored.insert name (discoveryInfo name)
  checkDiscovery current resumed known
  let keys := #[`collisionA, `collisionB]
  let values := keys.map discoveryInfo
  let collision : PHashMap Name ConstantInfo :=
    { root := .collision keys values (by simp [values]) }
  checkDiscovery {} collision {}
  let collisionKnown := ({} : NameSet).insert `collisionA |>.insert `collisionB
  checkDiscovery collision collision collisionKnown
  let expanded : PHashMap Name ConstantInfo :=
    { root := .collision (keys.push name) (values.push (discoveryInfo name)) (by simp [values]) }
  checkDiscovery collision expanded collisionKnown
  IO.println "PASS constant discovery matches the fold across promotions, collisions and rollback"

/-- Total discovery heartbeats for one constant added by each of `count` commands. -/
unsafe def discoveryCost (count : Nat) : IO Nat := do
  let mut current : PHashMap Name ConstantInfo := {}
  let mut known : NameSet := {}
  let mut heartbeats := 0
  for index in [:count] do
    let previous := current
    let name := .num `scaling index
    current := current.insert name (discoveryInfo name)
    let start ← IO.getNumHeartbeats
    let added := addedConstants previous current known
    unless added.size == 1 && added[0]!.1 == name do
      throw <| IO.userError "discovery lost or repeated a constant"
    heartbeats := heartbeats + ((← IO.getNumHeartbeats) - start)
    known := known.insert name
  return heartbeats

/-- Median discovery nanoseconds, with persistent inputs constructed before the timed region. -/
unsafe def discoveryTime (count : Nat) : IO Nat := do
  let mut inputs : Array (PHashMap Name ConstantInfo × PHashMap Name ConstantInfo × NameSet) := #[]
  let mut current : PHashMap Name ConstantInfo := {}
  let mut known : NameSet := {}
  for index in [:count] do
    let previous := current
    let name := .num `timing index
    current := current.insert name (discoveryInfo name)
    inputs := inputs.push (previous, current, known)
    known := known.insert name
  let mut samples : Array Nat := #[]
  for iteration in [:4] do
    let start ← IO.monoNanosNow
    let mut found := 0
    for (before, after, seen) in inputs do
      found := found + (addedConstants before after seen).size
    let elapsed := (← IO.monoNanosNow) - start
    unless found == count do throw <| IO.userError "timed discovery lost constants"
    if iteration != 0 then samples := samples.push elapsed
  return (samples.qsort (· < ·))[1]!

/-- Ten times as many declarations must stay below quadratic discovery growth. -/
unsafe def discoveryScaling : IO Unit := do
  let small ← discoveryCost 1000
  let large ← discoveryCost 10000
  IO.println s!"discovery heartbeats: 1000={small}, 10000={large}"
  let smallTime ← discoveryTime 1000
  let largeTime ← discoveryTime 10000
  IO.println s!"discovery nanoseconds: 1000={smallTime}, 10000={largeTime}"
  unless largeTime < 25 * smallTime do
    throw <| IO.userError "constant discovery exceeded discovery growth bound"

#eval discoveryCases
#eval discoveryScaling
