import CIL.Extraction.Dispatch
import Lean

/-! Scaling and rejection checks for virtual and indirect call target tables. -/

namespace Tests.DispatchCatalogScaling
open CIL CIL.Extraction

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The sole assembly providing the dispatch bodies. -/
private def pin : AssemblyPin := ⟨⟨name!"Fixture", ⟨1, 0, 0, 0⟩, name!"", none⟩⟩

/-- The assembly-qualified scope used by the class names. -/
private def scope := "Fixture, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

/-- Three-letter ASCII class names with distinct metadata codes at all measured sizes. -/
private def classId (index : Nat) : TypeExpr :=
  let alphabet := 26
  let code := (name!"AAA").code + index % alphabet + 256 * (index / alphabet)
  .object scope ⟨[⟨name!"", ⟨code⟩⟩]⟩

/-- The concrete, newly introduced slot at the root of the hierarchy. -/
private def slot : DispatchMethod := {
  token := 5, name := "Read", hasThis := true, isPublic := true, isAbstract := false,
  isVirtual := true, hasBody := true, genericArity := 0, explicitThis := false,
  callingConvention := 0, attributes := 0x140, implementation := 0,
  returnType := .void, parameters := [], overrides := [] }

/-- A call of the root's instance slot. -/
private def site : CallSite := {
  declared := { convention := 0x20 },
  method := {
    owner := classId 0, name := name!"Read", hasThis := true, genericArity := 0,
    returnType := .void, parameters := [] },
  name := "Read", target := .managed slot.token,
  typeArguments := [], parameterCount := 0, returnsValue := false }

/-- The extracted method matching the root slot's token, receiver and body requirements. -/
private def callee : SpecializedMethod := ⟨[], {
  token := slot.token, owner := (managedOwner (classId 0)).get!.1, hasThis := true,
  explicitThis := false, callingConvention := 0, attributes := slot.attributes, implementation := 0,
  returnType := .void, parameters := [], locals := [], initLocals := false, maxStack := 0,
  genericParameters := [], code := [⟨0, 42, .none⟩], receiverClass := some (classId 0) }, pin⟩

/-- A class whose only virtual method is inherited from the root. -/
private def entry (index : Nat) : DispatchType := {
  identity := classId index, valueType := false, interfaceType := false, interfaces := [],
  methods := if index == 0 then [slot] else [], assembly := pin,
  base := if index == 0 then .void else classId (index - 1) }

/-- Check the entire virtual table, including the index, receiver coverage and selected bodies. -/
private def virtual (catalog : List DispatchType) (targets : List DispatchType) : Bool :=
  let index := DispatchIndex.ofTypes catalog
  virtualTableValid catalog (fun id => (index.findType id).map (·.raw))
    (fun position => if position == 0 then some callee else none) site
    (targets.map fun target => (target.identity, 0)) 1

/-- Every concrete class in the chain must select the one inherited body. -/
private def virtualChain (count : Nat) : Bool :=
  let catalog := (List.range count).map entry
  virtual catalog catalog

/-- Check every scoped identity in the supplied order against its selected static body. -/
private def indirectTable (indices : List Nat) (identity : Nat → ManagedIdentity) : Bool :=
  let targets := indices.map fun index => (⟨identity index, index⟩ : ManagedTarget)
  let methods := fun index => some { callee with closed := { callee.closed with
    token := (identity index).token, owner := (identity index).owner,
    hasThis := false, receiverClass := none } }
  managedIndirectMatches methods ⟨0, 41, .indirectCall .void [] false false 0⟩ ⟨.void, []⟩ targets

/-- Distinct method rows in one module. -/
private def methodId (index : Nat) : ManagedIdentity := ⟨"Fixture", index + 1, []⟩

/-- Tokens appear in metadata order. -/
private def indirect (count : Nat) := indirectTable (List.range count) methodId

/-- Descending metadata rows are also strictly ordered. -/
private def reversedIndirect (count : Nat) := indirectTable (List.range count).reverse methodId

/-- Swapping each adjacent pair forces unordered token checks at every measured size. -/
private def shuffledIndirect (count : Nat) :=
  indirectTable ((List.range count).map (· ^^^ 1)) methodId

/-- Two owners reuse every metadata token, requiring complete owner-qualified identities. -/
private def scopedIndirect (count : Nat) :=
  indirectTable (List.range count) fun index =>
    ⟨if index % 2 == 0 then "Fixture" else "Other", index / 2 + 1, []⟩

/-- A repeated full identity anywhere in an unordered table disqualifies the entire call. -/
theorem repeatedIndirect : indirectTable [2, 1, 3, 2] methodId = false := by decide +kernel

#print axioms repeatedIndirect

/-- An override naming an ancestor or descendant on a path disqualifies it in either direction. -/
private def withOverride (declaring owner : Nat) : List DispatchType :=
  (List.range 4).map fun index =>
    let item := entry index
    if index != declaring then item else
      { item with methods := if index == 0 then
          [{ slot with overrides := [(slot.token, classId owner)] }]
        else [{ slot with name := "Unrelated", overrides := [(slot.token, classId owner)] }] }

/-- Catalog and target order do not affect resolution, and the target table must be complete. -/
theorem targetCoverage :
    let catalog := (List.range 4).map entry
    virtual catalog.reverse catalog.reverse = true ∧
      virtual catalog (catalog.take 3) = false ∧
      virtual catalog (catalog ++ [entry 1]) = false := by
  decide +kernel

#print axioms targetCoverage

/-- Ancestor and descendant override collisions fail, while an unrelated override owner passes. -/
theorem overrideExclusion :
    virtual (withOverride 0 3) (withOverride 0 3) = false ∧
      virtual (withOverride 3 0) (withOverride 3 0) = false ∧
      virtual (withOverride 2 9) (withOverride 2 9) = true := by decide +kernel

#print axioms overrideExclusion

/-- Classes with self-cycles outside the selected hierarchy cannot contribute a target. -/
private def unrelatedCycles (count : Nat) : Bool :=
  let others := (List.range count).map fun index =>
    let item := entry (index + 1)
    { item with base := item.identity }
  virtual (entry 0 :: others) [entry 0]

/-- Tangled ancestors outside the slot's hierarchy never resolve to its body. -/
theorem cyclicTargets :
    let cycle := [{ entry 1 with base := classId 2 }, { entry 2 with base := classId 1 }, entry 3]
    let catalog := entry 0 :: cycle
    virtual catalog [entry 0] = true ∧ virtual catalog catalog = false := by decide +kernel

#print axioms cyclicTargets

open Lean Elab Command Meta in
run_cmd do
  let maxFourfoldGrowth := 6
  for (label, check) in [("virtual chain", ``virtualChain), ("indirect table", ``indirect),
      ("reversed indirect table", ``reversedIndirect),
      ("shuffled indirect table", ``shuffledIndirect),
      ("shared token table", ``scopedIndirect), ("unrelated cycles", ``unrelatedCycles)] do
    let mut previous := 0
    for count in [8, 32, 128] do
      let (claim, proof) ← liftTermElabM do
        let claim ← mkEq (mkApp (mkConst check) (mkNatLit count)) (mkConst ``Bool.true)
        pure (claim, ← mkEqRefl (mkConst ``Bool.true))
      let start ← IO.getNumHeartbeats
      match Kernel.check (← getEnv) {} (Expr.letE `checked claim proof (.bvar 0) false) with
      | .error error => throwKernelException error
      | .ok _ => pure ()
      let cost := (← IO.getNumHeartbeats) - start
      if previous != 0 && cost > previous * maxFourfoldGrowth then
        throwError "{label} grew from {previous} to {cost} kernel heartbeats for 4× the entries"
      logInfo m!"{label} with {count} entries: {cost} kernel heartbeats"
      previous := cost

end Tests.DispatchCatalogScaling
