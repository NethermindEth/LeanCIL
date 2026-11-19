import CIL.RuntimeModel
import CIL.Resolution
import CIL.Extraction.Generics
import CIL.Extraction.Lockstep
import CIL.Extraction.FlowIndex
import CIL.Extraction.MetadataBytes

/-!
# Runtime model tables

A model table gives the runtime model a `call` or `newobj` of a typed `MethodRef` stands for,
from model entries searched by the method's name code. At the leaf the entry's name, opcode and
owner head are compared, and the entry resolves the whole reference.
`model_table%` writes a table as a literal balanced tree, so a lookup costs the depth of the tree
and the comparison of one reference. Modules that define entries import this one.
`CIL.Extraction.RuntimeModels` gathers the entries into the runtime table.
-/

namespace CIL.Extraction

/-- The type constructor of `type` with its type arguments removed, so every instance of a
    generic owner such as `Span<T>` has one head. -/
def TypeExpr.genericHead : TypeExpr → TypeExpr
  | .apply head _ => head.genericHead
  | type => type

/-- The methods of one opcode, owner head and name. A modelled call must resolve its closed
    reference and have a declaration the entry accepts. -/
structure ModelEntry where
  opcode : CallOpcode
  owner : TypeExpr
  name : MetadataName
  declares : OpenSignature → Bool
  resolve : (TypeExpr → ValueShape) → MethodRef → Option RuntimeModel
  /-- A family owned in full, including unresolved overloads, with its exact external operand. -/
  familyTarget : Option (String × MethodId) := none

/-- The declaration and the raw call fields agree with the selected member. -/
def ModelEntry.bindsSite (entry : ModelEntry) (site : CallSite) : Bool :=
  entry.declares site.declared && match entry.familyTarget with
    | none => true
    | some (name, target) =>
      site.name == name && site.target == target && site.ownerArgumentCount == 0 &&
        site.typeArguments == site.method.methodArguments &&
        site.parameterCount == site.method.parameters.length &&
        site.returnsValue == (site.returnType != .void)

/-- An entry for one declaration and closed method reference under `opcode`. -/
def ModelEntry.exact (opcode : CallOpcode) (method : MethodRef) (declared : OpenSignature)
    (model : RuntimeModel) : ModelEntry :=
  { opcode, owner := method.owner.genericHead, name := method.name,
    declares := (· == declared),
    resolve := fun _ reference => if reference = method then some model else none }

/-- The search key of an entry: the code of its method name. -/
def ModelEntry.key (entry : ModelEntry) : Nat := entry.name.code

/-- Whether two entries claim the same opcode, owner head and name, so one would hide the other. -/
def ModelEntry.sameSlot (left right : ModelEntry) : Bool :=
  left.key == right.key && left.opcode == right.opcode && left.owner == right.owner

/-- Model entries by name code; the entries under one code are tried in order. -/
abbrev ModelTable := SearchTree (List ModelEntry)

/-- The entry for the method's name, opcode and owner head. -/
def ModelTable.entry? (table : ModelTable) (opcode : CallOpcode) (method : MethodRef) :
    Option ModelEntry := do
  let entries ← table.find? method.name.code
  entries.find? fun entry =>
    entry.name == method.name && entry.opcode == opcode &&
      entry.owner == (if entry.familyTarget.isSome then method.owner else method.owner.genericHead)

/-- The model of a call under `opcode` to the closed reference `method`. -/
def ModelTable.find (table : ModelTable) (environment : LayoutEnvironment)
    (opcode : CallOpcode) (method : MethodRef) : Option RuntimeModel := do
  let entry ← table.entry? opcode method
  entry.resolve environment.valueShape method

/-- A family claims its name before overload resolution. Other entries share overlapping names
    with lowerings and claim the closed overloads they resolve. -/
def ModelTable.claims (table : ModelTable) (environment : LayoutEnvironment)
    (opcode : CallOpcode) (method : MethodRef) : Bool :=
  (table.entry? opcode method).any fun entry =>
    entry.familyTarget.isSome || (entry.resolve environment.valueShape method).isSome

/-- `groups` with `entry` added at the end of the group of its key. -/
def ModelTable.insertGroup (entry : ModelEntry) :
    List (Nat × List ModelEntry) → List (Nat × List ModelEntry)
  | [] => [(entry.key, [entry])]
  | (key, group) :: rest =>
    if entry.key < key then (entry.key, [entry]) :: (key, group) :: rest
    else if entry.key = key then (key, group ++ [entry]) :: rest
    else (key, group) :: insertGroup entry rest

/-- The entries grouped by key in ascending key order, each group in list order. Structural
    recursion keeps the grouping reducible, so a literal table is equal to it by `rfl`. -/
def ModelTable.groups (entries : List ModelEntry) : List (Nat × List ModelEntry) :=
  entries.foldl (fun groups entry => ModelTable.insertGroup entry groups) []

/-- The balanced table of `entries`, which `model_table%` writes out as a literal. -/
def ModelTable.ofEntries (entries : List ModelEntry) : ModelTable :=
  SearchTree.ofSorted (ModelTable.groups entries)

/-- Whether no two entries of one group claim the same slot. -/
def ModelTable.slotsDistinct (entries : List ModelEntry) : Bool :=
  (ModelTable.groups entries).all fun (_, group) => distinct group
where
  /-- No entry of the list shares a slot with a later one. -/
  distinct : List ModelEntry → Bool
    | [] => true
    | entry :: rest => !rest.any (entry.sameSlot ·) && distinct rest

open Lean Meta in
/-- The literal balanced tree of key-ordered groups, split as `SearchTree.ofSorted` splits. -/
private partial def literalTree (groups : Array (Nat × Array Expr)) : MetaM Expr := do
  let valueType := mkApp (mkConst ``List [0]) (mkConst ``ModelEntry)
  if groups.isEmpty then return mkApp (mkConst ``SearchTree.leaf) valueType
  let leftCount := groups.size / 2
  let (key, cells) := groups[leftCount]!
  return mkApp5 (mkConst ``SearchTree.node) valueType (← literalTree (groups.extract 0 leftCount))
    (mkNatLit key) (← mkListLit (mkConst ``ModelEntry) cells.toList)
    (← literalTree (groups.extract (leftCount + 1) groups.size))

open Lean Meta Elab Term in
/-- `model_table% entries` is `ModelTable.ofEntries entries` written out as a literal tree whose
    leaves hold the entry terms, so the kernel never sorts or splits the list. Entries that share a
    slot are an error. -/
elab "model_table% " entries:term : term => do
  let listType := mkApp (mkConst ``List [0]) (mkConst ``ModelEntry)
  let list ← elabTermEnsuringType entries listType
  synthesizeSyntheticMVarsNoPostponing
  let list ← instantiateMVars list
  let distinct ← unsafe evalExpr Bool (mkConst ``Bool)
    (mkApp (mkConst ``ModelTable.slotsDistinct) list)
  unless distinct do throwError "model table: two entries share an opcode, owner and name"
  let mut keyed : Array (Nat × Expr) := #[]
  for cell in ← literalCells list do
    keyed := keyed.push
      (← unsafe evalExpr Nat (mkConst ``Nat) (mkApp (mkConst ``ModelEntry.key) cell), cell)
  let mut groups : Array (Nat × Array Expr) := #[]
  for (key, cell) in keyed.toList.mergeSort fun left right => left.1 ≤ right.1 do
    match groups.back? with
    | some (last, cells) =>
      groups := if last = key then groups.pop.push (key, cells.push cell)
        else groups.push (key, #[cell])
    | none => groups := groups.push (key, #[cell])
  literalTree groups

/-- A value `find?` gives is one of the tree's entries. -/
theorem SearchTree.find?_mem_toList {α : Type} :
    ∀ (tree : SearchTree α) (key : Nat) (value : α), tree.find? key = some value →
      (key, value) ∈ tree.toList
  | .leaf, _, _, found => by simp [SearchTree.find?] at found
  | .node left root stored right, key, value, found => by
    simp only [SearchTree.find?] at found
    simp only [SearchTree.toList, List.mem_append, List.mem_cons]
    split at found
    · exact .inl (SearchTree.find?_mem_toList left key value found)
    · exact .inr (.inr (SearchTree.find?_mem_toList right key value found))
    · rename_i same
      cases found
      exact .inr (.inl (by rw [Nat.compare_eq_eq.mp same]))

#print axioms SearchTree.find?_mem_toList

/-- Every model `entry` resolves has `property`. -/
def ModelEntry.Yields (entry : ModelEntry) (property : RuntimeModel → Prop) : Prop :=
  ∀ environment method model, entry.resolve environment method = some model → property model

/-- An exact entry resolves only its own model. -/
@[simp] theorem ModelEntry.exact_yields {opcode : CallOpcode} {method : MethodRef}
    {declared : OpenSignature} {model : RuntimeModel} {property : RuntimeModel → Prop} :
    (ModelEntry.exact opcode method declared model).Yields property ↔ property model := by
  constructor
  · intro yields
    exact yields (LayoutEnvironment.valueShape {}) method model (by simp [ModelEntry.exact])
  · intro holds environment reference resolved found
    simp only [ModelEntry.exact] at found
    split at found
    · cases found
      exact holds
    · cases found

#print axioms ModelEntry.exact_yields

/-- A model a table gives has every property each of its entries' models has, so a proof about
    the models of a table covers an added entry once that entry's models have the property. -/
theorem ModelTable.find_yields {table : ModelTable} {property : RuntimeModel → Prop}
    (every : ∀ group ∈ table.toList, ∀ entry ∈ group.2, entry.Yields property)
    {environment : LayoutEnvironment} {opcode : CallOpcode} {method : MethodRef}
    {model : RuntimeModel} (found : table.find environment opcode method = some model) :
    property model := by
  obtain ⟨entry, selected, resolved⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨entries, filed, member⟩ := Option.bind_eq_some_iff.mp selected
  exact every _ (SearchTree.find?_mem_toList _ _ _ filed) entry
    (List.mem_of_find?_eq_some member) environment.valueShape method model resolved

#print axioms ModelTable.find_yields

/-- The table of runtime models checked at call sites. -/
structure ModelCatalog where
  table : ModelTable

/-- The call opcodes a model can stand for, by raw opcode. -/
def callOpcode? : Nat → Option CallOpcode
  | 40 => some .call
  | 115 => some .newobj
  | _ => none

end CIL.Extraction
