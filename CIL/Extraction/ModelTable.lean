import CIL.RuntimeModel
import CIL.Extraction.CallLayouts
import CIL.Extraction.Generics
import CIL.Extraction.Lockstep
import CIL.Extraction.FlowIndex
import CIL.Extraction.SearchTreeLiteral

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

/-- The raw operand a closed overload accepts. An external member binds its name, exact target
    and open declaration, including aggregate indices from the selected method. -/
inductive ModelOperand where
  | declaration (accepts : OpenSignature → Bool)
  | external (declared : MethodRef → OpenSignature) (name : String)
      (target : MethodRef → Option String)

/-- Whether the raw declaration and redundant fields describe this operand. -/
def ModelOperand.bindsSite (operand : ModelOperand) (site : CallSite) : Bool :=
  match operand with
  | .declaration accepts => accepts site.declared
  | .external declared name target =>
    site.declared == declared site.method && site.name == name &&
      (target site.method).any (fun id => site.target == .external id) &&
      site.ownerArgumentCount == 0 && site.typeArguments == site.method.methodArguments &&
      site.parameterCount == site.method.parameters.length &&
      site.returnsValue == (site.returnType != .void)

/-- One overload's raw operand and runtime semantics. The closed member selects the overload
    before either the raw fields or the layouts are checked. -/
structure ModelOverload where
  operand : ModelOperand
  resolve : CallLayouts → MethodRef → Option RuntimeModel
  accepts : MethodRef → Bool := fun _ => true

/-- The overloads filed under one opcode, owner and name. A reserved name claims even a
    closed reference for which none of its overloads resolves. -/
structure ModelEntry where
  opcode : CallOpcode
  owner : TypeExpr
  name : MetadataName
  overloads : List ModelOverload
  ownsName : Bool := false

/-- A closed reference must identify exactly one overload for binding and execution. -/
def ModelEntry.select? (entry : ModelEntry) (method : MethodRef) : Option ModelOverload :=
  select entry.overloads
where
  /-- Once a match is found, a second match makes the closed reference ambiguous. -/
  select : List ModelOverload → Option ModelOverload
    | [] => none
    | overload :: rest =>
      if overload.accepts method then
        if rest.any (fun other => other.accepts method) then none else some overload
      else select rest

/-- A successful selection always names a row of this entry. -/
theorem ModelEntry.select?_mem {entry : ModelEntry} {method : MethodRef} {row : ModelOverload}
    (selected : entry.select? method = some row) : row ∈ entry.overloads := by
  change ModelEntry.select?.select method entry.overloads = some row at selected
  generalize entry.overloads = rows at *
  induction rows with
  | nil => cases selected
  | cons first rest ih =>
    simp only [ModelEntry.select?.select] at selected
    split at selected
    · split at selected
      · contradiction
      · cases selected
        exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih selected)

#print axioms ModelEntry.select?_mem

/-- The selected overload binds the site's declaration and raw operand. -/
def ModelEntry.bindsSite (entry : ModelEntry) (site : CallSite) : Bool :=
  (entry.select? site.method).any (fun overload => overload.operand.bindsSite site)

/-- The model of the selected overload under the checked layouts. -/
def ModelEntry.resolve (entry : ModelEntry) (reader : CallLayouts) (method : MethodRef) :
    Option RuntimeModel :=
  (entry.select? method).bind (fun overload => overload.resolve reader method)

/-- A slot with a single binding needs no closed discriminator beyond its resolver. -/
def ModelEntry.single (opcode : CallOpcode) (owner : TypeExpr) (name : MetadataName)
    (operand : ModelOperand) (resolve : CallLayouts → MethodRef → Option RuntimeModel)
    (ownsName := false) : ModelEntry :=
  { opcode, owner, name, ownsName, overloads := [{ operand, resolve }] }

/-- A single binding passes the closed reference directly to its resolver. -/
@[simp] theorem ModelEntry.resolve_single (opcode owner name operand resolve ownsName)
    (reader : CallLayouts) (method : MethodRef) :
    (ModelEntry.single opcode owner name operand resolve ownsName).resolve reader method =
      resolve reader method := rfl

#print axioms ModelEntry.resolve_single

/-- An entry for one declaration and closed method reference under `opcode`. -/
def ModelEntry.exact (opcode : CallOpcode) (method : MethodRef) (declared : OpenSignature)
    (model : RuntimeModel) : ModelEntry :=
  .single opcode method.owner.genericHead method.name (.declaration (· == declared))
    (fun _ reference => if reference = method then some model else none)

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
      entry.owner == (if entry.ownsName && !(entry.owner matches .constructor ..) then method.owner
        else method.owner.genericHead)

/-- The model of a call under `opcode` to the closed reference `method`. -/
def ModelTable.find (table : ModelTable) (environment : LayoutEnvironment)
    (opcode : CallOpcode) (method : MethodRef) : Option RuntimeModel := do
  let entry ← table.entry? opcode method
  entry.resolve environment.callLayouts method

/-- A family claims its name before overload resolution. Other entries share overlapping names
    with lowerings and claim the closed overloads they resolve. -/
def ModelTable.claims (table : ModelTable) (environment : LayoutEnvironment)
    (opcode : CallOpcode) (method : MethodRef) : Bool :=
  (table.entry? opcode method).any fun entry =>
    entry.ownsName || (entry.resolve environment.callLayouts method).isSome

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
  let cells ← literalCells list
  let mut keys : Array Nat := #[]
  for cell in cells do
    let key := mkApp (mkConst ``ModelEntry.key) cell
    keys := keys.push (← unsafe evalExpr Nat (mkConst ``Nat) key)
  SearchTree.groupedLiteral (mkConst ``ModelEntry) cells keys

/-- Every model `entry` resolves has `property`. -/
def ModelEntry.Yields (entry : ModelEntry) (property : RuntimeModel → Prop) : Prop :=
  ∀ environment method model, entry.resolve environment method = some model → property model

/-- An exact entry resolves only its own model. -/
@[simp] theorem ModelEntry.exact_yields {opcode : CallOpcode} {method : MethodRef}
    {declared : OpenSignature} {model : RuntimeModel} {property : RuntimeModel → Prop} :
    (ModelEntry.exact opcode method declared model).Yields property ↔ property model := by
  constructor
  · intro yields
    exact yields (LayoutEnvironment.callLayouts {}) method model (by simp [ModelEntry.exact])
  · intro holds environment reference resolved found
    change (if reference = method then some model else none) = some resolved at found
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
    (List.mem_of_find?_eq_some member) environment.callLayouts method model resolved

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
