import CIL.RuntimeModel
import CIL.Extraction.Generics
import CIL.Extraction.Lockstep
import CIL.Extraction.MetadataBytes

/-!
# Runtime model resolution

`runtimeModel` gives the runtime model a `call` or `newobj` of a typed `MethodRef` stands for,
from a table of model entries searched by the method's name code and compared in full at the leaf.
`model_table%` writes the table as a literal balanced tree, so a lookup costs the depth of the
tree and the comparison of one reference, never the size of the table. `RuntimeModelsAgree`
requires that each live call site emits the model the table gives it, part of
`MethodEvidenceValid`. A runtime method enters the table together with the emissions its model
stands for, in `modelEntries` and `runtimeCatalog`.
-/

namespace CIL.Extraction

/-- The type constructor of `type` with its type arguments removed, so every instance of a
    generic owner such as `Span<T>` has one head. -/
def TypeExpr.genericHead : TypeExpr → TypeExpr
  | .apply head _ => head.genericHead
  | type => type

/-- The runtime methods of one opcode, owner head and name: `resolve` gives the model of a call to
    a method reference of that owner instance and signature, or `none` when none is modelled. -/
structure ModelEntry where
  opcode : CallOpcode
  owner : TypeExpr
  name : MetadataName
  resolve : LayoutEnvironment → MethodRef → Option RuntimeModel

/-- The entry whose model `model` stands for exactly the reference `method` under `opcode`. -/
def ModelEntry.exact (opcode : CallOpcode) (method : MethodRef) (model : RuntimeModel) :
    ModelEntry :=
  { opcode, owner := method.owner.genericHead, name := method.name,
    resolve := fun _ reference => if reference = method then some model else none }

/-- The search key of an entry: the code of its method name. -/
def ModelEntry.key (entry : ModelEntry) : Nat := entry.name.code

/-- Whether two entries claim the same opcode, owner head and name, so one would hide the other. -/
def ModelEntry.sameSlot (left right : ModelEntry) : Bool :=
  left.key == right.key && left.opcode == right.opcode && left.owner == right.owner

/-- Model entries by name code; the entries under one code are tried in order. -/
abbrev ModelTable := SearchTree (List ModelEntry)

/-- The model of a call under `opcode` to `method`: the entry of its name, opcode and owner
    head resolves the whole reference. -/
def ModelTable.find (table : ModelTable) (environment : LayoutEnvironment)
    (opcode : CallOpcode) (method : MethodRef) : Option RuntimeModel := do
  let entries ← table.find? method.name.code
  let entry ← entries.find? fun entry =>
    entry.opcode == opcode && entry.owner == method.owner.genericHead
  entry.resolve environment method

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
/-- The entries of a list term, unfolded until its cells are literal. -/
private partial def listCells (list : Expr) : MetaM (Array Expr) := do
  let list ← whnf list
  match_expr list with
  | List.cons _ head tail => return #[head] ++ (← listCells tail)
  | List.nil _ => return #[]
  | _ => throwError "model table: the entries do not unfold to a list: {list}"

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
  for cell in ← listCells list do
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

/-- The runtime methods with a model. -/
def modelEntries : List ModelEntry := []

/-- The table of `modelEntries`. -/
def runtimeModels : ModelTable := model_table% modelEntries

/-- The literal table is the balanced table of the entries. -/
theorem runtimeModels_eq : runtimeModels = ModelTable.ofEntries modelEntries := rfl

#print axioms runtimeModels_eq

/-- The runtime model a call under `opcode` to `method` stands for, if any. -/
def runtimeModel (environment : LayoutEnvironment) (opcode : CallOpcode) (method : MethodRef) :
    Option RuntimeModel :=
  runtimeModels.find environment opcode method

/-- A table with the emissions it accounts for: `lowered` gives the model an instruction emitted
    at a call stands for, for every model the table can give, and `none` for other emissions. -/
structure ModelCatalog where
  table : ModelTable
  lowered : Instruction → Option RuntimeModel

/-- The call opcodes a model can stand for, by raw opcode. -/
def callOpcode? : Nat → Option CallOpcode
  | 40 => some .call
  | 115 => some .newobj
  | _ => none

/-- A raw instruction and its emission agree with `catalog`: at a `call` or `newobj` the
    emission stands for exactly the model the table gives the site's method. -/
def ModelCatalog.siteAgrees (catalog : ModelCatalog) (environment : LayoutEnvironment)
    (raw : RawInstruction) (emitted : Instruction) : Bool :=
  match callOpcode? raw.opcode, raw.operand with
  | some opcode, .call site =>
    catalog.table.find environment opcode site.method == catalog.lowered emitted
  | _, _ => true

/-- Every live call site of `closed` emits in `code` the model `catalog` gives it, so a model
    emission is tied to the method it stands for and not only to its stack effect. -/
def ModelsAgree (catalog : ModelCatalog) (environment : LayoutEnvironment) (closed : RawMethod)
    (reachable : List Bool) (code : List Instruction) : Prop :=
  closed.code.length = reachable.length ∧ closed.code.length = code.length ∧
  all3 (fun raw live emitted => !live || catalog.siteAgrees environment raw emitted)
    closed.code reachable code = true

instance (catalog : ModelCatalog) (environment : LayoutEnvironment) (closed : RawMethod)
    (reachable : List Bool) (code : List Instruction) :
    Decidable (ModelsAgree catalog environment closed reachable code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The runtime models with the emissions they account for. -/
def runtimeCatalog : ModelCatalog where
  table := runtimeModels
  lowered _ := none

/-- Each live call site of a method emits the runtime model its method reference stands for. -/
def RuntimeModelsAgree (closed : RawMethod) (reachable : List Bool) (method : Method) : Prop :=
  ModelsAgree runtimeCatalog method.environment closed reachable method.code

instance (closed : RawMethod) (reachable : List Bool) (method : Method) :
    Decidable (RuntimeModelsAgree closed reachable method) :=
  inferInstanceAs (Decidable (ModelsAgree _ _ _ _ _))

end CIL.Extraction
