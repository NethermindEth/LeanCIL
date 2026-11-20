import StrictBinding.Sorted

/-!
# Type definitions at stated rows

A claim names a TypeDef row of a pinned image and states what that row defines: its namespace
and name, the type that encloses it, its kind, the Field rows it owns and the type it extends.
The claim also states the NestedClass rows that place the type and the row its base type is,
so `typeDefBound` reads a fixed number of cells and `#Strings` entries for each claim, whatever
the size of the tables. `TypeDefAt` states the same parts as reads of the image, and
`typeDefAt_of_typeDefBound` proves that a successful check means them; `TypeDefsBound` checks a
list of claims against one preparation of the pinned images. That a top-level type has no
NestedClass row, and a nested type exactly one, follows from the stated rows together with
`KeysSorted` for the NestedClass table, a separate fact over the whole table
(`not_nested_of_topLevel`, `only_row_of_nested`).
-/

namespace StrictBinding

open CIL.Safety (except_bind_ok)

/-! ## Claims -/

/-- Where a claim places a type in the NestedClass table, with the rows that show it. -/
inductive Nesting where
  /-- At the top level: NestedClass rows before `next` name lower TypeDef rows and rows from
      `next` on name higher ones, so with the table sorted no row names the type. `next` is one
      past the table when every row names a lower TypeDef row. -/
  | topLevel (next : Nat)
  /-- Nested in TypeDef row `enclosing`, as NestedClass row `nestedRow` states; the rows beside
      it name lower and higher TypeDef rows, so with the table sorted it is the type's only row. -/
  | nested (nestedRow enclosing : Nat)
  deriving DecidableEq, Repr

/-- What a type definition is, as the flags and base type of its row decide (II.23.1.15). -/
inductive TypeKind where
  /-- The row's flags set the interface semantics bit. -/
  | interface
  /-- The row extends `System.Enum`. -/
  | enum
  /-- The row extends `System.ValueType` and is not `System.Enum` itself. -/
  | valueType
  /-- Any other row: a class, as `System.Object` and `System.Enum` are. -/
  | classType
  deriving DecidableEq, Repr

/-- The type a TypeDef row's `Extends` column names. -/
inductive BaseType where
  /-- No type: the column's row part is zero, as for an interface or `System.Object`. -/
  | none
  /-- The TypeDef or TypeRef row of `token`, which has this namespace and name. -/
  | named (token : Nat) (typeNamespace typeName : List Nat)
  /-- The TypeSpec row of `token`: an instantiated generic type. -/
  | spec (token : Nat)
  deriving DecidableEq, Repr

/-- A claim that TypeDef row `row` of the image pinned under `identity` defines a type with
    these parts. A name is the bytes of its `#Strings` entry without the terminator. -/
structure TypeDefClaim where
  identity : String
  row : Nat
  typeNamespace : List Nat
  typeName : List Nat
  nesting : Nesting
  kind : TypeKind
  /-- The first Field row the type owns and how many rows it owns. -/
  fields : Nat × Nat
  base : BaseType
  deriving DecidableEq, Repr

/-- The table a token names a row of: its top byte. -/
def tableOf (token : Nat) : Nat := token / 2 ^ 24

/-- The token of the claimed TypeDef row, when its row number fits in 24 bits. -/
def TypeDefClaim.token (claim : TypeDefClaim) : Except AuditError Nat :=
  CIL.Extraction.checkedTokenOf CIL.Extraction.Table.typeDef claim.row .rowOverflow

/-! ## Columns and flags -/

/-- The flags column of a TypeDef row (II.22.37). -/
def typeDefFlagsColumn : Nat := 0

/-- The name column of a TypeDef or TypeRef row (II.22.37, II.22.38). -/
def typeNameColumn : Nat := 1

/-- The namespace column of a TypeDef or TypeRef row. -/
def typeNamespaceColumn : Nat := 2

/-- The `Extends` column of a TypeDef row. -/
def typeDefExtendsColumn : Nat := 3

/-- The field list column of a TypeDef row: the first Field row the type owns. -/
def typeDefFieldListColumn : Nat := 4

/-- The nested type column of a NestedClass row (II.22.32). -/
def nestedTypeColumn : Nat := 0

/-- The enclosing type column of a NestedClass row. -/
def enclosingTypeColumn : Nat := 1

/-- The visibility of TypeDef flags: the three bits of `VisibilityMask` (II.23.1.15). -/
def visibilityOf (flags : Nat) : Nat := flags % 8

/-- The lowest visibility of a nested type. `NotPublic` (0) and `Public` (1) are the
    visibilities of a type at the top level, and II.22.37 says the visibility decides whether a
    type is nested; the NestedClass rows a claim states show that the table agrees. -/
def nestedVisibility : Nat := 2

/-- The interface semantics bit of TypeDef flags. -/
def interfaceFlag : Nat := 0x20

/-- The value a cell of this coded index column holds to name the row of `token`: the row above
    the tag of the token's table (II.24.2.6). None when the column cannot name that table or is
    not a coded index. -/
def Column.valueOf (column : Column) (token : Nat) : Option Nat :=
  match column with
  | .coded bits tables =>
    (tables.findIdx? (· == tableOf token)).map fun tag => token % 2 ^ 24 * 2 ^ bits + tag
  | _ => Option.none

/-- The namespace `System`. -/
def systemNamespace : List Nat := asciiOf "System"

/-- The name `Enum`. -/
def enumName : List Nat := asciiOf "Enum"

/-- The name `ValueType`. -/
def valueTypeName : List Nat := asciiOf "ValueType"

/-- Whether the Assembly or AssemblyRef row names a neutral core library with its publisher's
    token. Both tables have the same identity columns after the Assembly's hash-algorithm column. -/
def coreAssemblyAt (image : PreparedImage) (row first : Nat) : Except AuditError Bool := do
  let cell := image.layout.cell image.view row
  let name ← image.layout.stringAt image.view (← cell (first + 6))
  let some name := CIL.MetadataName.ofBytes? name | return false
  let some publisher := CIL.Extraction.coreLibraryKey? name | return false
  if !(← image.layout.stringAt image.view (← cell (first + 7))).isEmpty then return false
  let flags ← cell (first + 4)
  let key ← image.layout.blobAt image.view (← cell (first + 5))
  return (← assemblyKeyToken flags key) == some publisher

/-- A local base uses the defining image's Assembly row. A referenced base must point directly
    to an AssemblyRef through its ResolutionScope column (II.24.2.6). -/
private def coreBaseScope (image : PreparedImage) (token : Nat) : Except AuditError Bool := do
  if tableOf token == CIL.Extraction.Table.typeDef then
    return ← coreAssemblyAt image (tokenOf 0x20 1) 1
  let scope ← image.layout.cell image.view token 0
  if scope % 4 != 2 then return false
  let row ← CIL.Extraction.checkedTokenOf CIL.Extraction.Table.assemblyRef (scope / 4) .rowOverflow
  coreAssemblyAt image row 0

/-- The kind determined by the flags and the qualified base type, including its assembly. -/
def kindOf (image : PreparedImage) (flags : Nat) (typeNamespace typeName : List Nat)
    (base : BaseType) : Except AuditError TypeKind := do
  if flags / interfaceFlag % 2 == 1 then return .interface
  let .named token baseNamespace baseName := base | return .classType
  if baseNamespace != systemNamespace || (baseName != enumName && baseName != valueTypeName) then
    return .classType
  if !(← coreBaseScope image token) then return .classType
  if baseName == enumName then return .enum
  if typeNamespace == systemNamespace && typeName == enumName then
    if ← coreAssemblyAt image (tokenOf 0x20 1) 1 then return .classType
  return .valueType

/-! ## Propositions -/

/-- The number of NestedClass rows of the image. -/
def nestedCount (image : PreparedImage) : Nat :=
  image.layout.rowCount CIL.Extraction.Table.nestedClass

/-- The TypeDef row that NestedClass row `nestedRow` names as nested. -/
def nestedTypeOf (image : PreparedImage) (nestedRow : Nat) : Except AuditError Nat :=
  image.layout.cellOfRow image.view CIL.Extraction.Table.nestedClass nestedRow nestedTypeColumn

/-- The TypeDef row that NestedClass row `nestedRow` names as enclosing. -/
def enclosingOf (image : PreparedImage) (nestedRow : Nat) : Except AuditError Nat :=
  image.layout.cellOfRow image.view CIL.Extraction.Table.nestedClass nestedRow enclosingTypeColumn

/-- NestedClass row `nestedRow` names a TypeDef row below `row`, or is row zero, before the
    table. -/
def NamesBelow (image : PreparedImage) (nestedRow row : Nat) : Prop :=
  nestedRow = 0 ∨ ∃ value, nestedTypeOf image nestedRow = .ok value ∧ value < row

/-- NestedClass row `nestedRow` names a TypeDef row above `row`, or is past the table. -/
def NamesAbove (image : PreparedImage) (nestedRow row : Nat) : Prop :=
  nestedCount image < nestedRow ∨ ∃ value, nestedTypeOf image nestedRow = .ok value ∧ row < value

/-- Column `column` of the row of `token` names the terminated `#Strings` entry `bytes`. -/
def NameAt (image : PreparedImage) (token column : Nat) (bytes : List Nat) : Prop :=
  ∃ key, image.layout.cell image.view token column = .ok key ∧ StringAt image key (bytes ++ [0])

/-- One past the last Field row TypeDef row `row` owns: the next row's field list, or one past
    the Field table for the last row (II.22.37). -/
def fieldsEnd (image : PreparedImage) (row : Nat) : Except AuditError Nat :=
  if row < image.layout.rowCount CIL.Extraction.Table.typeDef then
    image.layout.cellOfRow image.view CIL.Extraction.Table.typeDef (row + 1) typeDefFieldListColumn
  else pure (image.layout.rowCount CIL.Extraction.Table.field + 1)

/-- A row at the top level has a top-level visibility and the stated NestedClass rows bracket it;
    a nested row has a nested visibility, the stated NestedClass row pairs it with the stated
    enclosing row, and the rows beside that row name other types. The enclosing TypeDef is a
    nonzero row strictly before the nested type (II.22). -/
def NestingAt (image : PreparedImage) (row flags : Nat) : Nesting → Prop
  | .topLevel next =>
    visibilityOf flags < nestedVisibility ∧ 1 ≤ next ∧ next ≤ nestedCount image + 1 ∧
      NamesBelow image (next - 1) row ∧ NamesAbove image next row
  | .nested nestedRow enclosing =>
    nestedVisibility ≤ visibilityOf flags ∧ 1 ≤ nestedRow ∧ nestedRow ≤ nestedCount image ∧
      nestedTypeOf image nestedRow = .ok row ∧ enclosingOf image nestedRow = .ok enclosing ∧
      (1 ≤ enclosing ∧ enclosing < row) ∧
      NamesBelow image (nestedRow - 1) row ∧ NamesAbove image (nestedRow + 1) row

/-- The `Extends` value `baseValue` names the stated base type, with its namespace and name. -/
def BaseAt (image : PreparedImage) (baseValue : Nat) : BaseType → Prop
  | .none => baseValue / 2 ^ 2 = 0
  | .named token baseNamespace baseName =>
    (tableOf token = CIL.Extraction.Table.typeDef ∨
        tableOf token = CIL.Extraction.Table.typeRef) ∧
      Column.typeDefOrRef.valueOf token = some baseValue ∧
      NameAt image token typeNameColumn baseName ∧
      NameAt image token typeNamespaceColumn baseNamespace
  | .spec token =>
    tableOf token = CIL.Extraction.Table.typeSpec ∧
      Column.typeDefOrRef.valueOf token = some baseValue ∧
      ∃ position, image.layout.rowAt token = .ok position

/-- The claimed TypeDef row of the image defines the claimed type: its names, nesting, Field
    rows and base type are the row's, and its kind is the one the row's flags and base type
    give. -/
def TypeDefAt (image : PreparedImage) (claim : TypeDefClaim) : Prop :=
  ∃ token flags baseValue, claim.token = .ok token ∧
    image.layout.cell image.view token typeDefFlagsColumn = .ok flags ∧
    NameAt image token typeNameColumn claim.typeName ∧
    NameAt image token typeNamespaceColumn claim.typeNamespace ∧
    NestingAt image claim.row flags claim.nesting ∧
    image.layout.cell image.view token typeDefFieldListColumn = .ok claim.fields.1 ∧
    fieldsEnd image claim.row = .ok (claim.fields.1 + claim.fields.2) ∧
    1 ≤ claim.fields.1 ∧ claim.fields.1 + claim.fields.2 ≤
      image.layout.rowCount CIL.Extraction.Table.field + 1 ∧
    image.layout.cell image.view token typeDefExtendsColumn = .ok baseValue ∧
    BaseAt image baseValue claim.base ∧
    kindOf image flags claim.typeNamespace claim.typeName claim.base = .ok claim.kind

/-! ## Checks -/

/-- Succeeds when `holds`, and otherwise fails naming the row and the part that differs. -/
def requirePart (row : Nat) (part : TypeDefPart) (holds : Bool) : Except AuditError Unit :=
  if holds then pure () else throw (.typeDefMismatch row part)

/-- Column `column` of the row of `token` names the terminated entry `bytes`; a difference
    fails as `part` of claimed row `row`. -/
def nameBound (image : PreparedImage) (token column : Nat) (bytes : List Nat) (row : Nat)
    (part : TypeDefPart) : Except AuditError Unit := do
  let key ← image.layout.cell image.view token column
  requirePart row part (← stringFound image key (bytes ++ [0]))

/-- Whether NestedClass row `nestedRow` names a TypeDef row below `row` or is row zero. -/
def namesBelow (image : PreparedImage) (nestedRow row : Nat) : Except AuditError Bool :=
  if nestedRow = 0 then pure true else do return decide ((← nestedTypeOf image nestedRow) < row)

/-- Whether NestedClass row `nestedRow` names a TypeDef row above `row` or is past the table. -/
def namesAbove (image : PreparedImage) (nestedRow row : Nat) : Except AuditError Bool :=
  if nestedCount image < nestedRow then pure true
  else do return decide (row < (← nestedTypeOf image nestedRow))

/-- The row's visibility and the stated NestedClass rows agree with the claimed nesting. The
    check reads at most three NestedClass rows. -/
def nestingBound (image : PreparedImage) (row flags : Nat) : Nesting → Except AuditError Unit
  | .topLevel next => do
    requirePart row .nesting (decide (visibilityOf flags < nestedVisibility ∧ 1 ≤ next ∧
      next ≤ nestedCount image + 1))
    requirePart row .nesting (← namesBelow image (next - 1) row)
    requirePart row .nesting (← namesAbove image next row)
  | .nested nestedRow enclosing => do
    requirePart row .nesting (decide (nestedVisibility ≤ visibilityOf flags ∧ 1 ≤ nestedRow ∧
      nestedRow ≤ nestedCount image))
    let nested ← nestedTypeOf image nestedRow
    let outer ← enclosingOf image nestedRow
    requirePart row .nesting
      (nested == row && outer == enclosing && decide (1 ≤ enclosing ∧ enclosing < row))
    requirePart row .nesting (← namesBelow image (nestedRow - 1) row)
    requirePart row .nesting (← namesAbove image (nestedRow + 1) row)

/-- The `Extends` value names the claimed base type and that row has the claimed names. -/
def baseBound (image : PreparedImage) (row baseValue : Nat) :
    BaseType → Except AuditError Unit
  | .none => requirePart row .base (baseValue / 2 ^ 2 == 0)
  | .named token baseNamespace baseName => do
    requirePart row .base
      ((tableOf token == CIL.Extraction.Table.typeDef ||
          tableOf token == CIL.Extraction.Table.typeRef) &&
        Column.typeDefOrRef.valueOf token == some baseValue)
    nameBound image token typeNameColumn baseName row .base
    nameBound image token typeNamespaceColumn baseNamespace row .base
  | .spec token => do
    requirePart row .base
      (tableOf token == CIL.Extraction.Table.typeSpec &&
        Column.typeDefOrRef.valueOf token == some baseValue)
    let _ ← image.layout.rowAt token
    pure ()

/-- The claimed TypeDef row defines the claimed type. The check reads the row's five columns,
    one NestedClass row, the next TypeDef row's field list, the base row's two names and the
    four entries the names select, so its cost does not grow with the tables. -/
def typeDefBound (image : PreparedImage) (claim : TypeDefClaim) : Except AuditError Unit := do
  let token ← claim.token
  let flags ← image.layout.cell image.view token typeDefFlagsColumn
  nameBound image token typeNameColumn claim.typeName claim.row .typeName
  nameBound image token typeNamespaceColumn claim.typeNamespace claim.row .typeNamespace
  nestingBound image claim.row flags claim.nesting
  let first ← image.layout.cell image.view token typeDefFieldListColumn
  let next ← fieldsEnd image claim.row
  requirePart claim.row .fields
    (first == claim.fields.1 && next == claim.fields.1 + claim.fields.2 &&
      decide (1 ≤ first ∧ next ≤ image.layout.rowCount CIL.Extraction.Table.field + 1))
  let baseValue ← image.layout.cell image.view token typeDefExtendsColumn
  baseBound image claim.row baseValue claim.base
  requirePart claim.row .kind
    ((← kindOf image flags claim.typeNamespace claim.typeName claim.base) == claim.kind)

/-- The claim holds in the image pinned under the claim's identity. -/
def typeDefClaimBound (prepared : List PreparedImage) (claim : TypeDefClaim) :
    Except AuditError Unit := do
  typeDefBound (← located prepared claim.identity) claim

/-- Every claim holds in the image its identity names, against one preparation of the images. -/
def TypeDefsBound (images : List PinnedImage) (claims : List TypeDefClaim) : Prop :=
  ClaimsHold typeDefClaimBound images claims

instance (images : List PinnedImage) (claims : List TypeDefClaim) :
    Decidable (TypeDefsBound images claims) :=
  inferInstanceAs (Decidable (ClaimsHold _ _ _))

/-! ## Soundness -/

/-- A part check that succeeds held. -/
theorem requirePart_ok {row : Nat} {part : TypeDefPart} {holds : Bool}
    (checked : requirePart row part holds = .ok ()) : holds = true := by
  unfold requirePart at checked
  split at checked
  · assumption
  · exact absurd checked throw_ne_ok

#print axioms requirePart_ok

/-- A name check that succeeds found the entry the column names. -/
theorem nameAt_of_nameBound {image : PreparedImage} (bounded : image.view.Bounded)
    {token column row : Nat} {bytes : List Nat} {part : TypeDefPart}
    (checked : nameBound image token column bytes row part = .ok ()) :
    NameAt image token column bytes := by
  unfold nameBound at checked
  obtain ⟨key, readKey, checked⟩ := except_bind_ok checked
  obtain ⟨found, readFound, checked⟩ := except_bind_ok checked
  have holds := requirePart_ok checked
  subst holds
  exact ⟨key, readKey, stringAt_of_stringFound bounded readFound⟩

#print axioms nameAt_of_nameBound

/-- A lower-row check that succeeds means the row names a lower TypeDef row or is row zero. -/
theorem namesBelow_ok {image : PreparedImage} {nestedRow row : Nat}
    (checked : namesBelow image nestedRow row = .ok true) : NamesBelow image nestedRow row := by
  unfold namesBelow at checked
  split at checked
  · exact Or.inl (by assumption)
  · obtain ⟨value, readValue, checked⟩ := except_bind_ok checked
    simp only [pure, Except.pure, Except.ok.injEq, decide_eq_true_eq] at checked
    exact Or.inr ⟨value, readValue, checked⟩

#print axioms namesBelow_ok

/-- A higher-row check that succeeds means the row names a higher TypeDef row or is past the
    table. -/
theorem namesAbove_ok {image : PreparedImage} {nestedRow row : Nat}
    (checked : namesAbove image nestedRow row = .ok true) : NamesAbove image nestedRow row := by
  unfold namesAbove at checked
  split at checked
  · exact Or.inl (by assumption)
  · obtain ⟨value, readValue, checked⟩ := except_bind_ok checked
    simp only [pure, Except.pure, Except.ok.injEq, decide_eq_true_eq] at checked
    exact Or.inr ⟨value, readValue, checked⟩

#print axioms namesAbove_ok

/-- A nesting check that succeeds means the claimed nesting. -/
theorem nestingAt_of_nestingBound {image : PreparedImage} {row flags : Nat} {nesting : Nesting}
    (checked : nestingBound image row flags nesting = .ok ()) :
    NestingAt image row flags nesting := by
  cases nesting with
  | topLevel next =>
    unfold nestingBound at checked
    obtain ⟨visible, visibleOk, checked⟩ := except_bind_ok checked
    cases visible
    obtain ⟨below, belowOk, checked⟩ := except_bind_ok checked
    obtain ⟨placed, placedOk, checked⟩ := except_bind_ok checked
    cases placed
    obtain ⟨above, aboveOk, aboveHolds⟩ := except_bind_ok checked
    have bounds := of_decide_eq_true (requirePart_ok visibleOk)
    have belowTrue := requirePart_ok placedOk
    have aboveTrue := requirePart_ok aboveHolds
    subst belowTrue
    subst aboveTrue
    exact ⟨bounds.1, bounds.2.1, bounds.2.2, namesBelow_ok belowOk, namesAbove_ok aboveOk⟩
  | nested nestedRow enclosing =>
    unfold nestingBound at checked
    obtain ⟨visible, visibleOk, checked⟩ := except_bind_ok checked
    cases visible
    obtain ⟨nested, readNested, checked⟩ := except_bind_ok checked
    obtain ⟨outer, readOuter, checked⟩ := except_bind_ok checked
    obtain ⟨paired, pairedOk, checked⟩ := except_bind_ok checked
    cases paired
    obtain ⟨below, belowOk, checked⟩ := except_bind_ok checked
    obtain ⟨placed, placedOk, checked⟩ := except_bind_ok checked
    cases placed
    obtain ⟨above, aboveOk, aboveHolds⟩ := except_bind_ok checked
    have bounds := of_decide_eq_true (requirePart_ok visibleOk)
    have same := requirePart_ok pairedOk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at same
    obtain ⟨⟨rfl, rfl⟩, precedes⟩ := same
    have belowTrue := requirePart_ok placedOk
    have aboveTrue := requirePart_ok aboveHolds
    subst belowTrue
    subst aboveTrue
    exact ⟨bounds.1, bounds.2.1, bounds.2.2, readNested, readOuter, precedes,
      namesBelow_ok belowOk, namesAbove_ok aboveOk⟩

#print axioms nestingAt_of_nestingBound

/-- The key II.22 requires the NestedClass table sorted by: its nested type column. -/
def nestedClassKey : List Nat := [nestedTypeColumn]

/-- In a sorted NestedClass table, a row names a TypeDef row at most the one a later row names. -/
theorem nestedType_le {image : PreparedImage}
    (sorted : KeysSorted image CIL.Extraction.Table.nestedClass nestedClassKey)
    {lower upper first last : Nat} (low : 1 ≤ lower) (ordered : lower ≤ upper)
    (inside : upper ≤ nestedCount image) (readFirst : nestedTypeOf image lower = .ok first)
    (readLast : nestedTypeOf image upper = .ok last) : first ≤ last :=
  value_le_of_keysSorted sorted low ordered inside readFirst readLast

#print axioms nestedType_le

/-- With the NestedClass table sorted, no NestedClass row names a type claimed at the top level. -/
theorem not_nested_of_topLevel {image : PreparedImage} {row flags next : Nat}
    (sorted : KeysSorted image CIL.Extraction.Table.nestedClass nestedClassKey)
    (placed : NestingAt image row flags (.topLevel next)) :
    ∀ nestedRow, 1 ≤ nestedRow → nestedRow ≤ nestedCount image →
      nestedTypeOf image nestedRow ≠ .ok row := by
  intro nestedRow low high read
  obtain ⟨_, first, last, below, above⟩ := placed
  by_cases before : nestedRow < next
  · rcases below with zero | ⟨bound, readBound, less⟩
    · omega
    · have := nestedType_le sorted low (show nestedRow ≤ next - 1 by omega) (by omega) read
        readBound
      omega
  · rcases above with past | ⟨bound, readBound, greater⟩
    · omega
    · have := nestedType_le sorted first (show next ≤ nestedRow by omega) high readBound read
      omega

#print axioms not_nested_of_topLevel

/-- With the NestedClass table sorted, the row a nested claim states is the only NestedClass row
    that names the type. -/
theorem only_row_of_nested {image : PreparedImage} {row flags nestedRow enclosing : Nat}
    (sorted : KeysSorted image CIL.Extraction.Table.nestedClass nestedClassKey)
    (placed : NestingAt image row flags (.nested nestedRow enclosing)) :
    ∀ other, 1 ≤ other → other ≤ nestedCount image → nestedTypeOf image other = .ok row →
      other = nestedRow := by
  intro other low high read
  obtain ⟨_, first, last, _, _, _, below, above⟩ := placed
  by_cases before : other < nestedRow
  · rcases below with zero | ⟨bound, readBound, less⟩
    · omega
    · have := nestedType_le sorted low (show other ≤ nestedRow - 1 by omega) (by omega) read
        readBound
      omega
  · by_cases after : nestedRow < other
    · rcases above with past | ⟨bound, readBound, greater⟩
      · omega
      · have := nestedType_le sorted (show 1 ≤ nestedRow + 1 by omega)
          (show nestedRow + 1 ≤ other by omega) high readBound read
        omega
    · omega

#print axioms only_row_of_nested

/-- A base check that succeeds means the claimed base type and its names. -/
theorem baseAt_of_baseBound {image : PreparedImage} (bounded : image.view.Bounded)
    {row baseValue : Nat} {base : BaseType}
    (checked : baseBound image row baseValue base = .ok ()) : BaseAt image baseValue base := by
  cases base with
  | none =>
    have holds := requirePart_ok checked
    show baseValue / 2 ^ 2 = 0
    simpa only [beq_iff_eq] using holds
  | named token baseNamespace baseName =>
    unfold baseBound at checked
    obtain ⟨named, namedOk, checked⟩ := except_bind_ok checked
    cases named
    obtain ⟨named, nameOk, namespaceOk⟩ := except_bind_ok checked
    cases named
    have holds := requirePart_ok namedOk
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at holds
    exact ⟨holds.1, holds.2, nameAt_of_nameBound bounded nameOk,
      nameAt_of_nameBound bounded namespaceOk⟩
  | spec token =>
    unfold baseBound at checked
    obtain ⟨checkedBase, matched, checked⟩ := except_bind_ok checked
    cases checkedBase
    obtain ⟨position, found, _⟩ := except_bind_ok checked
    have holds := requirePart_ok matched
    simp only [Bool.and_eq_true, beq_iff_eq] at holds
    exact ⟨holds.1, holds.2, position, found⟩

#print axioms baseAt_of_baseBound

/-- A type definition check that succeeds means the claimed row defines the claimed type. -/
theorem typeDefAt_of_typeDefBound {image : PreparedImage} (bounded : image.view.Bounded)
    {claim : TypeDefClaim} (checked : typeDefBound image claim = .ok ()) :
    TypeDefAt image claim := by
  unfold typeDefBound at checked
  obtain ⟨token, readToken, checked⟩ := except_bind_ok checked
  obtain ⟨flags, readFlags, checked⟩ := except_bind_ok checked
  obtain ⟨named, nameOk, checked⟩ := except_bind_ok checked
  cases named
  obtain ⟨named, namespaceOk, checked⟩ := except_bind_ok checked
  cases named
  obtain ⟨nested, nestingOk, checked⟩ := except_bind_ok checked
  cases nested
  obtain ⟨first, readFirst, checked⟩ := except_bind_ok checked
  obtain ⟨next, readNext, checked⟩ := except_bind_ok checked
  obtain ⟨owned, fieldsOk, checked⟩ := except_bind_ok checked
  cases owned
  obtain ⟨baseValue, readBase, checked⟩ := except_bind_ok checked
  obtain ⟨based, baseOk, checked⟩ := except_bind_ok checked
  cases based
  obtain ⟨kind, readKind, kindOk⟩ := except_bind_ok checked
  have fields := requirePart_ok fieldsOk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at fields
  obtain ⟨⟨rfl, rfl⟩, lower, upper⟩ := fields
  have sameKind := requirePart_ok kindOk
  simp only [beq_iff_eq] at sameKind
  exact ⟨token, flags, baseValue, readToken, readFlags, nameAt_of_nameBound bounded nameOk,
    nameAt_of_nameBound bounded namespaceOk, nestingAt_of_nestingBound nestingOk,
    readFirst, readNext, lower, upper, readBase, baseAt_of_baseBound bounded baseOk,
    sameKind ▸ readKind⟩

#print axioms typeDefAt_of_typeDefBound

/-- Every claim of a successful check holds in the image its identity selects, from one
    preparation of the pinned images. -/
theorem typeDefAt_of_typeDefsBound {images : List PinnedImage} {claims : List TypeDefClaim}
    (bound : TypeDefsBound images claims) :
    ∃ prepared, prepare images = .ok prepared ∧
      ∀ claim ∈ claims, ∃ image, located prepared claim.identity = .ok image ∧
        TypeDefAt image claim := by
  obtain ⟨prepared, decoded, checks⟩ := check_of_claimsHold bound
  refine ⟨prepared, decoded, fun claim member => ?_⟩
  have one := checks claim member
  unfold typeDefClaimBound at one
  cases found : located prepared claim.identity with
  | error error => simp [found, bind, Except.bind, ok] at one
  | ok image =>
    refine ⟨image, rfl, ?_⟩
    have checked : typeDefBound image claim = .ok () := by
      cases result : typeDefBound image claim with
      | error error => simp [found, result, bind, Except.bind, ok] at one
      | ok value => cases value; rfl
    exact typeDefAt_of_typeDefBound (prepare_bounded decoded image (mem_of_located found))
      checked

#print axioms typeDefAt_of_typeDefsBound

end StrictBinding
