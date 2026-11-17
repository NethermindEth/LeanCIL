import StrictBinding.Evidence

/-!
# Type definitions at stated rows

A claim names a TypeDef row of a pinned image and states what that row defines: its namespace
and name, the type that encloses it, its kind, the Field rows it owns and the type it extends.
The claim also states the NestedClass row of a nested type and the row its base type is, so
`typeDefBound` reads a fixed number of cells and `#Strings` entries for each claim, whatever the
size of the tables. `TypeDefAt` states the same parts as reads of the image, and
`typeDefAt_of_typeDefBound` proves that a successful check means them; `TypeDefsBound` checks a
list of claims against one preparation of the pinned images.
-/

namespace StrictBinding

open CIL.Safety (except_bind_ok)

/-! ## Claims -/

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
  /-- The NestedClass row that pairs this row with the TypeDef row enclosing it, and that row;
      none for a type at the top level. -/
  nesting : Option (Nat × Nat)
  kind : TypeKind
  /-- The first Field row the type owns and how many rows it owns. -/
  fields : Nat × Nat
  base : BaseType
  deriving DecidableEq, Repr

/-- The table a token names a row of: its top byte. -/
def tableOf (token : Nat) : Nat := token / 2 ^ 24

/-- The token of TypeDef row `row`. -/
def typeDefToken (row : Nat) : Nat := tokenOf CIL.Extraction.Table.typeDef row

/-- The token of NestedClass row `row`. -/
def nestedClassToken (row : Nat) : Nat := tokenOf CIL.Extraction.Table.nestedClass row

/-- The token of the claimed TypeDef row. -/
def TypeDefClaim.token (claim : TypeDefClaim) : Nat := typeDefToken claim.row

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
    visibilities of a type at the top level, and II.22.37 gives a nested visibility exactly to
    the rows NestedClass lists. -/
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

/-- The kind a row with these flags, names and base type has. -/
def kindOf (flags : Nat) (typeNamespace typeName : List Nat) (base : BaseType) : TypeKind :=
  if flags / interfaceFlag % 2 == 1 then .interface
  else
    match base with
    | .named _ baseNamespace baseName =>
      if baseNamespace == systemNamespace && baseName == enumName then .enum
      else if baseNamespace == systemNamespace && baseName == valueTypeName &&
          !(typeNamespace == systemNamespace && typeName == enumName) then .valueType
      else .classType
    | _ => .classType

/-! ## Propositions -/

/-- Column `column` of the row of `token` names the terminated `#Strings` entry `bytes`. -/
def NameAt (image : PreparedImage) (token column : Nat) (bytes : List Nat) : Prop :=
  ∃ key, image.layout.cell image.view token column = .ok key ∧ StringAt image key (bytes ++ [0])

/-- One past the last Field row TypeDef row `row` owns: the next row's field list, or one past
    the Field table for the last row (II.22.37). -/
def fieldsEnd (image : PreparedImage) (row : Nat) : Except AuditError Nat :=
  if row < image.layout.rowCount CIL.Extraction.Table.typeDef then
    image.layout.cell image.view (typeDefToken (row + 1)) typeDefFieldListColumn
  else pure (image.layout.rowCount CIL.Extraction.Table.field + 1)

/-- A row at the top level has a top-level visibility; a nested row has a nested visibility and
    the stated NestedClass row pairs it with the stated enclosing row. -/
def NestingAt (image : PreparedImage) (row flags : Nat) : Option (Nat × Nat) → Prop
  | Option.none => visibilityOf flags < nestedVisibility
  | some (nestedRow, enclosing) =>
    nestedVisibility ≤ visibilityOf flags ∧
      image.layout.cell image.view (nestedClassToken nestedRow) nestedTypeColumn = .ok row ∧
      image.layout.cell image.view (nestedClassToken nestedRow) enclosingTypeColumn = .ok enclosing

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
      Column.typeDefOrRef.valueOf token = some baseValue

/-- The claimed TypeDef row of the image defines the claimed type: its names, nesting, Field
    rows and base type are the row's, and its kind is the one the row's flags and base type
    give. -/
def TypeDefAt (image : PreparedImage) (claim : TypeDefClaim) : Prop :=
  ∃ flags baseValue,
    image.layout.cell image.view claim.token typeDefFlagsColumn = .ok flags ∧
    NameAt image claim.token typeNameColumn claim.typeName ∧
    NameAt image claim.token typeNamespaceColumn claim.typeNamespace ∧
    NestingAt image claim.row flags claim.nesting ∧
    image.layout.cell image.view claim.token typeDefFieldListColumn = .ok claim.fields.1 ∧
    fieldsEnd image claim.row = .ok (claim.fields.1 + claim.fields.2) ∧
    image.layout.cell image.view claim.token typeDefExtendsColumn = .ok baseValue ∧
    BaseAt image baseValue claim.base ∧
    claim.kind = kindOf flags claim.typeNamespace claim.typeName claim.base

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

/-- The row's visibility and the stated NestedClass row agree with the claimed nesting. -/
def nestingBound (image : PreparedImage) (row flags : Nat) :
    Option (Nat × Nat) → Except AuditError Unit
  | Option.none => requirePart row .nesting (decide (visibilityOf flags < nestedVisibility))
  | some (nestedRow, enclosing) => do
    requirePart row .nesting (decide (nestedVisibility ≤ visibilityOf flags))
    let nested ← image.layout.cell image.view (nestedClassToken nestedRow) nestedTypeColumn
    let outer ← image.layout.cell image.view (nestedClassToken nestedRow) enclosingTypeColumn
    requirePart row .nesting (nested == row && outer == enclosing)

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
  | .spec token =>
    requirePart row .base
      (tableOf token == CIL.Extraction.Table.typeSpec &&
        Column.typeDefOrRef.valueOf token == some baseValue)

/-- The claimed TypeDef row defines the claimed type. The check reads the row's five columns,
    one NestedClass row, the next TypeDef row's field list, the base row's two names and the
    four entries the names select, so its cost does not grow with the tables. -/
def typeDefBound (image : PreparedImage) (claim : TypeDefClaim) : Except AuditError Unit := do
  let flags ← image.layout.cell image.view claim.token typeDefFlagsColumn
  nameBound image claim.token typeNameColumn claim.typeName claim.row .typeName
  nameBound image claim.token typeNamespaceColumn claim.typeNamespace claim.row .typeNamespace
  nestingBound image claim.row flags claim.nesting
  let first ← image.layout.cell image.view claim.token typeDefFieldListColumn
  let next ← fieldsEnd image claim.row
  requirePart claim.row .fields
    (first == claim.fields.1 && next == claim.fields.1 + claim.fields.2)
  let baseValue ← image.layout.cell image.view claim.token typeDefExtendsColumn
  baseBound image claim.row baseValue claim.base
  requirePart claim.row .kind
    (kindOf flags claim.typeNamespace claim.typeName claim.base == claim.kind)

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

/-- A nesting check that succeeds means the claimed nesting. -/
theorem nestingAt_of_nestingBound {image : PreparedImage} {row flags : Nat}
    {nesting : Option (Nat × Nat)} (checked : nestingBound image row flags nesting = .ok ()) :
    NestingAt image row flags nesting := by
  cases nesting with
  | none =>
    unfold nestingBound at checked
    show visibilityOf flags < nestedVisibility
    exact of_decide_eq_true (requirePart_ok checked)
  | some pair =>
    obtain ⟨nestedRow, enclosing⟩ := pair
    unfold nestingBound at checked
    obtain ⟨visible, visibleOk, checked⟩ := except_bind_ok checked
    cases visible
    obtain ⟨nested, readNested, checked⟩ := except_bind_ok checked
    obtain ⟨outer, readOuter, checked⟩ := except_bind_ok checked
    have same := requirePart_ok checked
    simp only [Bool.and_eq_true, beq_iff_eq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨of_decide_eq_true (requirePart_ok visibleOk), readNested, readOuter⟩

#print axioms nestingAt_of_nestingBound

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
    have holds := requirePart_ok checked
    simp only [Bool.and_eq_true, beq_iff_eq] at holds
    exact holds

#print axioms baseAt_of_baseBound

/-- A type definition check that succeeds means the claimed row defines the claimed type. -/
theorem typeDefAt_of_typeDefBound {image : PreparedImage} (bounded : image.view.Bounded)
    {claim : TypeDefClaim} (checked : typeDefBound image claim = .ok ()) :
    TypeDefAt image claim := by
  unfold typeDefBound at checked
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
  obtain ⟨based, baseOk, kindOk⟩ := except_bind_ok checked
  cases based
  have fields := requirePart_ok fieldsOk
  simp only [Bool.and_eq_true, beq_iff_eq] at fields
  have kind := requirePart_ok kindOk
  simp only [beq_iff_eq] at kind
  exact ⟨flags, baseValue, readFlags, nameAt_of_nameBound bounded nameOk,
    nameAt_of_nameBound bounded namespaceOk, nestingAt_of_nestingBound nestingOk,
    fields.1 ▸ readFirst, fields.2 ▸ readNext, readBase, baseAt_of_baseBound bounded baseOk,
    kind.symm⟩

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
