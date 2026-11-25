import StrictBinding.TypeDefs

/-! Resolve public System types and their physical field ranges in pinned platform images. -/

namespace StrictBinding

open CIL.Extraction

/-- The unique public, top-level, non-interface definition with the given System name. -/
private def definitionRow (image : PreparedImage) (name : String) (invalid : AuditError) :
    Except AuditError (Option Nat) := do
  let cell := image.layout.cellOfRow image.view Table.typeDef
  let mut found := none
  for i in [:image.layout.rowCount Table.typeDef] do
    let row := i + 1
    unless ← stringFound image (← cell row typeNameColumn) (asciiOf name ++ [0]) do continue
    unless ← stringFound image (← cell row typeNamespaceColumn) (systemNamespace ++ [0]) do continue
    let flags ← cell row typeDefFlagsColumn
    if visibilityOf flags ≥ nestedVisibility then continue
    if found.isSome || visibilityOf flags != 1 || flags &&& interfaceFlag != 0 then throw invalid
    found := some row
  let some row := found | return none
  for i in [:nestedCount image] do
    if (← nestedTypeOf image (i + 1)) == row then throw invalid
  return some row

/-- The half-open range of physical Field rows owned by a TypeDef. -/
def platformFieldRange (image : PreparedImage) (row : Nat) : Except AuditError (Nat × Nat) := do
  let cell := image.layout.cellOfRow image.view Table.typeDef
  let first ← cell row typeDefFieldListColumn
  let finish ← fieldsEnd image row
  unless 1 ≤ first && first ≤ finish && finish ≤ image.layout.rowCount Table.field + 1 do
    throw (.typeDefMismatch row .fields)
  return (first, finish)

/-- A top-level ExportedType forwarder for this System type resolves an exact core AssemblyRef. -/
private def forwarder (image : PreparedImage) (name : String) (invalid : AuditError) :
    Except AuditError (Option CIL.AssemblyName) := do
  let exportedType := 0x27
  let cell := image.layout.cellOfRow image.view exportedType
  let mut target := none
  for i in [:image.layout.rowCount exportedType] do
    let row := i + 1
    unless ← stringFound image (← cell row 2) (asciiOf name ++ [0]) do continue
    unless ← stringFound image (← cell row 3) (systemNamespace ++ [0]) do continue
    let implementation ← cell row 4
    if implementation % 4 == 2 then continue  -- A nested export names its enclosing export.
    if target.isSome || implementation % 4 != 1 || implementation / 4 == 0 ||
        (← cell row 0) &&& 0x00200000 == 0 then throw invalid
    let token ← CIL.Extraction.checkedTokenOf Table.assemblyRef (implementation / 4) .rowOverflow
    unless ← coreAssemblyAt image token 0 do throw invalid
    target := some (← assemblyColumnsAt image.view image.layout token 0)
  return target

/-- The platform Assembly row carries a full public key that hashes to the recognized token. -/
def platformAssembly (image : PreparedImage) : Except AuditError Bool :=
  coreAssemblyAt image (tokenOf 0x20 1) 1

/-- Resolve a public System type through authenticated platform images and check its definition.
    A missing destination leaves coverage incomplete. A cycle or competing definition fails. -/
def resolvePlatformType (images : List PreparedImage) (name : String)
    (invalid : String → AuditError) (check : PreparedImage → Nat → Except AuditError Unit)
    (identity : CIL.AssemblyName) : Nat → Except AuditError Bool
  | 0 => throw (invalid identity.display)
  | fuel + 1 => do
    let some image := images.find? (·.assembly == identity) | return false
    let invalidHere := invalid image.identity
    unless ← platformAssembly image do throw invalidHere
    match ← definitionRow image name invalidHere, ← forwarder image name invalidHere with
    | some row, none => check image row; pure true
    | none, some next => resolvePlatformType images name invalid check next fuel
    | _, _ => throw invalidHere

end StrictBinding
