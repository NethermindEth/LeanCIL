import StrictBinding.EnumEvidence
import CIL.Extraction.BodyDecoding

/-! Enum storage claims of TypeDef rows in the method's own and referenced slices. -/

namespace StrictBinding

open CIL CIL.Extraction

/-- The row and typed enum declaration that a carried definition resolves to. -/
structure CarriedEnum where
  row : Nat
  entry : PlatformDefinition
  deriving DecidableEq, Repr

/-- Read from the exact slice and TypeDef token the default decoder uses. -/
def carriedEnum? (env : MetadataEnv) (position token : Nat) : Option CarriedEnum := do
  guard (metadataTableOf token == Table.typeDef)
  let named ← (typeDefNamed env position resolveFuel token).toOption
  let .enumType code := named.kind | none
  let assembly ← named.assembly
  return ⟨tokenRow token, ⟨assembly, named.parts, .enumType code named.platformArity⟩⟩

/-- Enumerate every carried row from the checked indexes, once per slice. -/
def carriedEnums (env : MetadataEnv) : List CarriedEnum :=
  env.slices.toList.flatMap fun (position, index) =>
    index.rows.toList.filterMap fun (token, _) => carriedEnum? env position token

/-- A successful lookup of a row in a carried slice places its enum in this audit. -/
theorem carriedEnum_mem {env : MetadataEnv} {position token : Nat} {index : MetadataIndex}
    {bytes : List Nat} {entry : CarriedEnum} (slice : env.slices.find? position = some index)
    (row : index.rows.find? token = some bytes) (enum : carriedEnum? env position token = some entry) :
    entry ∈ carriedEnums env := by
  unfold carriedEnums
  apply List.mem_flatMap.mpr
  refine ⟨(position, index), SearchTree.find?_mem_toList _ _ _ slice, ?_⟩
  exact List.mem_filterMap.mpr ⟨(token, bytes), SearchTree.find?_mem_toList _ _ _ row, enum⟩
#print axioms carriedEnum_mem

/-- Every enum resolved by the decoder at a carried TypeDef is selected from the same environment. -/
theorem carriedEnums_of_typeDefNamed {env : MetadataEnv} {position fuel token code : Nat}
    {named : NamedType} (budget : fuel ≤ resolveFuel)
    (lookup : typeDefNamed env position fuel token = .ok named)
    (kind : named.kind = .enumType code) :
    ∃ assembly, named.assembly = some assembly ∧
      ⟨tokenRow token, ⟨assembly, named.parts, .enumType code named.platformArity⟩⟩ ∈
        carriedEnums env := by
  have resolved := typeDefNamed_of_le budget lookup
  have original := resolved
  obtain ⟨_, _, assembled⟩ := typeDefNamed_assembly resolved
  refine ⟨_, assembled, ?_⟩
  unfold typeDefNamed at resolved
  obtain ⟨index, located, later⟩ := CIL.Safety.except_bind_ok resolved
  obtain ⟨row, decoded, _⟩ := CIL.Safety.except_bind_ok later
  obtain ⟨typed, bytes, fromRow⟩ := MetadataIndex.typeDef_bytes decoded
  unfold MetadataEnv.slice at located
  cases fromSlice : env.slices.find? position with
  | none => simp [fromSlice] at located
  | some found =>
    simp only [fromSlice, Except.ok.injEq] at located
    subst found
    apply carriedEnum_mem fromSlice fromRow
    simp [carriedEnum?, original, typed, guard, pure, Option.bind, Except.toOption, kind, assembled]
#print axioms carriedEnums_of_typeDefNamed

/-- Check both the physical TypeDef token and its field code. A missing assembly leaves the
    claim uncovered. An incorrect declaration in a supplied assembly fails. -/
def carriedEnumBound (images : List PreparedImage) (claim : CarriedEnum) : Except AuditError Bool := do
  let some image := images.find? (·.assembly == claim.entry.assembly) | return false
  let .enumType code _ := claim.entry.kind | throw (.typeDefMismatch claim.row .kind)
  unless (← enumDefinition? image 0 claim.entry.parts) == some claim.row do
    throw (.typeDefMismatch claim.row .typeName)
  unless (← physicalEnumCode image claim.row) == code do throw (.typeDefMismatch claim.row .fields)
  return true

end StrictBinding
