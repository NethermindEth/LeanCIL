import StrictBinding.DefinitionRoute
import CIL.Extraction.MetadataResolution

/-! Bind the storage of an admitted enum to the selected physical definition. -/

namespace StrictBinding

open CIL CIL.Extraction

/-- Missing scope images leave their enum entries uncovered. A bad supplied definition fails. -/
def coveredEnumEntry (images : List PreparedImage) (entry : PlatformDefinition) :
    Except AuditError Bool := do
  let .enumType code _ := entry.kind | return true
  let some (image, row) ← findPinnedDefinition images entry.parts entry.scope (images.length + 1)
    | return false
  unless (← physicalEnumCode image row) == code do throw (.typeDefMismatch row .fields)
  return true

/-- Check every entry, including entries after an unavailable image. -/
def coveredEnumEntries (images : List PreparedImage) :
    List PlatformDefinition → Except AuditError Bool
  | [] => .ok true
  | head :: rest => do
    let first ← coveredEnumEntry images head
    let remaining ← coveredEnumEntries images rest
    return first && remaining

/-- Complete coverage includes each entry of the table. -/
theorem coveredEnumEntries_each {images : List PreparedImage} {entries : List PlatformDefinition}
    (checked : coveredEnumEntries images entries = .ok true) {entry} (member : entry ∈ entries) :
    coveredEnumEntry images entry = .ok true := by
  induction entries with
  | nil => simp at member
  | cons head rest ih =>
    simp only [coveredEnumEntries] at checked
    obtain ⟨first, read, checked⟩ := CIL.Safety.except_bind_ok checked
    obtain ⟨remaining, tail, accepted⟩ := CIL.Safety.except_bind_ok checked
    change Except.ok (ε := AuditError) (first && remaining) = .ok true at accepted
    simp only [Except.ok.injEq, Bool.and_eq_true] at accepted
    obtain ⟨firstTrue, remainingTrue⟩ := accepted
    rcases List.mem_cons.mp member with rfl | later
    · exact firstTrue ▸ read
    · exact ih (remainingTrue ▸ tail) later
#print axioms coveredEnumEntries_each

/-- The element code an extracted enum operand admits is the code in its physical backing field. -/
theorem externalEnum_physicalStorage {images : List PreparedImage} {env : MetadataEnv} {token : Nat}
    {scope : AssemblyColumns} {name : List Nat} {parts : List (List Nat)} {hint : Option Bool} {frame : Frame}
    {fuel : Nat} {named : NamedType} {identity : TypeIdentity} {underlying : TypeExpr}
    (resolved : env.externalNamed token scope name parts hint = .ok named)
    (admitted : typeAdmits frame (fuel + 1) (.named named) (.enum identity underlying) = true)
    (checked : coveredEnumEntries images env.platform.definitions = .ok true) :
    ∃ code image row, PinnedDefinitionAt images named.parts named.scope image row ∧
      physicalEnumCode image row = .ok code ∧ integerElement code = true ∧
      typeAdmits frame fuel (.primitive code) underlying = true := by
  obtain ⟨_, code, member, integer, representation⟩ := typeAdmits_external_enum resolved admitted
  have covered := coveredEnumEntries_each checked member
  simp only [coveredEnumEntry, bind, Except.bind] at covered
  cases selected : findPinnedDefinition images named.parts named.scope (images.length + 1) with
  | error fault => simp [selected] at covered
  | ok result =>
    cases result with
    | none => simp [selected, pure, Except.pure] at covered
    | some pair =>
      obtain ⟨image, row⟩ := pair
      cases read : physicalEnumCode image row with
      | error fault => simp [selected, read] at covered
      | ok actual =>
        simp [selected, read] at covered
        split at covered <;> try contradiction
        rename_i same
        exact ⟨code, image, row, pinnedDefinitionAt_of_find selected, same ▸ read, integer,
          representation⟩
#print axioms externalEnum_physicalStorage

end StrictBinding
