import StrictBinding.EnumStorage

/-! Relate a complete enum receipt to the physical definitions of the certified method types. -/

namespace StrictBinding

open CIL CIL.Extraction

/-- A complete receipt checked every carried enum claim and the same external table as the proof. -/
theorem EnumStorageChecked.complete {images : List PinnedImage} {platform : PlatformTable}
    {methods : List MethodEvidence} (checked : EnumStorageChecked images platform methods true) :
    ∃ prepared claims, prepare images = .ok prepared ∧ methodEnumClaims platform methods = .ok claims ∧
      (∀ claim ∈ claims, carriedEnumBound prepared claim = .ok true) ∧
      coveredEnumEntries prepared platform.definitions = .ok true := by
  have done : checkEnumStorage images platform methods = .ok true := by
    cases result : checkEnumStorage images platform methods with
    | error err => simp [EnumStorageChecked, result, Except.toOption] at checked
    | ok value =>
      have yes : value = true := by simpa [EnumStorageChecked, result, Except.toOption] using checked
      rw [yes]
  unfold checkEnumStorage at done
  obtain ⟨prepared, preparedOk, done⟩ := CIL.Safety.except_bind_ok done
  obtain ⟨claims, claimsOk, done⟩ := CIL.Safety.except_bind_ok done
  obtain ⟨localChecks, localOk, done⟩ := CIL.Safety.except_bind_ok done
  obtain ⟨external, externalOk, done⟩ := CIL.Safety.except_bind_ok done
  have confirmed := Except.ok.inj done
  simp only [Bool.and_eq_true] at confirmed
  refine ⟨prepared, claims, preparedOk, claimsOk, ?_, confirmed.2 ▸ externalOk⟩
  intro claim member
  obtain ⟨result, found, read⟩ := read_member member localOk
  have yes : result = true := List.all_eq_true.mp confirmed.1.2 result found
  exact yes ▸ read
#print axioms EnumStorageChecked.complete


/-- Each certified body uses the extraction's platform table and contributes every carried enum. -/
theorem methodEnumClaims_body {platform : PlatformTable} {methods : List MethodEvidence}
    {item : MethodEvidence} {env : MetadataEnv} {claims : List CarriedEnum}
    (method : item ∈ methods) (environment : item.body.environment = .ok env)
    (checked : methodEnumClaims platform methods = .ok claims) :
    env.platform = platform ∧ ∀ claim ∈ carriedEnums env, claim ∈ claims := by
  unfold methodEnumClaims at checked
  obtain ⟨groups, groupsOk, finished⟩ := CIL.Safety.except_bind_ok checked
  obtain ⟨group, listed, selected⟩ := read_member method groupsOk
  by_cases same : env.platform = platform
  · have chosen : carriedEnums env = group := by
      simpa [environment, same, bind, Except.bind, pure, Except.pure] using selected
    refine ⟨same, ?_⟩
    intro claim found
    have equal : groups.flatten.eraseDups = claims := Except.ok.inj finished
    rw [← equal]
    exact List.mem_eraseDups.mpr (List.mem_flatten.mpr ⟨group, listed, chosen ▸ found⟩)
  · simp [environment, same, bind, Except.bind, throw] at selected
#print axioms methodEnumClaims_body

/-- The physical TypeDef row and storage code of any carried enum resolved in a certified body. -/
theorem EnumStorageChecked.carried {images : List PinnedImage} {platform : PlatformTable}
    {methods : List MethodEvidence} {item : MethodEvidence} {env : MetadataEnv}
    {position fuel token code : Nat} {named : NamedType}
    (checked : EnumStorageChecked images platform methods true) (method : item ∈ methods)
    (environment : item.body.environment = .ok env) (budget : fuel ≤ resolveFuel)
    (lookup : typeDefNamed env position fuel token = .ok named) (kind : named.kind = .enumType code) :
    ∃ prepared image, prepare images = .ok prepared ∧ image ∈ prepared ∧
      bytesOf image.identity = named.scope ∧
      enumDefinition? image 0 named.parts = .ok (some (tokenRow token)) ∧
      physicalEnumCode image (tokenRow token) = .ok code := by
  obtain ⟨prepared, claims, built, selected, covered, _⟩ := checked.complete
  have member := carriedEnums_of_typeDefNamed budget lookup kind
  have physical := covered _ ((methodEnumClaims_body method environment selected).2 _ member)
  unfold carriedEnumBound at physical
  simp only [bind, Except.bind] at physical
  cases hi : prepared.find? (fun image => bytesOf image.identity == named.scope) with
  | none => simp [hi, pure, Except.pure] at physical
  | some image =>
    have scope := List.find?_some hi
    refine ⟨prepared, image, built, List.mem_of_find?_eq_some hi, by simpa using scope, ?_⟩
    cases row : enumDefinition? image 0 named.parts with
    | error err => simp [hi, row] at physical
    | ok result =>
      cases read : physicalEnumCode image (tokenRow token) with
      | error err =>
        simp [hi, row, read, throw] at physical
        split at physical <;> contradiction
      | ok actual =>
        simp [hi, row, read, throw] at physical
        split at physical <;> try contradiction
        rename_i sameRow
        split at physical <;> try contradiction
        rename_i sameCode
        exact ⟨congrArg Except.ok (by simpa using sameRow), congrArg Except.ok (by simpa using sameCode)⟩
#print axioms EnumStorageChecked.carried

/-- A certified external enum resolves through its supplied forwarders to its physical field code. -/
theorem EnumStorageChecked.external {images : List PinnedImage} {platform : PlatformTable}
    {methods : List MethodEvidence} {item : MethodEvidence} {env : MetadataEnv} {token fuel : Nat}
    {scope : AssemblyColumns} {name : List Nat} {parts : List (List Nat)} {hint : Option Bool} {frame : Frame}
    {named : NamedType} {identity : TypeIdentity} {underlying : TypeExpr}
    (checked : EnumStorageChecked images platform methods true) (method : item ∈ methods)
    (environment : item.body.environment = .ok env)
    (resolved : env.externalNamed token scope name parts hint = .ok named)
    (admitted : typeAdmits frame (fuel + 1) (.named named) (.enum identity underlying) = true) :
    ∃ prepared, prepare images = .ok prepared ∧ ∃ code image row,
      PinnedDefinitionAt prepared named.parts named.scope image row ∧
      physicalEnumCode image row = .ok code ∧ integerElement code = true ∧
      typeAdmits frame fuel (.primitive code) underlying = true := by
  obtain ⟨prepared, _, built, selected, _, covered⟩ := checked.complete
  have same := (methodEnumClaims_body method environment selected).1
  exact ⟨prepared, built, externalEnum_physicalStorage resolved admitted (same ▸ covered)⟩
#print axioms EnumStorageChecked.external

end StrictBinding
