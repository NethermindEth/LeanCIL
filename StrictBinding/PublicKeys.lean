import StrictBinding.Bind
import CIL.Safety.Embedding.Step
import CIL.Extraction.Translation

/-! Compare the publisher tokens in the certified metadata with the keys of the referenced images. -/

namespace StrictBinding

open CIL.Extraction

/-- The Assembly row supplies either a full publisher key or the empty unsigned identity. -/
def definitionKeyToken (image : PreparedImage) : Except AuditError (Option Nat) := do
  let cell := image.layout.cell image.view (tokenOf 0x20 1)
  pure (publisherToken (← image.layout.blobAt image.view (← cell 6)))

/-- A publisher token for an Assembly definition comes from hashing its full key blob. -/
theorem definitionKeyToken_signed {image : PreparedImage} {token : Nat}
    (verified : definitionKeyToken image = .ok (some token)) :
    ∃ offset key, image.layout.cell image.view (tokenOf 0x20 1) 6 = .ok offset ∧
      image.layout.blobAt image.view offset = .ok key ∧ key.isEmpty = false ∧
      token = CIL.Crypto.Sha1.keyToken key := by
  unfold definitionKeyToken at verified
  obtain ⟨offset, offsetRead, rest⟩ := CIL.Safety.except_bind_ok verified
  obtain ⟨key, keyRead, rest⟩ := CIL.Safety.except_bind_ok rest
  refine ⟨offset, key, offsetRead, keyRead, ?_⟩
  simp only [pure, Except.pure, Except.ok.injEq, publisherToken] at rest
  split at rest <;> simp_all

#print axioms definitionKeyToken_signed

/-- The key or eight-byte token stored in this image's AssemblyRef row. -/
private def referenceKeyToken (image : PreparedImage) (token : Nat) :
    Except AuditError (Option Nat) := do
  let cell := image.layout.cell image.view token
  let flags ← cell 4
  let key ← image.layout.blobAt image.view (← cell 5)
  assemblyKeyToken flags key

/-- Every carried AssemblyRef retains the physical row's key or token under its heap numbering. -/
private def checkCarriedKeys (images : List PreparedImage) (slice : MetadataSlice) :
    Except AuditError Unit := do
  let source ← located images slice.assembly.identity
  let .ok index := slice.index | throw (.referenceKeyMismatch source.identity 0)
  for (token, _) in slice.rows do
    unless CIL.Extraction.metadataTableOf token == Table.assemblyRef do continue
    let .ok row := index.assemblyRef token | throw (.referenceKeyMismatch source.identity token)
    let .ok key := index.blob row.publicKeyOrToken
      | throw (.referenceKeyMismatch source.identity token)
    unless (← assemblyKeyToken row.flags key) == (← referenceKeyToken source token) do
      throw (.referenceKeyMismatch source.identity token)

/-- Compare every AssemblyRef in each extraction pin with the definition in the supplied images.
    A missing image leaves coverage incomplete. A present image must agree even then. -/
def checkPublicKeys (images : List PinnedImage) (pins : List AssemblyPin)
    (evidence : List MethodEvidence) : Except AuditError Bool := do
  let prepared ← prepare images
  let mut keys : Std.TreeMap String (Option Nat) := {}
  for image in prepared do
    keys := keys.insert image.identity (← definitionKeyToken image)
  for item in evidence do
    for slice in item.body.metadata.slices do
      unless pins.any (·.identity == slice.assembly.identity) do
        throw (.unpinned slice.assembly.identity)
      checkCarriedKeys prepared slice
  let mut complete := true
  let mut seen := false
  for pin in pins do
    let source ← located prepared pin.identity
    for i in [:source.layout.rowCount Table.assemblyRef] do
      seen := true
      let token ← checkedTokenOf Table.assemblyRef (i + 1) .rowOverflow
      let text ← assemblyIdentityAt source.view source.layout token 0
      let expected ← referenceKeyToken source token
      match keys.get? (String.ofList (text.map Char.ofNat)) with
      | none => complete := false
      | some actual =>
        unless actual == expected do throw (.referenceKeyMismatch source.identity token)
  return seen && complete

/-- All references have images whose full keys reproduce their tokens, including unsigned targets. -/
def PublicKeysBound (images : List PinnedImage) (pins : List AssemblyPin)
    (evidence : List MethodEvidence) : Prop :=
  (checkPublicKeys images pins evidence).toOption = some true

instance (images : List PinnedImage) (pins : List AssemblyPin) (evidence : List MethodEvidence) :
    Decidable (PublicKeysBound images pins evidence) := inferInstanceAs (Decidable (_ = _))

/-- Every supplied AssemblyRef target agrees with its caller's publisher token. -/
def SuppliedPublicKeysValid (images : List PinnedImage) (pins : List AssemblyPin)
    (evidence : List MethodEvidence) : Prop := ok (checkPublicKeys images pins evidence) = true

instance (images : List PinnedImage) (pins : List AssemblyPin) (evidence : List MethodEvidence) :
    Decidable (SuppliedPublicKeysValid images pins evidence) :=
  inferInstanceAs (Decidable (_ = true))

end StrictBinding
