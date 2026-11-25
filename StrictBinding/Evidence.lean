import StrictBinding.Slice
import CIL.Extraction.Translation

/-!
# Extraction evidence bound to images

The propositions that generated audit modules state about an extraction: each one reads the
constants of `Extracted` that `Extracted.translation_valid` certifies and asks a check of
`StrictBinding.Bind` about them. The audit proves them in the same environment as that
certificate, so they describe the certified evidence and no other.
-/

namespace StrictBinding

/-- The body each method evidence record carries, with the assembly and token it names. -/
def bodyClaims (evidence : List CIL.Extraction.MethodEvidence) : List BodyClaim :=
  evidence.map fun item =>
    { identity := item.assembly.identity, token := item.original.token, bytes := item.body.bytes }

/-- Every method body of the evidence is the bytes at the place the MethodDef row of its token
    gives, in the pinned image of the assembly the evidence names. -/
def BodiesBound (images : List PinnedImage) (evidence : List CIL.Extraction.MethodEvidence) :
    Prop :=
  ClaimsHold bodyClaimBound images (bodyClaims evidence)

instance (images : List PinnedImage) (evidence : List CIL.Extraction.MethodEvidence) :
    Decidable (BodiesBound images evidence) :=
  inferInstanceAs (Decidable (ClaimsHold _ _ _))

/-- The rows, heaps and core-library AssemblyRef of each carried slice are checked against the
    image selected by its assembly's identity. Cost is one lookup and one contents check per
    carried slice; the Assembly blocks are checked by `assemblyBlockBound`. -/
def methodMetadataBound (prepared : List PreparedImage)
    (metadata : CIL.Extraction.MethodMetadata) : Except AuditError Unit :=
  metadata.slices.forM fun slice => do
    let image <- located prepared slice.assembly.identity
    sliceContentsBound image slice

/-- A carried Assembly block, with the identity and key token it states, is checked against the
    image selected by its identity. -/
def assemblyBlockBound (prepared : List PreparedImage)
    (assembly : CIL.Extraction.AssemblyMetadata) : Except AuditError Unit := do
  let image <- located prepared assembly.identity
  assemblyBound image assembly

/-- The carried metadata of each method, in evidence order. -/
def metadataClaims (evidence : List CIL.Extraction.MethodEvidence) :
    List CIL.Extraction.MethodMetadata := evidence.map (fun item => item.body.metadata)

/-- The distinct Assembly blocks the metadata carries, in first-occurrence order. Blocks are
    compared whole, so two blocks with one identity and different bytes are both kept. -/
def assemblyBlocks (claims : List CIL.Extraction.MethodMetadata) :
    List CIL.Extraction.AssemblyMetadata :=
  (claims.flatMap fun metadata => metadata.slices.map fun slice => slice.assembly).eraseDups

/-- Every carried metadata block belongs to its named pinned image, modulo heap numbering: each
    distinct Assembly block, with its identity and the key token the image's key gives, is
    checked once, and the rows, heaps and core-library AssemblyRef of every slice. -/
def MetadataRowsBound (images : List PinnedImage) (evidence : List CIL.Extraction.MethodEvidence) :
    Prop :=
  And (ClaimsHold assemblyBlockBound images (assemblyBlocks (metadataClaims evidence)))
    (ClaimsHold methodMetadataBound images (metadataClaims evidence))

instance (images : List PinnedImage) (evidence : List CIL.Extraction.MethodEvidence) :
    Decidable (MetadataRowsBound images evidence) :=
  inferInstanceAs (Decidable (And _ _))

/-- A successful traversal checked every member successfully. -/
theorem check_of_forM_ok {Claim : Type} {check : Claim -> Except AuditError Unit}
    {claims : List Claim} (holds : ok (claims.forM check) = true) :
    forall claim, List.Mem claim claims -> ok (check claim) = true := by
  induction claims with
  | nil => intro claim member; cases member
  | cons first rest onRest =>
    cases checked : check first with
    | error error => simp [List.forM, checked, bind, Except.bind, ok] at holds
    | ok value =>
      simp only [List.forM, checked, bind, Except.bind] at holds
      intro claim member
      cases member with
      | head => simp [checked, ok]
      | tail _ member => exact onRest holds claim member

#print axioms check_of_forM_ok

/-- Every claim holds individually against the same successful image preparation. -/
theorem check_of_claimsHold {Claim : Type}
    {check : List PreparedImage -> Claim -> Except AuditError Unit}
    {images : List PinnedImage} {claims : List Claim}
    (holds : ClaimsHold check images claims) :
    Exists fun prepared => And (prepare images = .ok prepared)
      (forall claim, List.Mem claim claims -> ok (check prepared claim) = true) := by
  unfold ClaimsHold checkAll at holds
  cases decoded : prepare images with
  | error error => simp [decoded, bind, Except.bind, ok] at holds
  | ok prepared =>
    simp only [decoded, bind, Except.bind] at holds
    exact Exists.intro prepared (And.intro rfl (check_of_forM_ok holds))

#print axioms check_of_claimsHold

/-- Every member of a successful image preparation has bounded chunks. -/
theorem prepare_bounded {images : List PinnedImage} {prepared : List PreparedImage}
    (decoded : prepare images = .ok prepared) :
    forall image, List.Mem image prepared -> image.view.Bounded := by
  have mapped : forall (images : List PinnedImage) (prepared : List PreparedImage),
      images.mapM prepareOne = .ok prepared ->
      forall image, List.Mem image prepared -> image.view.Bounded := by
    intro images
    induction images with
    | nil =>
      intro prepared decoded image member
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at decoded
      subst prepared
      cases member
    | cons pinned rest onRest =>
      intro prepared decoded image member
      rw [List.mapM_cons] at decoded
      cases CIL.Safety.except_bind_ok decoded with
      | intro first firstResult =>
        cases CIL.Safety.except_bind_ok firstResult.2 with
        | intro later laterResult =>
          have same : first :: later = prepared := Except.ok.inj laterResult.2
          subst prepared
          cases member with
          | head => exact prepareOne_bounded firstResult.1
          | tail _ member => exact onRest later laterResult.1 image member
  unfold prepare at decoded
  cases CIL.Safety.except_bind_ok decoded with
  | intro result checks =>
    cases repeated : duplicateIdentity? result with
    | some identity => simp [repeated, throw] at checks
    | none =>
      have same : result = prepared := by
        simpa [repeated, pure, Except.pure] using checks.2
      subst prepared
      exact mapped images result checks.1

#print axioms prepare_bounded

/-- Every carried block is bound to its selected image from one preparation of the pins. -/
theorem sliceMatches_of_metadataRowsBound {images : List PinnedImage}
    {evidence : List CIL.Extraction.MethodEvidence} (bound : MetadataRowsBound images evidence) :
    Exists fun prepared => And (prepare images = .ok prepared)
      (forall item, List.Mem item evidence ->
        forall slice, List.Mem slice item.body.metadata.slices ->
          Exists fun image => And (located prepared slice.assembly.identity = .ok image)
            (SliceMatches image slice)) := by
  cases check_of_claimsHold bound.2 with
  | intro prepared checks =>
    cases check_of_claimsHold bound.1 with
    | intro blockPrepared blockChecks =>
      have samePreparation : prepared = blockPrepared :=
        Except.ok.inj (checks.1.symm.trans blockChecks.1)
      subst samePreparation
      refine Exists.intro prepared (And.intro checks.1 ?_)
      intro item member slice carried
      have metadataMember : List.Mem item.body.metadata (metadataClaims evidence) :=
        List.mem_map.mpr (Exists.intro item (And.intro member rfl))
      have checked := checks.2 item.body.metadata metadataMember
      have one := check_of_forM_ok checked slice carried
      have sliceAssembly :
          List.Mem slice.assembly (item.body.metadata.slices.map fun slice => slice.assembly) :=
        List.mem_map.mpr (Exists.intro slice (And.intro carried rfl))
      have blockMember : List.Mem slice.assembly (assemblyBlocks (metadataClaims evidence)) :=
        List.mem_eraseDups.mpr (List.mem_flatMap.mpr (Exists.intro item.body.metadata
          (And.intro metadataMember sliceAssembly)))
      have blockOne := blockChecks.2 slice.assembly blockMember
      cases found : located prepared slice.assembly.identity with
      | error error => simp [found, bind, Except.bind, ok] at one
      | ok image =>
        refine Exists.intro image (And.intro rfl ?_)
        have imageMember : List.Mem image prepared := mem_of_located found
        have contents : sliceContentsBound image slice = .ok () := by
          cases result : sliceContentsBound image slice with
          | error error => simp [found, result, bind, Except.bind, ok] at one
          | ok value => cases value; rfl
        have assembly : assemblyBound image slice.assembly = .ok () := by
          unfold assemblyBlockBound at blockOne
          cases result : assemblyBound image slice.assembly with
          | error error => simp [found, result, bind, Except.bind, ok] at blockOne
          | ok value => cases value; rfl
        exact sliceMatches_of_bounds (prepare_bounded checks.1 image imageMember) assembly contents

#print axioms sliceMatches_of_metadataRowsBound

end StrictBinding
