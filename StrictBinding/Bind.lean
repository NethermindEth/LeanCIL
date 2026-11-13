import StrictBinding.Identity

/-!
# Binding claims to images

A claim names an assembly by its identity and says that some bytes belong to it at a place the
claim does not state. The audit decodes each pinned image, checks that the Assembly row spells
the identity the image is pinned under, and takes the place from the image itself: a method body
is at the file offset that the section table gives for the relative virtual address in the
method's own MethodDef row.

`bodiesBound` is the check and `BodiesBound` the proposition an audited theorem states about it.
Each further kind of claim is another `Except` check over the same prepared images and a
proposition of the form `ok (check ...) = true`.
-/

namespace StrictBinding

/-- A pinned image, decoded: its identity, the checked view of its bytes and its tables. -/
structure PreparedImage where
  identity : String
  view : ImageView
  layout : MetadataLayout
  /-- The offset and width of the RVA column of a MethodDef row, computed once. -/
  rvaColumn : Nat × Nat
  /-- The offset and width of the implementation flags column of a MethodDef row. -/
  implementationColumn : Nat × Nat

/-- A pinned image decoded, with its identity checked against its Assembly row. -/
def prepareOne (pinned : PinnedImage) : Except AuditError PreparedImage := do
  let view ← ImageView.ofImage pinned.image
  let layout ← decodeMetadata view
  if (← assemblyIdentity view layout) != asciiOf pinned.identity then
    throw (.identityMismatch pinned.identity)
  pure { identity := pinned.identity, view, layout, rvaColumn := ← layout.columnIn 0x06 0,
         implementationColumn := ← layout.columnIn 0x06 1 }

/-- The identity of the first prepared image that a later one repeats. -/
def duplicateIdentity? : List PreparedImage → Option String
  | [] => none
  | image :: rest =>
    if rest.any (·.identity == image.identity) then some image.identity
    else duplicateIdentity? rest

/-- Every pinned image decoded, once, with distinct identities. -/
def prepare (images : List PinnedImage) : Except AuditError (List PreparedImage) := do
  let prepared ← images.mapM prepareOne
  match duplicateIdentity? prepared with
  | some identity => throw (.duplicateImage identity)
  | none => pure prepared

/-- The prepared image that is pinned under `identity`. -/
def located (prepared : List PreparedImage) (identity : String) :
    Except AuditError PreparedImage :=
  match prepared.find? (·.identity == identity) with
  | some image => pure image
  | none => throw (.unpinned identity)

/-- A claim that the bytes of a method body, its header and its code, belong to the assembly
    `identity`, as the body of the method that `token` names. -/
structure BodyClaim where
  identity : String
  /-- A MethodDef token. -/
  token : Nat
  bytes : List Nat

/-- The MethodDef row of the claim has a body and the claimed bytes are at the file offset its
    relative virtual address maps to. -/
def bodyBound (image : PreparedImage) (token : Nat) (bytes : List Nat) :
    Except AuditError Unit := do
  if token / 2 ^ 24 != 0x06 then throw (.notMethodDef token)
  let (row, _) ← image.layout.rowAt token
  let rva ← image.view.u (row + image.rvaColumn.1) image.rvaColumn.2
  let implementation ←
    image.view.u (row + image.implementationColumn.1) image.implementationColumn.2
  if rva == 0 || implementation % 4 != 0 then throw (.noIlBody token)
  let offset ← mapRva image.layout.pe.sections rva bytes.length
  unless (← image.view.hasBytesAt offset bytes) do throw (.bodyMismatch token rva offset)

/-- Every claim in order is in the image that it names, at the place that image's own MethodDef
    row gives. -/
def claimsBound (prepared : List PreparedImage) : List BodyClaim → Except AuditError Unit
  | [] => pure ()
  | claim :: rest => do
    bodyBound (← located prepared claim.identity) claim.token claim.bytes
    claimsBound prepared rest

/-- Every claimed body is in the pinned image that its claim names, at the place that image's
    own MethodDef row gives. -/
def bodiesBound (images : List PinnedImage) (claims : List BodyClaim) :
    Except AuditError Unit := do
  claimsBound (← prepare images) claims

/-- Every claimed body is in its image at the place its MethodDef row gives. -/
def ClaimedBodiesBound (images : List PinnedImage) (claims : List BodyClaim) : Prop :=
  ok (bodiesBound images claims) = true

instance (images : List PinnedImage) (claims : List BodyClaim) :
    Decidable (ClaimedBodiesBound images claims) :=
  inferInstanceAs (Decidable (_ = _))

/-- Claims that each hold hold together: claims are checked one after another. -/
theorem claimsBound_append (prepared : List PreparedImage) (first second : List BodyClaim)
    (holdsFirst : ok (claimsBound prepared first) = true)
    (holdsSecond : ok (claimsBound prepared second) = true) :
    ok (claimsBound prepared (first ++ second)) = true := by
  induction first with
  | nil => simpa [claimsBound] using holdsSecond
  | cons claim rest ih =>
    simp only [List.cons_append, claimsBound] at holdsFirst ⊢
    cases lookup : located prepared claim.identity with
    | error _ => simp [lookup, bind, Except.bind, ok] at holdsFirst
    | ok image =>
      cases bound : bodyBound image claim.token claim.bytes with
      | error _ => simp [lookup, bound, bind, Except.bind, ok] at holdsFirst
      | ok _ =>
        simp only [lookup, bound, bind, Except.bind] at holdsFirst ⊢
        exact ih holdsFirst

#print axioms claimsBound_append

/-- Two lists of claims that each hold in the pinned images hold together. -/
theorem bodiesBound_append (images : List PinnedImage) (first second : List BodyClaim)
    (holdsFirst : ok (bodiesBound images first) = true)
    (holdsSecond : ok (bodiesBound images second) = true) :
    ok (bodiesBound images (first ++ second)) = true := by
  unfold bodiesBound at *
  cases decoded : prepare images with
  | error _ => simp [decoded, bind, Except.bind, ok] at holdsFirst
  | ok prepared =>
    simp only [decoded, bind, Except.bind] at holdsFirst holdsSecond ⊢
    exact claimsBound_append prepared first second holdsFirst holdsSecond

#print axioms bodiesBound_append

/-- When the images decode and spell their identities, the empty list of claims holds. -/
theorem bodiesBound_nil {images : List PinnedImage}
    (prepared : ok (prepare images) = true) : ok (bodiesBound images []) = true := by
  unfold bodiesBound
  cases decoded : prepare images with
  | error _ => simp [decoded, ok] at prepared
  | ok _ => simp [bind, Except.bind, claimsBound, ok, pure, Except.pure]

#print axioms bodiesBound_nil

/-- The claims of page `index` when pages hold `size` claims each. -/
def claimPage (claims : List BodyClaim) (size index : Nat) : List BodyClaim :=
  (claims.drop (index * size)).take size

/-- The pages of the claims before an index each hold. A page is one kernel evaluation, so the
    memory of a page grows with its `size` claims and not with the number of pages. -/
inductive ClaimPagesBound (images : List PinnedImage) (claims : List BodyClaim) (size : Nat) :
    Nat → Prop where
  | zero : ClaimPagesBound images claims size 0
  | succ {index : Nat} : ClaimedBodiesBound images (claimPage claims size index) →
      ClaimPagesBound images claims size index → ClaimPagesBound images claims size (index + 1)

/-- The first `count` pages of claims hold together as the claims they cover. -/
theorem claimedBodiesBound_of_first_pages {images : List PinnedImage} {claims : List BodyClaim}
    {size : Nat} (prepared : ok (prepare images) = true) :
    ∀ count, ClaimPagesBound images claims size count →
      ClaimedBodiesBound images (claims.take (count * size)) := by
  intro count pages
  induction pages with
  | zero => simpa [ClaimedBodiesBound] using bodiesBound_nil prepared
  | @succ index page _ ih =>
    have split : claims.take ((index + 1) * size) =
        claims.take (index * size) ++ claimPage claims size index := by
      rw [Nat.succ_mul, List.take_add]; rfl
    rw [split]
    exact bodiesBound_append images _ _ ih page

#print axioms claimedBodiesBound_of_first_pages

/-- Pages that cover every claim, each page holding, give the claims: they are covered once and
    in order. -/
theorem claimedBodiesBound_of_pages {images : List PinnedImage} {claims : List BodyClaim}
    {size count : Nat} (prepared : ok (prepare images) = true)
    (covers : claims.length ≤ count * size) (pages : ClaimPagesBound images claims size count) :
    ClaimedBodiesBound images claims := by
  have whole := claimedBodiesBound_of_first_pages (claims := claims) prepared count pages
  rwa [List.take_of_length_le covers] at whole

#print axioms claimedBodiesBound_of_pages

end StrictBinding
