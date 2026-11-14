import StrictBinding.Identity

/-!
# Binding claims to images

A claim names an assembly by its identity and says that some bytes belong to it at a place the
claim does not state. The audit decodes each pinned image, checks that the Assembly row spells
the identity the image is pinned under, and takes the place from the image itself: a method body
is at the file offset that the section table gives for the relative virtual address in the
method's own MethodDef row.

`checkAll` prepares the images once and runs one kind of claim check over every claim in order;
`ClaimsHold` is the proposition an audited theorem states about it, and `bodyClaimBound` is the
check for method bodies. A generated module proves the claims a page at a time, each page its own
kernel evaluation, and `claimsHold_of_pages` composes the pages into the claims.
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

/-- Every claim holds against the images prepared once, each claim checked once and in order. -/
def checkAll {Claim : Type} (check : List PreparedImage → Claim → Except AuditError Unit)
    (images : List PinnedImage) (claims : List Claim) : Except AuditError Unit := do
  let prepared ← prepare images
  claims.forM (check prepared)

/-- The proposition every audited check states: the claims hold against the pinned images. -/
def ClaimsHold {Claim : Type} (check : List PreparedImage → Claim → Except AuditError Unit)
    (images : List PinnedImage) (claims : List Claim) : Prop :=
  ok (checkAll check images claims) = true

instance {Claim : Type} (check : List PreparedImage → Claim → Except AuditError Unit)
    (images : List PinnedImage) (claims : List Claim) :
    Decidable (ClaimsHold check images claims) :=
  inferInstanceAs (Decidable (_ = _))

/-- Claims that each hold against one preparation hold together: they are checked in order. -/
theorem forM_append_ok {Claim : Type} (check : Claim → Except AuditError Unit)
    (first second : List Claim) (holdsFirst : ok (first.forM check) = true)
    (holdsSecond : ok (second.forM check) = true) :
    ok ((first ++ second).forM check) = true := by
  induction first with
  | nil => simpa using holdsSecond
  | cons claim rest ih =>
    simp only [List.cons_append, List.forM] at holdsFirst ⊢
    cases checked : check claim with
    | error _ => simp [checked, bind, Except.bind, ok] at holdsFirst
    | ok _ =>
      simp only [checked, bind, Except.bind] at holdsFirst ⊢
      exact ih holdsFirst

#print axioms forM_append_ok

/-- Two lists of claims that each hold in the pinned images hold together. -/
theorem claimsHold_append {Claim : Type}
    {check : List PreparedImage → Claim → Except AuditError Unit} {images : List PinnedImage}
    {first second : List Claim}
    (holdsFirst : ClaimsHold check images first) (holdsSecond : ClaimsHold check images second) :
    ClaimsHold check images (first ++ second) := by
  unfold ClaimsHold checkAll at *
  cases decoded : prepare images with
  | error _ => simp [decoded, bind, Except.bind, ok] at holdsFirst
  | ok prepared =>
    simp only [decoded, bind, Except.bind] at holdsFirst holdsSecond ⊢
    exact forM_append_ok (check prepared) first second holdsFirst holdsSecond

#print axioms claimsHold_append

/-- When the images decode and spell distinct identities, the empty list of claims holds. -/
theorem claimsHold_nil {Claim : Type}
    {check : List PreparedImage → Claim → Except AuditError Unit} {images : List PinnedImage}
    (prepared : ok (prepare images) = true) :
    ClaimsHold check images [] := by
  unfold ClaimsHold checkAll
  cases decoded : prepare images with
  | error _ => simp [decoded, ok] at prepared
  | ok _ => simp [bind, Except.bind, ok, List.forM, pure, Except.pure]

#print axioms claimsHold_nil

/-- The claims of page `index` when pages hold `size` claims each. -/
def claimPage {Claim : Type} (claims : List Claim) (size index : Nat) : List Claim :=
  (claims.drop (index * size)).take size

/-- The pages of claims before an index each hold. A page is one kernel evaluation, so the
    memory of a page grows with its `size` claims and not with the number of pages. -/
inductive PagesHold {Claim : Type} (holds : List Claim → Prop) (claims : List Claim)
    (size : Nat) : Nat → Prop where
  | zero : PagesHold holds claims size 0
  | succ {index : Nat} : holds (claimPage claims size index) →
      PagesHold holds claims size index → PagesHold holds claims size (index + 1)

/-- The first `count` pages of claims hold together as the claims they cover. -/
theorem claimsHold_of_first_pages {Claim : Type}
    {check : List PreparedImage → Claim → Except AuditError Unit} {images : List PinnedImage}
    {claims : List Claim} {size : Nat} (prepared : ok (prepare images) = true) :
    ∀ count, PagesHold (ClaimsHold check images) claims size count →
      ClaimsHold check images (claims.take (count * size)) := by
  intro count pages
  induction pages with
  | zero => simpa using claimsHold_nil prepared
  | @succ index page _ ih =>
    have split : claims.take ((index + 1) * size) =
        claims.take (index * size) ++ claimPage claims size index := by
      rw [Nat.succ_mul, List.take_add]; rfl
    rw [split]
    exact claimsHold_append ih page

#print axioms claimsHold_of_first_pages

/-- Pages that cover every claim give all claims, each once and in order. -/
theorem claimsHold_of_pages {Claim : Type}
    {check : List PreparedImage → Claim → Except AuditError Unit} {images : List PinnedImage}
    {claims : List Claim} {size count : Nat} (prepared : ok (prepare images) = true)
    (covers : claims.length ≤ count * size)
    (pages : PagesHold (ClaimsHold check images) claims size count) :
    ClaimsHold check images claims := by
  have whole := claimsHold_of_first_pages (claims := claims) prepared count pages
  rwa [List.take_of_length_le covers] at whole

#print axioms claimsHold_of_pages

/-- The claimed body is in the image pinned under the claim's identity, at the place that
    image's own MethodDef row gives. -/
def bodyClaimBound (prepared : List PreparedImage) (claim : BodyClaim) :
    Except AuditError Unit := do
  bodyBound (← located prepared claim.identity) claim.token claim.bytes

end StrictBinding
