import CIL.Extraction.DecodedDefinition
import StrictBinding.Bind

/-!
# Checked metadata layouts for generated image audits

The kernel checks compact headers against `prepare` on the pinned bytes. Restoring a checked
header reads its byte view from the corresponding pin and its column offsets from its layout.
-/

namespace StrictBinding.PreparedImages

open Lean

deriving instance DecidableEq, ToExpr for Section
deriving instance DecidableEq, ToExpr for Stream
deriving instance DecidableEq, ToExpr for PeLayout
deriving instance DecidableEq, ToExpr for TableRows
deriving instance DecidableEq, ToExpr for MetadataLayout

/-- The metadata and method-column positions of a prepared image. -/
structure Header where
  identity : String
  assembly : CIL.AssemblyName
  layout : MetadataLayout
  rvaColumn : Nat × Nat
  implementationColumn : Nat × Nat
  deriving DecidableEq, ToExpr

/-- The decoded header fields retained from a prepared image. -/
private def Header.ofPrepared (image : PreparedImage) : Header :=
  ⟨image.identity, image.assembly, image.layout, image.rvaColumn, image.implementationColumn⟩

/-- The result of `prepare` with one compact header per image. -/
def headers (pins : List PinnedImage) : Except AuditError (List Header) :=
  (prepare pins).map fun images => images.map Header.ofPrepared

/-- The prepared image with the pin's original byte view and the layout's column table. -/
private def Header.restore (pin : PinnedImage) (header : Header) : PreparedImage :=
  { identity := header.identity, assembly := header.assembly, layout := header.layout,
    view := (ImageView.ofImage pin.image).toOption.getD ⟨0, none⟩,
    rvaColumn := header.rvaColumn, implementationColumn := header.implementationColumn,
    columns := header.layout.columnTable }

/-- Restores headers against the pins in order and preserves errors from `prepare`. -/
def restore (pins : List PinnedImage) (result : Except AuditError (List Header)) :
    Except AuditError (List PreparedImage) :=
  result.map (pins.zipWith Header.restore)

/-- A successful `prepareOne` returns the byte view of its pin and the columns of its layout. -/
private theorem restore_one {pin : PinnedImage} {image : PreparedImage}
    (valid : prepareOne pin = .ok image) :
    Header.restore pin (Header.ofPrepared image) = image := by
  cases viewEq : ImageView.ofImage pin.image with
  | error err => simp [prepareOne, viewEq, bind, Except.bind] at valid
  | ok view =>
    simp only [prepareOne, viewEq, bind, Except.bind, pure, Except.pure] at valid
    repeat' split at valid
    all_goals simp_all [Header.restore, Header.ofPrepared]
    subst image
    rfl

#print axioms restore_one

/-- A successful traversal pairs each recorded header with its own input pin. -/
private theorem restore_list {pins : List PinnedImage} {images : List PreparedImage}
    (valid : pins.mapM prepareOne = .ok images) :
    pins.zipWith Header.restore (images.map Header.ofPrepared) = images := by
  induction pins generalizing images with
  | nil => simpa [List.mapM_nil, pure, Except.pure] using valid.symm
  | cons pin pins ih =>
    cases first : prepareOne pin with
    | error err => simp [List.mapM_cons, first, bind, Except.bind] at valid
    | ok image =>
      cases rest : pins.mapM prepareOne with
      | error err => simp [List.mapM_cons, first, rest, bind, Except.bind] at valid
      | ok tail =>
        simp [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure] at valid
        subst images
        simp [restore_one first, ih rest]

#print axioms restore_list

/-- Restoring the headers preserves every field and error of `prepare`. -/
theorem restore_headers (pins : List PinnedImage) : restore pins (headers pins) = prepare pins := by
  cases prepared : prepare pins with
  | error err => simp [restore, headers, prepared, Except.map]
  | ok images =>
    have allPins : pins.mapM prepareOne = .ok images := by
      unfold prepare at prepared
      cases traversal : pins.mapM prepareOne with
      | error err => simp [traversal, bind, Except.bind] at prepared
      | ok output =>
        cases dup : duplicateIdentity? output with
        | some name => simp [traversal, dup, bind, Except.bind] at prepared
        | none =>
          simp [traversal, dup, bind, Except.bind, pure, Except.pure] at prepared
          rw [prepared]
    simp [restore, headers, prepared, Except.map, restore_list allPins]

#print axioms restore_headers

/-- Compares all recorded header fields or the error returned by `prepare`. -/
def sameResult (left right : Except AuditError (List Header)) : Bool :=
  match left, right with
  | .ok first, .ok second => decide (first = second)
  | .error first, .error second => decide (first = second)
  | _, _ => false

/-- Checked headers reconstruct the images returned by `prepare` without comparing byte trees. -/
theorem prepare_eq_of_checked {pins : List PinnedImage} {result : Except AuditError (List Header)}
    (same : sameResult (headers pins) result = true) : prepare pins = restore pins result := by
  have exactResult : headers pins = result := by
    cases original : headers pins <;> cases result <;> simp_all [sameResult]
  rw [← exactResult, restore_headers]

#print axioms prepare_eq_of_checked

/-- Candidate headers from one call to `prepare`. On an ill-formed pin, the generated facts
    expose the error returned by that check. -/
def resultExpr (pins : List PinnedImage) (pinList : Expr) : Expr :=
  match headers pins with
  | .error _ => mkApp (mkConst ``headers) pinList
  | .ok values =>
    mkApp3 (mkConst ``Except.ok [.zero, .zero]) (mkConst ``AuditError)
      (mkApp (mkConst ``List [.zero]) (mkConst ``Header)) (toExpr values)

end StrictBinding.PreparedImages
