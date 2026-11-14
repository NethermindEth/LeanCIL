import StrictBinding.Bind
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

end StrictBinding
