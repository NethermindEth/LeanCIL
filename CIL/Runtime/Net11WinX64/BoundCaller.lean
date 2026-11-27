import CIL.Extraction.BodyDecoding

/-! A caller whose exception constructions link to the bound .NET 11 Windows x64 image. -/

namespace CIL.Runtime.Net11WinX64
open CIL.Extraction

/-- A caller's body with the image's dependency rows and links, the original method decoded
    from that body, and the construction link of each bound site. -/
structure BoundCaller where
  body : BodyEvidence
  original : RawMethod
  links : List (Nat × Link)

end CIL.Runtime.Net11WinX64
