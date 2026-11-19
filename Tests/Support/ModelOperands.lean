import CIL.Extraction.DecodedMethod

/-! Decoder controls and one-field refusals for external runtime model operands. -/

namespace Tests.ModelOperands

open CIL CIL.Extraction

/-- The single live call of a method with empty local and argument storage. -/
def decoded (site : CallSite) (environment : LayoutEnvironment := {})
    (profile := FeatureProfile.scalar) : Option (List Instruction) :=
  let source : RawMethod :=
    { token := 0, owner := "Fixture", hasThis := false, explicitThis := false,
      callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
      parameters := [], locals := [], initLocals := true, maxStack := 3, genericParameters := [],
      code := [⟨0, 40, .call site⟩] }
  (Method.ofRaw? profile environment [] [true] source []).map Method.code

/-- The control keeps its call. Each altered operand prevents method construction. -/
def checks (site : CallSite) : Bool :=
  let wrong := TypeExpr.atom "Fixture" "Other"
  let owner := match site.method.owner with
    | .atom _ name => TypeExpr.atom "Fixture" name
    | _ => wrong
  let parameters := match site.method.parameters with
    | [] => [wrong]
    | _ :: rest => wrong :: rest
  let variants : List CallSite := [
    { site with method.owner := owner }, { site with method.name := name!"Other" },
    { site with name := "Other" },
    { site with method.genericArity := site.method.genericArity + 1 },
    { site with method.hasThis := true }, { site with method.parameters := parameters },
    { site with method.returnType := wrong }, { site with declared.convention := 5 },
    { site with target := .external "Fixture" }]
  decide (decoded site = some [.call site.method {}]) &&
    variants.all (fun changed => decide (decoded changed = none))

end Tests.ModelOperands
