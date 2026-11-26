import Tests.Support.RawDecoding

/-! Decoder controls and one-field refusals for external runtime model operands. -/

namespace Tests.ModelOperands

open CIL CIL.Extraction

/-- The code of the single live call of a method with empty local and argument storage, or the
    stage that refuses the method. -/
def decoded (site : CallSite) (environment : LayoutEnvironment := {})
    (profile := FeatureProfile.scalar) : Except RawDecodeError (List Instruction) :=
  let source : RawMethod :=
    { token := 0, owner := "Fixture", hasThis := false, explicitThis := false,
      callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
      parameters := [], locals := [], initLocals := true, maxStack := 3, genericParameters := [],
      code := [⟨0, 40, .call site⟩] }
  (decodeRaw profile environment [] [true] source []).map Method.code

/-- The control keeps its call. Each altered operand leaves the call a live hole at pc 0. -/
def checks (site : CallSite) : Bool :=
  let wrong := TypeExpr.atom "Fixture" "Other" .classType
  let owner := match site.method.owner with
    | .primitive type => TypeExpr.atom "Fixture" type.display .valueType
    | .atom _ name kind => TypeExpr.atom "Fixture" name kind
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
  decide (decoded site = .ok [.call site.method {}]) &&
    variants.all (fun changed => decide (decoded changed = liveHoleAt 0 40))

end Tests.ModelOperands
