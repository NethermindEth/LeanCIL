import CIL.Extraction.Generics

namespace CIL.Extraction

private def runtimeScope : String :=
  "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"

/-- Recognize the external helper from raw metadata, independently of translation. -/
def skipInitCall (layouts : List RawLayout) (instruction : RawInstruction) : Bool :=
  match instruction.opcode, instruction.operand with
  | 0x28, .call site =>
    site.declaringType == .atom runtimeScope "System.Runtime.CompilerServices.Unsafe" &&
    site.name == "SkipInit" &&
    site.target == .external (runtimeScope ++
      "::System.Void System.Runtime.CompilerServices.Unsafe::SkipInit(!!0&)") &&
    site.parameterCount == 1 && !site.hasThis && !site.returnsValue &&
    match site.typeArguments with
    | [type] => match typeStorage layouts type with
      | some .reference | none => false
      | some _ => true
    | _ => false
  | _, _ => false

/-- Bind both directions: a recognized call must skip initialization, and an
    emitted skip cannot replace an unrelated instruction. -/
def SkipInitValid (layouts : List RawLayout) (closed : RawMethod)
    (reachable : List Bool) (code : List Op) : Prop :=
  closed.code.length = reachable.length ∧ closed.code.length = code.length ∧
  all3 (fun instruction live emitted => !live ||
    skipInitCall layouts instruction == (match emitted with
      | .skipInit => true
      | _ => false)) closed.code reachable code = true

instance (layouts : List RawLayout) (closed : RawMethod)
    (reachable : List Bool) (code : List Op) : Decidable (SkipInitValid layouts closed reachable code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end CIL.Extraction
