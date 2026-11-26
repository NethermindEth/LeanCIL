import CIL.Extraction.IntegerMath

/-! Runtime models for System.Math division with remainder and double-width multiplication. -/

namespace CIL.Extraction

/-- The layout identity of a pair of runtime integers, including both argument scopes. -/
def integerPairIdentity (element : String) : String :=
  let argument := s!"{runtimeScope}::{element}"
  s!"{runtimeScope}::System.ValueTuple`2<{argument},{argument}>"

/-- The closed tuple resulting from DivRem, with its fields at offsets zero and one word. -/
def integerPairResult (environment : CallLayouts) (type : TypeExpr)
    (element : PrimitiveType) (width : Nat) : Bool :=
  match type with
  | .aggregate identity index =>
    let validRaw := (layoutAt? environment.indexedRaw index).any fun raw =>
      match raw.fields with
      | [first, second] => raw.identity == identity && raw.packing <= 0 &&
        element.fieldType?.any fun kind => first.type == kind && second.type == kind
      | _ => false
    identity == integerPairIdentity element.display && validRaw &&
      (layoutAt? environment.layouts index).any fun entry =>
        entry.alignment == width && entry.layout.size == 2 * width &&
          match entry.layout.fields with
          | [first, second] => first.offset == 0 && first.width == width &&
            second.offset == width && second.width == width &&
            !first.aggregate && !second.aggregate
          | _ => false
  | _ => false

/-- Each form determines the result representation and whether the last parameter is byref. -/
private inductive Form where
  | tuple | remainderOut | product | productOut
  deriving DecidableEq

/-- The scalar intrinsic or checked out-parameter write for a declared overload. -/
private def Form.model (form : Form) (width : Nat) (signed : Bool) : RuntimeModel :=
  match form with
  | .tuple => .intrinsic (.scalar (.divRem width signed)) 2
  | .remainderOut => .memory (.divRemOut width)
  | .product => .intrinsic (.scalar (.bigMul32 signed)) 2
  | .productOut => .memory (.bigMul64 signed)

/-- One concrete declaration, including the environment-local index of a tuple result. -/
private def arithmeticRow (name : String) (form : Form) (element : PrimitiveType) (width : Nat)
    (signed : Bool) : ModelOverload :=
  let word := TypeExpr.primitive element
  let out := form == .remainderOut || form == .productOut
  let parameters := if out then [word, word, .byref word] else [word, word]
  let resultType : PrimitiveType := match form with
    | .product => if signed then .int64 else .uint64
    | _ => element
  let spelled := element.display
  let result := match form with
    | .tuple => s!"System.ValueTuple`2<{spelled},{spelled}>"
    | _ => resultType.display
  let argumentNames := if out then s!"{spelled},{spelled},{spelled}&" else s!"{spelled},{spelled}"
  let target := s!"{runtimeScope}::{result} System.Math::{name}({argumentNames})"
  let returns := fun (type : TypeExpr) => match form, type with
    | .tuple, .aggregate identity _ => identity == integerPairIdentity spelled
    | .tuple, _ => false
    | _, _ => type == .primitive resultType
  -- These declarations are non-generic, so their raw types equal the selected closed types.
  { operand := .external (fun method => method.signature 0) name (fun _ => some target)
    accepts := fun method => !method.hasThis && method.genericArity == 0 &&
      method.methodArguments.isEmpty && method.parameters == parameters &&
      returns method.returnType
    resolve := fun reader method =>
      if form != .tuple || integerPairResult reader method.returnType element (width / 8)
      then some (form.model width signed) else none }

/-- The twelve division and four multiplication declarations on the runtime Math owner. -/
def wideArithmeticEntries : List ModelEntry :=
  let owner := TypeExpr.atom runtimeScope "System.Math" .classType
  let division := arithmeticRow "DivRem"
  let multiply := arithmeticRow "BigMul"
  [{ opcode := .call, owner, name := name!"DivRem", ownsName := true
     overloads := (mathIntegers.map fun (type, width, signed) => division .tuple type width signed)
       ++ [division .remainderOut .int32 32 true, division .remainderOut .int64 64 true] },
   { opcode := .call, owner, name := name!"BigMul", ownsName := true
     overloads := [multiply .product .int32 32 true, multiply .product .uint32 32 false,
       multiply .productOut .int64 64 true, multiply .productOut .uint64 64 false] }]

/-- Every admitted arithmetic overload runs an intrinsic or a checked memory operation. -/
theorem wideArithmeticEntries_yields {property : RuntimeModel → Prop}
    (intrinsic : ∀ operation argc, property (.intrinsic operation argc))
    (memory : ∀ operation, property (.memory operation)) :
    ∀ entry ∈ wideArithmeticEntries, entry.Yields property := by
  intro entry listed reader method model found
  obtain ⟨row, selected, resolved⟩ := Option.bind_eq_some_iff.mp found
  have member := ModelEntry.select?_mem selected
  have holds (name form element width signed)
      (produced : (arithmeticRow name form element width signed).resolve reader method =
        some model) : property model := by
    simp only [arithmeticRow] at produced
    split at produced
    · cases produced
      cases form <;> first | exact intrinsic _ _ | exact memory _
    · contradiction
  simp only [wideArithmeticEntries, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl <;>
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at member
  · rcases member with ⟨⟨_, _, _⟩, _, rfl⟩ | rfl | rfl <;> apply holds _ _ _ _ _ resolved
  · rcases member with rfl | rfl | rfl | rfl <;> apply holds _ _ _ _ _ resolved

#print axioms wideArithmeticEntries_yields

end CIL.Extraction
