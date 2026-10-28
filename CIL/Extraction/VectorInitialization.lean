import CIL.Extraction.Generics

/-!
# Vector initialization

`initobj` (0xFE15) zeroes its target, so its emitted `initAggregate` must zero exactly the
type's width. `VectorInitializationsValid` checks that an `initAggregate` emitted for a live
`initobj` of a struct, an admitted integer vector or a primitive has the right width.
Vector object loads, stores, copies and sizes are also bound to their exact type token and
width. Loads and stores retain initialization masks; typed copies require initialized bytes.
Aggregate widths themselves are bound by the layout checks.
-/

namespace CIL.Extraction

/-- `Vector128<T>`, `Vector256<T>` or `Vector512<T>` for any `T` and scope. -/
private def vectorFamily : TypeExpr → Bool
  | .apply (.constructor _ name) _ => name ∈ ["System.Runtime.Intrinsics.Vector128`1",
      "System.Runtime.Intrinsics.Vector256`1", "System.Runtime.Intrinsics.Vector512`1"]
  | _ => false

/-- The byte width of a primitive integer, `bool` or `char` type. -/
private def primitiveWidth (type : TypeExpr) : Option Nat := do
  let .field kind ← typeStorage [] type | none
  primitiveFieldWidth kind

/-- Whether an emitted memory operation transfers a vector snapshot. -/
private def vectorMemory : Op → Bool
  | .memory .load128 | .memory .load256 | .memory .load512
  | .memory .store128 | .memory .store256 | .memory .store512 => true
  | _ => false

/-- Vector object operations preserve the exact token's storage width and opcode semantics. -/
def vectorObjectMatches (raw : RawInstruction) (emitted : Op) : Bool :=
  match raw.operand with
  | .type type =>
    if !vectorFamily type || raw.opcode ∉ [0x70, 0x71, 0x81, 0xfe15, 0xfe1c] then
      if raw.opcode ∈ [0x71, 0x81] && vectorMemory emitted then false else
      match raw.opcode, type, emitted with
      | 0x70, .aggregate .., _ => true
      | 0x70, _, .copyObject width => primitiveWidth type == some width
      | _, _, _ => true
    else match integerVectorWidth type with
      | none => false
      | some width => match raw.opcode, emitted with
        | 0x70, .copyObject bytes | 0xfe15, .initAggregate bytes => bytes == width
        | 0xfe1c, .const32 bits => bits.toNat == width
        | 0x71, .memory .load128 | 0x81, .memory .store128 => width == 16
        | 0x71, .memory .load256 | 0x81, .memory .store256 => width == 32
        | 0x71, .memory .load512 | 0x81, .memory .store512 => width == 64
        | _, _ => false
  | _ => raw.opcode ∉ [0x70, 0x71, 0x81, 0xfe15, 0xfe1c]

/-- An emitted `initAggregate` comes from an `initobj` of a struct, whose width the layout
    check binds, or of a vector or primitive of exactly that width; no other emission may
    come from an `initobj` of a vector type. -/
def vectorInitializationMatches (raw : RawInstruction) (emitted : Op) : Bool :=
  vectorObjectMatches raw emitted && match emitted with
  | .initAggregate width =>
    raw.opcode == 65045 && match raw.operand with
    | .type (.aggregate _ _) => true
    | .type type => (integerVectorWidth type).orElse (fun _ => primitiveWidth type) == some width
    | _ => false
  | _ => !(raw.opcode == 65045 && match raw.operand with
    | .type type => vectorFamily type
    | _ => false)

/-- The profile is valid and every live instruction passes `vectorInitializationMatches`. -/
def VectorInitializationsValid (closed : RawMethod) (reachable : List Bool) (method : Method) :
    Prop :=
  method.profile.Valid ∧ closed.code.length = reachable.length ∧
    closed.code.length = method.code.length ∧
  all3 (fun raw live emitted => !live || vectorInitializationMatches raw emitted)
    closed.code reachable method.code = true

instance (closed : RawMethod) (reachable : List Bool) (method : Method) :
    Decidable (VectorInitializationsValid closed reachable method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem vector_initialization_checked {closed : RawMethod} {reachable : List Bool}
    {method : Method}
    (valid : VectorInitializationsValid closed reachable method) (pc : Nat)
    (instruction : RawInstruction) (emitted : Op)
    (rawAt : closed.code[pc]? = some instruction) (liveAt : reachable[pc]? = some true)
    (emittedAt : method.code[pc]? = some emitted) :
    vectorInitializationMatches instruction emitted = true := by
  have checked := all3_at valid.2.2.2 rawAt liveAt emittedAt
  simpa using checked

#print axioms vector_initialization_checked

end CIL.Extraction
