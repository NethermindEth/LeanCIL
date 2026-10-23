import CIL.Extraction.Generics

namespace CIL.Extraction

private def vectorFamily : TypeExpr → Bool
  | .apply (.constructor _ name) _ => name ∈ ["System.Runtime.Intrinsics.Vector128`1",
      "System.Runtime.Intrinsics.Vector256`1", "System.Runtime.Intrinsics.Vector512`1"]
  | _ => false

private def vectorWidth : TypeExpr → Option Nat
  | .apply (.constructor scope name) (.atom elementScope "System.UInt64") =>
    if scope != "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51" ||
        elementScope != "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a" then none
    else if name == "System.Runtime.Intrinsics.Vector128`1" then some 16
    else if name == "System.Runtime.Intrinsics.Vector256`1" then some 32
    else if name == "System.Runtime.Intrinsics.Vector512`1" then some 64
    else none
  | _ => none

private def primitiveWidth (type : TypeExpr) : Option Nat := do
  let .field kind ← typeStorage [] type | none
  match kind with
  | .signed8 | .unsigned8 | .boolean => some 1
  | .signed16 | .unsigned16 | .character => some 2
  | .signed32 | .unsigned32 => some 4
  | .signed64 | .unsigned64 | .nativeInt | .nativeUInt => some 8
  | _ => none

def vectorInitializationMatches (raw : RawInstruction) (emitted : Op) : Bool :=
  match emitted with
  | .initAggregate width =>
    raw.opcode == 65045 && match raw.operand with
    | .type (.aggregate _ _) => true
    | .type type => (vectorWidth type).orElse (fun _ => primitiveWidth type) == some width
    | _ => false
  | _ => !(raw.opcode == 65045 && match raw.operand with
    | .type type => vectorFamily type
    | _ => false)

def VectorInitializationsValid (closed : RawMethod) (reachable : List Bool) (method : Method) : Prop :=
  method.profile.Valid ∧ closed.code.length = reachable.length ∧ closed.code.length = method.code.length ∧
  all3 (fun raw live emitted => !live || vectorInitializationMatches raw emitted)
    closed.code reachable method.code = true

instance (closed : RawMethod) (reachable : List Bool) (method : Method) :
    Decidable (VectorInitializationsValid closed reachable method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem vector_initialization_checked {closed : RawMethod} {reachable : List Bool} {method : Method}
    (valid : VectorInitializationsValid closed reachable method) (pc : Nat)
    (instruction : RawInstruction) (emitted : Op)
    (rawAt : closed.code[pc]? = some instruction) (liveAt : reachable[pc]? = some true)
    (emittedAt : method.code[pc]? = some emitted) : vectorInitializationMatches instruction emitted = true := by
  have checked := all3_at valid.2.2.2 rawAt liveAt emittedAt
  simpa using checked

#print axioms vector_initialization_checked

end CIL.Extraction
