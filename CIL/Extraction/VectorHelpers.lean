import CIL.Extraction.ModelTable
import CIL.Extraction.TransferKinds

/-! Runtime models for portable vector construction, whole-vector equality and byte transfers. -/

namespace CIL.Extraction

/-- One vector declaration and the operation its admitted instantiations execute. -/
private inductive VectorMember where
  | create (width bits count : Nat)
  | combine
  | span (width : Nat)
  | equal (width : Nat)
  | transfer (store offset : Bool)

/-- The helper class or vector constructor, and its unscoped metadata spelling. -/
private def vectorOwnerName (width : Nat) := s!"System.Runtime.Intrinsics.Vector{width}"

/-- A signature component and the text the external member reference spells for it. -/
private abbrev VectorOperand := TypeExpr × String

/-- The named runtime primitive. -/
private def primitiveOperand (name : String) : VectorOperand :=
  (.atom runtimeScope name, name)

/-- The vector constructor applied to an open parameter or concrete element. -/
private def vectorOperand (width : Nat) (element : VectorOperand) : VectorOperand :=
  let head := vectorOwnerName width ++ "`1"
  (.apply (.constructor intrinsicsScope head) element.1, s!"{head}<{element.2}>")

/-- The single-word broadcast used by the AVX2 execution lemmas. -/
def broadcast256Method : MethodRef :=
  let word := TypeExpr.atom runtimeScope "System.UInt64"
  { owner := .atom intrinsicsScope "System.Runtime.Intrinsics.Vector256",
    name := name!"Create", hasThis := false, genericArity := 0,
    returnType := .apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector256`1") word,
    parameters := [word] }

/-- The result and parameters of a declaration at the supplied type argument. -/
private def VectorMember.signature (member : VectorMember) (element : VectorOperand) :
    VectorOperand × List VectorOperand :=
  match member with
  | .create width bits count =>
    let word := primitiveOperand (if bits == 32 then "System.UInt32" else "System.UInt64")
    (vectorOperand width word, List.replicate count word)
  | .combine =>
    let word := primitiveOperand "System.UInt64"
    (vectorOperand 512 word, List.replicate 2 (vectorOperand 256 word))
  | .span width =>
    (vectorOperand width element, [(.apply (.constructor runtimeScope "System.ReadOnlySpan`1")
      element.1, s!"System.ReadOnlySpan`1<{element.2}>")])
  | .equal width =>
    (primitiveOperand "System.Boolean", List.replicate 2 (vectorOperand width element))
  | .transfer store offset =>
    let vector := vectorOperand 128 element
    let address := (TypeExpr.byref element.1, element.2 ++ "&")
    let tail := if offset then [primitiveOperand "System.UIntPtr"] else []
    (if store then (.void, "System.Void") else vector,
      (if store then [vector, address] else [address]) ++ tail)

/-- The existing checked operation for this overload. -/
private def VectorMember.model (reader : CallLayouts) (method : MethodRef) :
    VectorMember → Option RuntimeModel
  | .create width bits count =>
    some (.intrinsic (.vector (if bits == 32 then .create32 width else .create64 width)) count)
  | .combine => some (.intrinsic (.vector .combine256) 2)
  | .span _ => (transferKind? reader method.returnType).map fun kind =>
      .memory (.marshalRead kind false)
  | .equal width => some (.intrinsic (.vector (.equalsAll width)) 2)
  | .transfer store offset => some (.memory (.vector128Unsafe store offset))

/-- The element of a concrete vector equality reference, or the byte of a generic helper. -/
private def VectorMember.element (member : VectorMember) (method : MethodRef) :
    Option VectorOperand :=
  match member with
  | .equal _ => do
    guard (integerVectorWidth method.owner).isSome
    let .apply _ (.atom _ name) := method.owner | none
    return primitiveOperand name
  | _ => some (primitiveOperand "System.Byte")

/-- The open operand and disjoint closed signature for one declaration in a reserved slot. -/
private def VectorMember.row (member : VectorMember) (width : Nat) (key : MetadataName)
    (name : String) : ModelOverload :=
  let generic := member matches .span _ | .transfer ..
  let equal := member matches .equal _
  let argument : VectorOperand :=
    if equal then (.ownerParameter 0, "!0") else (.parameter 0, "!!0")
  let (result, parameters) := member.signature argument
  let decl : OpenSignature :=
    { convention := if generic then 16 else 0, returnType := result.1,
      parameters := parameters.map Prod.fst }
  let owner := vectorOwnerName width
  let target (method : MethodRef) := do
    let element ← member.element method
    let declaring := if equal then (vectorOperand width element).2 else owner
    let names := ",".intercalate (parameters.map Prod.snd)
    return s!"{intrinsicsScope}::{result.2} {declaring}::{name}({names})"
  let accepts (method : MethodRef) := (member.element method).any fun element =>
    let (closedResult, closedParams) := member.signature element
    let declaring := if equal then (vectorOperand width element).1 else .atom intrinsicsScope owner
    method.owner == declaring && method.name == key && !method.hasThis &&
      method.genericArity == (if generic then 1 else 0) &&
      method.methodArguments == (if generic then [element.1] else []) &&
      method.returnType == closedResult.1 && method.parameters == closedParams.map Prod.fst
  { operand := .external (fun _ => decl) name target, accepts,
    resolve := fun reader method => member.model reader method }

/-- A vector name owns all its overloads at the given owner head. -/
private def vectorSlot (width : Nat) (key : MetadataName) (name : String)
    (members : List VectorMember) (genericOwner := false) : ModelEntry :=
  let owner := vectorOwnerName width
  { opcode := .call, name := key, ownsName := true,
    owner := if genericOwner then .constructor intrinsicsScope (owner ++ "`1")
      else .atom intrinsicsScope owner,
    overloads := members.map (fun member => member.row width key name) }

/-- The four scalar and span constructions of a 128- or 256-bit vector. -/
private def createSlot (width : Nat) : ModelEntry :=
  vectorSlot width name!"Create" "Create"
    [.create width 64 1, .create width 64 (width / 64), .create width 32 (width / 32), .span width]

/-- The declarations for portable construction, equality and byte-reference transfer. -/
def vectorHelperEntries : List ModelEntry :=
  [createSlot 128, createSlot 256, vectorSlot 512 name!"Create" "Create" [.combine],
   vectorSlot 128 name!"LoadUnsafe" "LoadUnsafe" [.transfer false false, .transfer false true],
   vectorSlot 128 name!"StoreUnsafe" "StoreUnsafe" [.transfer true false, .transfer true true]] ++
  [128, 256, 512].map (fun width =>
    vectorSlot width name!"op_Equality" "op_Equality" [.equal width] true)

/-- Every model of a vector overload runs the declared intrinsic or checked transfer. -/
theorem vectorHelperEntries_yields {property : RuntimeModel → Prop}
    (intrinsic : ∀ operation count, property (.intrinsic operation count))
    (memory : ∀ operation, property (.memory operation)) :
    ∀ entry ∈ vectorHelperEntries, entry.Yields property := by
  have slot (width key name members genericOwner) :
      (vectorSlot width key name members genericOwner).Yields property := by
    intro reader method model found
    obtain ⟨row, selected, resolved⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨member, _, rfl⟩ := List.mem_map.mp (ModelEntry.select?_mem selected)
    change member.model reader method = some model at resolved
    cases member <;> simp only [VectorMember.model, Option.map_eq_some_iff, Option.some.injEq]
      at resolved
    all_goals first
      | subst model; apply intrinsic
      | subst model; apply memory
      | obtain ⟨_, _, rfl⟩ := resolved; apply memory
  intro entry listed
  simp only [vectorHelperEntries, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at listed
  rcases listed with (rfl | rfl | rfl | rfl | rfl) | ⟨_, _, rfl⟩ <;> apply slot

#print axioms vectorHelperEntries_yields

end CIL.Extraction
