import StrictBinding.GenericConstraints
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation

namespace Tests.StrictBinding.PlatformKinds

open CIL.Extraction _root_.StrictBinding

private def shape (row : Nat) : Option (_root_.StrictBinding.TypeKind × Nat) := do
  let image ← (prepareOne ⟨StrictFixture.identity, StrictFixture.image⟩).toOption
  (physicalTypeShape image row).toOption

/-- Small, Overlay, Shape and Triangle have their CLI kinds in the compiled fixture. -/
theorem compiled_type_shapes :
    shape 2 = some (.enum, 0) ∧ shape 3 = some (.valueType, 0) ∧
    shape 5 = some (.classType, 0) ∧ shape 6 = some (.classType, 0) ∧
    shape 3 ≠ some (.classType, 0) ∧ shape 5 ≠ some (.classType, 1) := by decide +kernel
#print axioms compiled_type_shapes

/-- The fixture has one final AssemblyRef row. Give its table slot to GenericParam and
    set the ordinal and TypeOrMethodDef owner in the resulting physical row. -/
private def parameterImage (ordinal owner flags : Nat) : Except AuditError PreparedImage := do
  let start := StrictFixture.expectedFacts.findSome? fun fact => match fact with
    | .stream "tables" offset _ => some offset
    | _ => none
  let last := StrictFixture.expectedFacts.findSome? fun fact => match fact with
    | .table 0x23 _ _ offset => some offset
    | _ => none
  let some tables := start | throw (.typeDefMismatch 6 .kind)
  let some field := last | throw (.typeDefMismatch 6 .kind)
  let bytes := flipBytes StrictFixture.image
    [(tables + 12, 0x08), (tables + 13, 0x04), (field, 11 ^^^ ordinal),
     (field + 2, flags), (field + 4, owner)]
  prepareOne ⟨StrictFixture.identity, bytes⟩

/-- The physical arity of the sixth TypeDef after assigning the parameter row. -/
private def withParameter (ordinal owner : Nat) : Except AuditError Nat := do
  physicalTypeArity (← parameterImage ordinal owner 0) 6

/-- Only the target TypeDef's parameter contributes to its arity. A gap in its ordinals fails. -/
theorem type_parameter_ownership :
    (withParameter 0 12).toOption = some 1 ∧ (withParameter 0 10).toOption = some 0 ∧
    (withParameter 0 13).toOption = some 0 ∧
    failsWith (withParameter 1 12) (.typeDefMismatch 6 .kind) = true := by decide +kernel
#print axioms type_parameter_ownership

private def overlay (kind : PlatformKind) : PlatformDefinition :=
  { scope := bytesOf StrictFixture.identity
    parts := [asciiOf "StrictFixture", asciiOf "Overlay"]
    kind }

private def checkKinds (claims : List PlatformDefinition) : Except AuditError Bool := do
  let image ← prepareOne ⟨StrictFixture.identity, StrictFixture.image⟩
  return (← claims.mapM (coveredPlatformKind [image])).all id

/-- The pinned Overlay definition is a nongeneric value type. A missing assembly leaves
    coverage partial and cannot conceal another entry with the wrong physical kind. -/
theorem physical_kind_and_partial_coverage :
    let absent := { overlay .valueType with scope := bytesOf "Missing" }
    (checkKinds [overlay .valueType]).toOption = some true ∧
    (checkKinds [absent, overlay .valueType]).toOption = some false ∧
    failsWith (checkKinds [absent, overlay .classType]) (.typeDefMismatch 3 .kind) = true ∧
    failsWith (checkKinds [overlay (.genericValue 1), absent]) (.typeDefMismatch 3 .kind) = true := by
  decide +kernel
#print axioms physical_kind_and_partial_coverage

/-- The first MethodDef's declaration in an image with one physical generic parameter. -/
private def methodParameter (ordinal owner flags : Nat) (claims : List GenericConstraint) :
    Except AuditError Unit := do
  let image ← parameterImage ordinal owner flags
  parameterDeclarations image (_root_.StrictBinding.tokenOf Table.methodDef 1) claims

/-- Moving a parameter to the owning type, altering its flags or ordinal, adding a constraint,
    or omitting the parameter cannot reconfirm the original method declaration. -/
theorem method_parameter_declaration :
    let present : GenericConstraint := ⟨24, [], []⟩
    let mismatch := AuditError.constraintMismatch (_root_.StrictBinding.tokenOf Table.methodDef 1)
    (methodParameter 0 3 24 [present]).toOption = some () ∧
    failsWith (methodParameter 0 2 24 [present]) mismatch = true ∧
    failsWith (methodParameter 0 3 8 [present]) mismatch = true ∧
    failsWith (methodParameter 1 3 24 [present]) mismatch = true ∧
    failsWith (methodParameter 0 3 24 [{present with types := ["IForged"]}]) mismatch = true ∧
    failsWith (methodParameter 0 3 24 []) mismatch = true := by decide +kernel
#print axioms method_parameter_declaration

end Tests.StrictBinding.PlatformKinds
