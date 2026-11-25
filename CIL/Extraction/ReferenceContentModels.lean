import CIL.Extraction.ModelTable

/-! The reference-content query for types with checked reference-free storage. -/

namespace CIL.Extraction

/-- The generic RuntimeHelpers member with no parameters and a Boolean result. -/
private def queryOwner :=
  TypeExpr.atom runtimeScope "System.Runtime.CompilerServices.RuntimeHelpers"

/-- The open declaration has one method parameter and no value parameters. -/
private def queryDeclaration : OpenSignature :=
  { convention := 0x10, returnType := .primitive .boolean }

/-- The exact open MemberRef whose closed type argument supplies the queried storage. -/
private def queryOperand : ModelOperand :=
  let name := "IsReferenceOrContainsReferences"
  let owner := "System.Runtime.CompilerServices.RuntimeHelpers"
  let target := s!"{runtimeScope}::System.Boolean {owner}::{name}()"
  .external (fun _ => queryDeclaration) name (fun _ => some target)

/-- Only the static query closed over one method argument has this result. -/
private def querySignature (method : MethodRef) : Bool :=
  !method.hasThis && method.genericArity == 1 && method.methodArguments.length == 1 &&
    method.signature 0x10 == queryDeclaration

/-- Field storage binds a primitive, enum or aggregate. Vectors must have integer lanes. -/
private def queryValue (storage : TypeExpr → Option StorageType) (method : MethodRef) :
    Option W32 := do
  let [element] := method.methodArguments | none
  guard ((storage element matches some (.field _)) || (integerVectorWidth element).isSome)
  return 0

/-- The query's single reserved overload reads storage through the checked layout index. -/
private def queryEntry : ModelEntry :=
  let row : ModelOverload :=
    { operand := queryOperand, accepts := querySignature
      resolve := fun reader method => RuntimeModel.constant <$> queryValue reader.storage method }
  { opcode := .call, owner := queryOwner, name := name!"IsReferenceOrContainsReferences",
    overloads := [row], ownsName := true }

/-- The reference-content model family. -/
def referenceContentEntries := [queryEntry]

/-- Reachability reads the same operand, closed signature and indexed storage as the model. -/
def referenceContentFact (layouts : Array RawLayout) (site : CallSite) : Option W32 := do
  guard (site.method.name == queryEntry.name && site.method.owner == queryOwner &&
    querySignature site.method && queryOperand.bindsSite site)
  queryValue (typeStorageAt (layouts[·]?)) site.method

/-- The reference-content query resolves only to a constant model. -/
theorem referenceContentEntries_yields {property : RuntimeModel → Prop}
    (constant : ∀ value, property (.constant value)) :
    ∀ entry ∈ referenceContentEntries, entry.Yields property := by
  intro entry listed reader method model found
  obtain rfl := List.mem_singleton.mp listed
  simp only [ModelEntry.resolve, queryEntry, ModelEntry.select?, ModelEntry.select?.select] at found
  split at found <;> simp_all
  obtain ⟨_, _, rfl⟩ := found
  exact constant _

#print axioms referenceContentEntries_yields

end CIL.Extraction
