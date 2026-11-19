import CIL.Extraction.ModelTable
import CIL.Resolution

/-!
# Unsafe helper models

The runtime models of the generic `System.Runtime.CompilerServices.Unsafe` helpers a call keeps.
Each entry covers one name of the exact `System.Runtime` owner, so a helper of another owner or
assembly, or of the owner applied to type arguments, has no model. Its resolve selects the
overload from the closed reference: a static reference of generic arity one whose parameters and
result are the overload's, rebuilt from its type argument. The element is read through
`LayoutEnvironment.valueShape`, the reader of `sizeof`, so a size comes from the checked layouts
and never from the extraction. Every entry requires an element with a size, including those that
read none (the reference comparisons and `SkipInit`): an element without one (a span, a generic
parameter, a pointer, a class, a floating-point type or a struct outside the layouts) has no
model and decodes to a hole.
-/

namespace CIL.Extraction

/-- `System.Runtime.CompilerServices.Unsafe` of the exact `System.Runtime` assembly. -/
def unsafeOwner : TypeExpr := .atom runtimeScope "System.Runtime.CompilerServices.Unsafe"

/-- The type argument of a static reference of generic arity one whose owner is exactly
    `unsafeOwner`; an owner with type arguments of its own names no helper. -/
def unsafeArgument (method : MethodRef) : Option TypeExpr :=
  if method.owner != unsafeOwner || method.hasThis || method.genericArity != 1 then none
  else match method.methodArguments with
    | [element] => some element
    | _ => none

/-- Whether `method` takes `parameters element` and returns `result element` for an element with a
    checked size. -/
def unsafeSignature (reader : CallLayouts) (method : MethodRef)
    (parameters : TypeExpr → List TypeExpr) (result : TypeExpr → TypeExpr) : Bool :=
  match unsafeArgument method with
  | some element => (reader.valueShape element).size?.isSome &&
    method.parameters == parameters element && method.returnType == result element
  | none => false

/-- `model` when `admitted` holds. -/
def unsafeGuarded (admitted : Bool) (model : RuntimeModel) : Option RuntimeModel :=
  if admitted then some model else none

/-- A guarded model is the model it guards. -/
theorem unsafeGuarded_eq {admitted : Bool} {model resolved : RuntimeModel}
    (found : unsafeGuarded admitted model = some resolved) : resolved = model := by
  unfold unsafeGuarded at found
  split at found <;> cases found
  rfl

#print axioms unsafeGuarded_eq

/-- The size of the element of `int Unsafe.SizeOf<T>()`. -/
def unsafeSizeOf (reader : CallLayouts) (method : MethodRef) : Option Nat := do
  let element ← unsafeArgument method
  if !method.parameters.isEmpty || method.returnType != .atom runtimeScope "System.Int32" then
    none
  (reader.valueShape element).size?

/-- `Unsafe.SizeOf<T>` pushes the size of `T`, as `sizeof T` does. -/
def unsafeSizeOfModel (reader : CallLayouts) (method : MethodRef) :
    Option RuntimeModel :=
  (unsafeSizeOf reader method).map fun size => .constant (BitVec.ofNat 32 size)

/-- `bool Unsafe.AreSame<T>(ref T, ref T)` and the two address orders compare their references by
    `relation`. -/
def unsafeCompareModel (relation : ReferenceRelation) (reader : CallLayouts)
    (method : MethodRef) : Option RuntimeModel :=
  let boolean := TypeExpr.atom runtimeScope "System.Boolean"
  unsafeGuarded (unsafeSignature reader method
    (fun element => [.byref element, .byref element]) (fun _ => boolean))
    (.referenceCompare relation)

/-- `void Unsafe.SkipInit<T>(out T)` forms its out reference and writes nothing. -/
def unsafeSkipInitModel (reader : CallLayouts) (method : MethodRef) :
    Option RuntimeModel :=
  unsafeGuarded (unsafeSignature reader method (fun element => [.byref element])
    (fun _ => .void)) .skipInit

/-- The open declaration of a generic Unsafe helper of arity one: the generic convention, and the
    helper's parameters and result over its method type parameter `!!0`. -/
def unsafeDeclaration (parameters : TypeExpr → List TypeExpr) (result : TypeExpr → TypeExpr) :
    OpenSignature :=
  { convention := 0x10, returnType := result (.parameter 0),
    parameters := parameters (.parameter 0) }

/-- The exact external member and open declaration for one Unsafe overload. -/
def unsafeOperand (name result parameters : String) (declared : OpenSignature) : ModelOperand :=
  let owner := "System.Runtime.CompilerServices.Unsafe"
  let target := s!"{runtimeScope}::{result} {owner}::{name}({parameters})"
  .external declared name (fun _ => some target)

/-- The reserved `call` entry for a single Unsafe overload. -/
def unsafeEntry (key : MetadataName) (name result parameters : String) (declared : OpenSignature)
    (resolve : CallLayouts → MethodRef → Option RuntimeModel) : ModelEntry :=
  .single .call unsafeOwner key (unsafeOperand name result parameters declared) resolve true

/-- The open declaration `bool (ref !!0, ref !!0)` of the reference comparisons. -/
def unsafeComparisonDeclaration : OpenSignature :=
  unsafeDeclaration (fun element => [.byref element, .byref element])
    (fun _ => .atom runtimeScope "System.Boolean")

/-- The Unsafe helper entries. -/
def unsafeEntries : List ModelEntry :=
  [unsafeEntry name!"SizeOf" "SizeOf" "System.Int32" ""
    (unsafeDeclaration (fun _ => []) (fun _ => .atom runtimeScope "System.Int32"))
    unsafeSizeOfModel,
   unsafeEntry name!"AreSame" "AreSame" "System.Boolean" "!!0&,!!0&"
     unsafeComparisonDeclaration (unsafeCompareModel .same),
   unsafeEntry name!"IsAddressLessThan" "IsAddressLessThan" "System.Boolean" "!!0&,!!0&"
     unsafeComparisonDeclaration
     (unsafeCompareModel .less),
   unsafeEntry name!"IsAddressGreaterThan" "IsAddressGreaterThan" "System.Boolean" "!!0&,!!0&"
     unsafeComparisonDeclaration
     (unsafeCompareModel .greater),
   unsafeEntry name!"SkipInit" "SkipInit" "System.Void" "!!0&"
     (unsafeDeclaration (fun element => [.byref element]) (fun _ => .void)) unsafeSkipInitModel]

/-- Every model an Unsafe entry resolves is a constant, a reference comparison or `SkipInit`, so a
    property those models have holds of them. -/
theorem unsafeEntries_yields {property : RuntimeModel → Prop}
    (constant : ∀ value, property (.constant value))
    (compare : ∀ relation, property (.referenceCompare relation))
    (skipInit : property .skipInit) :
    ∀ entry ∈ unsafeEntries, entry.Yields property := by
  simp only [unsafeEntries, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro environment method model found <;>
    simp only [unsafeEntry, ModelEntry.resolve_single, unsafeSizeOfModel, unsafeCompareModel,
      unsafeSkipInitModel, Option.map_eq_some_iff] at found
  · rcases found with ⟨_, _, rfl⟩
    exact constant _
  all_goals
    rw [unsafeGuarded_eq found]
    first | exact compare _ | exact skipInit

#print axioms unsafeEntries_yields

end CIL.Extraction
