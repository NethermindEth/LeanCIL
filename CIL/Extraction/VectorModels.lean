import CIL.Extraction.ModelTable
import CIL.Extraction.TypeStorage

/-!
# Vector helper models

The runtime models of the vector helpers a call keeps: `Vector128.CreateScalarUnsafe` of a
`ulong`, which sets the low lane and leaves the upper lane unspecified, and `GetElement` of a
`ulong` lane of a 128- or 256-bit vector. Each entry stands for exactly one instantiated
reference of the exact `System.Runtime.Intrinsics` assembly under `call`, so a helper of
another owner, assembly, element type or signature has no model.
-/

namespace CIL.Extraction

/-- `vector<ulong>` for the generic vector type named `vector`, with exact scopes. The names
    are literals, so stepping never evaluates a string to compare a call's method. -/
def ulongVectorOf (vector : String) : TypeExpr :=
  .apply (.constructor intrinsicsScope vector) (.primitive .uint64)

/-- `Vector128<ulong> Vector128.CreateScalarUnsafe(ulong)`. -/
def createScalarUnsafeMethod : MethodRef :=
  { owner := .atom intrinsicsScope "System.Runtime.Intrinsics.Vector128",
    name := name!"CreateScalarUnsafe", hasThis := false, genericArity := 0,
    returnType := ulongVectorOf "System.Runtime.Intrinsics.Vector128`1",
    parameters := [.primitive .uint64] }

/-- `ulong owner.GetElement<ulong>(vector<ulong>, int)`, as a call site instantiates it. -/
def getElementMethod (owner vector : String) : MethodRef :=
  { owner := .atom intrinsicsScope owner, name := name!"GetElement", hasThis := false,
    genericArity := 1, returnType := .primitive .uint64,
    parameters := [ulongVectorOf vector, .primitive .int32],
    methodArguments := [.primitive .uint64] }

/-- `GetElement` of a `Vector128<ulong>` lane. -/
def getElement128Method : MethodRef :=
  getElementMethod "System.Runtime.Intrinsics.Vector128" "System.Runtime.Intrinsics.Vector128`1"

/-- `GetElement` of a `Vector256<ulong>` lane. -/
def getElement256Method : MethodRef :=
  getElementMethod "System.Runtime.Intrinsics.Vector256" "System.Runtime.Intrinsics.Vector256`1"

/-- The declaration of a generic lane read from the named vector type. -/
def getElementSignature (vector : String) : OpenSignature :=
  { convention := 0x10, returnType := .parameter 0,
    parameters := [.apply (.constructor intrinsicsScope vector) (.parameter 0),
      .primitive .int32] }

/-- The vector helper entries: each stands for one exact reference and runs as its intrinsic. -/
def vectorEntries : List ModelEntry :=
  [.exact .call createScalarUnsafeMethod (createScalarUnsafeMethod.signature 0)
      (.intrinsic (.vector .createScalarUnsafe64) 1),
    .exact .call getElement128Method (getElementSignature "System.Runtime.Intrinsics.Vector128`1")
      (.intrinsic (.vector (.extract64 128)) 2),
    .exact .call getElement256Method (getElementSignature "System.Runtime.Intrinsics.Vector256`1")
      (.intrinsic (.vector (.extract64 256)) 2)]

/-- Every model a vector helper entry resolves is an intrinsic, so a property every intrinsic
    model has holds of them. -/
theorem vectorEntries_yields {property : RuntimeModel → Prop}
    (intrinsic : ∀ operation argc, property (.intrinsic operation argc)) :
    ∀ entry ∈ vectorEntries, entry.Yields property := by
  simp only [vectorEntries, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, ModelEntry.exact_yields]
  exact ⟨intrinsic _ _, intrinsic _ _, intrinsic _ _⟩

#print axioms vectorEntries_yields

end CIL.Extraction
