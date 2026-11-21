import CIL.Extraction.ModelTable

/-!
# Integer math helpers

`Math.Min`, `Max`, `Clamp`, `Abs` and `Sign` on one integer type, and the same helpers that
each primitive integer type declares, are modelled by the scalar intrinsic of that operation, width
and signedness. Each entry covers one owner and name, so a helper of another owner or assembly
has no model, and its resolve gives a model only to a static, non-generic reference whose
parameters and result are that integer type, `Sign` returning `System.Int32`.
-/

namespace CIL.Extraction

/-- The integer types the helpers are modelled on, with their width in bits and signedness; the
    native integers are 64 bits wide. -/
def mathIntegers : List (String × Nat × Bool) :=
  [("System.SByte", 8, true), ("System.Byte", 8, false),
    ("System.Int16", 16, true), ("System.UInt16", 16, false),
    ("System.Int32", 32, true), ("System.UInt32", 32, false),
    ("System.Int64", 64, true), ("System.UInt64", 64, false),
    ("System.IntPtr", 64, true), ("System.UIntPtr", 64, false)]

/-- The modelled helpers by metadata name, with their operation and number of parameters. -/
def mathOperations : List (MetadataName × IntegerMath × Nat) :=
  [(name!"Min", .min, 2), (name!"Max", .max, 2), (name!"Clamp", .clamp, 3),
    (name!"Abs", .abs, 1), (name!"Sign", .sign, 1)]

/-- Whether `operation` is defined only on signed integers. -/
def _root_.CIL.IntegerMath.signedOnly : IntegerMath → Bool
  | .abs | .sign => true
  | .min | .max | .clamp => false

/-- The width and signedness for a helper taking `arity` parameters of one integer type, fixed
    for a primitive owner. The result is that type, or `System.Int32` for `Sign`. -/
def integerMathOperand (operation : IntegerMath) (arity : Nat) (fixed : Option TypeExpr)
    (returned : TypeExpr) (parameters : List TypeExpr) : Option (Nat × Bool) := do
  let parameter ← parameters.head?
  if parameters != List.replicate arity parameter then none
  if fixed.any (· != parameter) then none
  let .atom scope name := parameter | none
  if scope != runtimeScope then none
  let (width, signed) ← mathIntegers.lookup name
  if operation.signedOnly && !signed then none
  let result := if operation == .sign then TypeExpr.atom runtimeScope "System.Int32" else parameter
  if returned != result then none
  some (width, signed)

/-- The model of a call of `method` as the helper `operation` of `arity` parameters: the scalar
    intrinsic at the width and signedness of the integer type it takes. -/
def integerMathModel (operation : IntegerMath) (arity : Nat) (fixed : Option TypeExpr)
    (method : MethodRef) : Option RuntimeModel := do
  if method.hasThis || method.genericArity != 0 || !method.methodArguments.isEmpty then none
  let (width, signed) ←
    integerMathOperand operation arity fixed method.returnType method.parameters
  some (.intrinsic (.scalar (.math operation width signed)) arity)

/-- The `call` entry of the helper `name` declared by `owner`, whose parameters must be
    `fixed` when given. -/
def integerMathEntry (owner : TypeExpr) (fixed : Option TypeExpr)
    (helper : MetadataName × IntegerMath × Nat) : ModelEntry :=
  let (name, operation, arity) := helper
  .single .call owner name (.declaration fun sig => sig.convention == 0 &&
    (integerMathOperand operation arity fixed sig.returnType sig.parameters).isSome)
    (fun _ => integerMathModel operation arity fixed)

/-- The helpers of `System.Math`, then those each integer type declares on itself; an unsigned
    type declares no `Abs` or `Sign`. -/
def integerMathEntries : List ModelEntry :=
  mathOperations.map (integerMathEntry (.atom runtimeScope "System.Math") none) ++
    mathIntegers.flatMap fun (name, _, signed) =>
      let owner := TypeExpr.atom runtimeScope name
      (mathOperations.filter fun (_, operation, _) => signed || !operation.signedOnly).map
        (integerMathEntry owner (some owner))

/-- Every model an integer math entry resolves is an intrinsic, so a property every intrinsic
    model has holds of them. -/
theorem integerMathEntries_yields {property : RuntimeModel → Prop}
    (intrinsic : ∀ operation argc, property (.intrinsic operation argc)) :
    ∀ entry ∈ integerMathEntries, entry.Yields property := by
  intro entry _ environment method model found
  have resolved : ∃ operation arity fixed, integerMathModel operation arity fixed method =
      some model := by
    simp only [integerMathEntries, integerMathEntry, List.mem_append, List.mem_map,
      List.mem_flatMap, List.mem_filter] at *
    rename_i member
    rcases member with ⟨helper, _, rfl⟩ | ⟨integer, _, helper, _, rfl⟩ <;>
      exact ⟨_, _, _, found⟩
  rcases resolved with ⟨operation, arity, fixed, resolved⟩
  unfold integerMathModel at resolved
  split at resolved
  · contradiction
  obtain ⟨⟨width, signed⟩, _, same⟩ := Option.bind_eq_some_iff.mp resolved
  cases same
  exact intrinsic _ _

#print axioms integerMathEntries_yields

end CIL.Extraction
