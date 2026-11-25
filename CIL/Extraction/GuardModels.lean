import CIL.Extraction.ModelTable

/-! The null and integer argument guards called through System.Runtime. -/

namespace CIL.Extraction

/-- The integer guard determines the number and order of operands before the parameter name. -/
private inductive GuardKind where
  | null
  | zero (operation : ZeroGuard)
  | comparison (operation : ComparisonGuard)

/-- The integer guard reads the low bits at the declared width and signedness. -/
private def guardInteger (element : TypeExpr) : Option (Nat × Bool) := do
  let .primitive type := element | none
  match type with
  | .sbyte => some (8, true)
  | .byte => some (8, false)
  | .int16 => some (16, true)
  | .uint16 => some (16, false)
  | .int32 => some (32, true)
  | .uint32 => some (32, false)
  | .int64 | .intPtr => some (64, true)
  | .uint64 | .uintPtr => some (64, false)
  | .boolean | .char | .single | .double => none

/-- Every guard has a final string argument naming the parameter. -/
private def GuardKind.signature (kind : GuardKind) (element : TypeExpr) : OpenSignature :=
  let label := TypeExpr.object runtimeScope "System.String"
  match kind with
  | .null => { convention := 0, parameters := [.atom runtimeScope "System.Object", label] }
  | .zero _ => { convention := 0x10, parameters := [element, label] }
  | .comparison _ => { convention := 0x10, parameters := [element, element, label] }

/-- The closed reference instantiates the same value type in each integer argument. -/
private def GuardKind.accepts (kind : GuardKind) (method : MethodRef) : Bool :=
  !method.hasThis && match kind, method.genericArity, method.methodArguments with
  | .null, 0, [] => method.signature 0 == kind.signature .void
  | .zero _, 1, [element] | .comparison _, 1, [element] =>
    method.signature 0x10 == kind.signature element
  | _, _, _ => false

/-- The selected operation reads the same checked operands as the integer or null guard. -/
private def GuardKind.operation (kind : GuardKind) (method : MethodRef) : Option MemoryOp := do
  match kind with
  | .null => return .throwIfNull
  | .zero operation =>
    let (width, signed) ← method.methodArguments.head? >>= guardInteger
    return .zeroGuard operation width signed
  | .comparison operation =>
    let (width, signed) ← method.methodArguments.head? >>= guardInteger
    return .comparisonGuard operation width signed

/-- The owned guard row binds the uninstantiated member and its assembly-qualified target. -/
private def guardEntry (key : MetadataName) (name : String) (kind : GuardKind) : ModelEntry :=
  let (owner, parameters) := match kind with
    | .null => ("System.ArgumentNullException", "System.Object,System.String")
    | .zero _ => ("System.ArgumentOutOfRangeException", "!!0,System.String")
    | .comparison _ => ("System.ArgumentOutOfRangeException", "!!0,!!0,System.String")
  let target := s!"{runtimeScope}::System.Void {owner}::{name}({parameters})"
  let row : ModelOverload :=
    { operand := .external (fun _ => kind.signature (.parameter 0)) name (fun _ => some target)
      accepts := kind.accepts
      resolve := fun _ method => RuntimeModel.memory <$> kind.operation method }
  { opcode := .call, owner := .atom runtimeScope owner, name := key, ownsName := true,
    overloads := [row] }

/-- The runtime row whose object parameter requires object-reference provenance on the stack. -/
def nullGuardEntry := guardEntry name!"ThrowIfNull" "ThrowIfNull" .null

/-- The reserved runtime slots of the null guard and each integer guard. -/
def guardEntries : List ModelEntry := [
  nullGuardEntry,
  guardEntry name!"ThrowIfZero" "ThrowIfZero"
    (.zero .zero),
  guardEntry name!"ThrowIfNegative" "ThrowIfNegative"
    (.zero .negative),
  guardEntry name!"ThrowIfNegativeOrZero" "ThrowIfNegativeOrZero"
    (.zero .negativeOrZero),
  guardEntry name!"ThrowIfEqual" "ThrowIfEqual"
    (.comparison .equal),
  guardEntry name!"ThrowIfNotEqual" "ThrowIfNotEqual"
    (.comparison .notEqual),
  guardEntry name!"ThrowIfGreaterThan" "ThrowIfGreaterThan"
    (.comparison .greaterThan),
  guardEntry name!"ThrowIfGreaterThanOrEqual" "ThrowIfGreaterThanOrEqual"
    (.comparison .greaterThanOrEqual),
  guardEntry name!"ThrowIfLessThan" "ThrowIfLessThan"
    (.comparison .lessThan),
  guardEntry name!"ThrowIfLessThanOrEqual" "ThrowIfLessThanOrEqual"
    (.comparison .lessThanOrEqual)]

/-- A guard row resolves only to a checked memory operation. -/
private theorem guardEntry_yields {key name kind} {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation)) :
    (guardEntry key name kind).Yields property := by
  intro reader method model found
  simp only [ModelEntry.resolve, guardEntry, ModelEntry.select?, ModelEntry.select?.select] at found
  split at found <;> simp_all
  obtain ⟨_, _, rfl⟩ := found
  exact memory _

#print axioms guardEntry_yields

/-- Each guard transports and executes as its checked memory operation. -/
theorem guardEntries_yields {property : RuntimeModel → Prop}
    (memory : ∀ operation, property (.memory operation)) :
    ∀ entry ∈ guardEntries, entry.Yields property := by
  intro entry listed
  simp only [guardEntries, List.mem_cons, List.not_mem_nil, or_false] at listed
  repeat' rcases listed with rfl | listed
  all_goals first | exact guardEntry_yields memory | subst entry; exact guardEntry_yields memory

#print axioms guardEntries_yields

end CIL.Extraction
