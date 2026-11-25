import Extracted
import CIL.Safety.MethodContract
/-! A compiled class test follows the forwarding facade to the defining assembly. -/
namespace ForwardedClass
open CIL CIL.Extraction CIL.Safety

/-- Both derived classes have the same public base in the implementation assembly. -/
private def instanceOf (name : String) (bases : List TypeExpr) : Allocation :=
  ⟨.object ⟨.object Extracted.assembly2Scope name, bases⟩, ⟨8, 8, []⟩, true, []⟩

private def before : Safety.Memory := { Safety.Memory.empty with
  allocations := fun id =>
    let bases := [.object Extracted.assembly2Scope "Forward.Shape"]
    match id with
    | 0 => some (instanceOf "Forward.Shape" [])
    | 1 => some (instanceOf "Forward.Second" bases)
    | 2 => some (instanceOf "Forward.Family/Child" bases)
    | _ => none
  nextIdentity := 3 }

/-- References distinguish the base, both forwarded subclasses and null. -/
inductive Input where | null | base | second | child

private def reference : Input → ManagedReference
  | .null => .null
  | .base => .address ⟨0, 0⟩
  | .second => .address ⟨1, 0⟩
  | .child => .address ⟨2, 0⟩

private def expected : Input → W32
  | .second => 1
  | .child => 2
  | _ => 0

/-- The class tests preserve all three allocations and identify which subclass the caller passed. -/
def contract : MethodContract Input W32 where
  args input := [.object (reference input)]
  results value := [.scalar (.i32 value)]
  pre _ memory := memory = before
  footprint _ := []
  post input initial final value := final = initial ∧ value = expected input

/-- All four cases return at the original entry without a write. -/
theorem correctness : contract.Holds Extracted.program 0 := by
  rintro input _ rfl
  have ran : invoke Extracted.program 16 0 (contract.args input) before =
      .ok (before, contract.results (expected input)) := by cases input <;> rfl
  exact MethodContract.Holds.intro (c := contract) _ _ ⟨16, ran⟩ (Confined.refl [] _) ⟨rfl, rfl⟩
#print axioms correctness
end ForwardedClass
