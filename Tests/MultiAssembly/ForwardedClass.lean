import Extracted
import CIL.Safety.MethodContract
/-! A compiled class test follows the forwarding facade to the defining assembly. -/
namespace ForwardedClass
open CIL CIL.Safety

/-- Both allocations have their runtime class in the implementation assembly. -/
private def before : Safety.Memory := { Safety.Memory.empty with
  allocations := fun id =>
    if id == 0 then some ⟨.object ⟨.object Extracted.assembly2.identity "Forward.Shape", []⟩,
      ⟨8, 8, []⟩, true, []⟩
    else if id == 1 then some ⟨.object ⟨.object Extracted.assembly2.identity "Forward.Second",
      [.object Extracted.assembly2.identity "Forward.Shape"]⟩, ⟨8, 8, []⟩, true, []⟩
    else none
  nextIdentity := 2 }

/-- Three receiver cases for the compiled class test. -/
inductive Input where | null | base | child

private def reference : Input → ManagedReference
  | .null => .null
  | .base => .address ⟨0, 0⟩
  | .child => .address ⟨1, 0⟩

private def expected : Input → W32
  | .child => 1
  | _ => 0

/-- The caller retains both objects and receives one exactly for a derived instance. -/
def contract : MethodContract Input W32 where
  args input := [.object (reference input)]
  results value := [.scalar (.i32 value)]
  pre _ memory := memory = before
  footprint _ := []
  post input initial final value := final = initial ∧ value = expected input

/-- All three cases return at the original entry without a write. -/
theorem correctness : contract.Holds Extracted.program 0 := by
  rintro input _ rfl
  have ran : invoke Extracted.program 16 0 (contract.args input) before =
      .ok (before, contract.results (expected input)) := by cases input <;> rfl
  exact MethodContract.Holds.intro (c := contract) _ _ ⟨16, ran⟩ (Confined.refl [] _) ⟨rfl, rfl⟩
#print axioms correctness
end ForwardedClass
