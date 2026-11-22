import StrictBinding.DispatchCatalogs
import Tests.StrictBinding.Fixture
import Tests.StrictBinding.Mutation

/-! The class and method declarations of the physical virtual slot StrictFixture.Shape.Sides. -/

namespace Tests.StrictBinding.DispatchCatalogs
open CIL.Extraction _root_.StrictBinding

/-- The root class and the complete method list of every descendant, in physical row order. -/
private def declarations (bytes := StrictFixture.image) :
    Option (List (TypeExpr × Bool × List (Nat × Bool))) := do
  let image ← (prepareOne ⟨StrictFixture.identity, bytes⟩).toOption
  let owner ← (methodDeclaringType image 0x06000004).toOption
  let some types ← (ClassDispatch.physicalHierarchy image (owner % 2^24)).run.toOption | none
  return types.map fun type =>
    (type.identity, type.abstractType, type.methods.map fun m => (m.token, m.isVirtual))

/-- A pinned class name from the fixture. -/
private def named (name : String) :=
  TypeExpr.object StrictFixture.identity ("StrictFixture." ++ name)

/-- The root declares Sides, Count and its constructor. Both derived classes override Sides. -/
theorem completeDeclarations :
    declarations = some [
      (named "Shape", false, [(0x06000004,true), (0x06000005,false), (0x06000006,false)]),
      (named "Triangle", false, [(0x06000007,true), (0x06000008,false)]),
      (named "Square", false, [(0x06000009,true), (0x0600000a,false)])] := by decide +kernel
#print axioms completeDeclarations

/-- Mutate one physical metadata cell independently of the claimed declarations. -/
private def change (token column mask : Nat) : Option Bool := do
  let image ← (prepareOne ⟨StrictFixture.identity, StrictFixture.image⟩).toOption
  let (offset, _) ← (image.layout.cellAt token column).toOption
  let altered ← declarations (Tests.StrictBinding.flipByte StrictFixture.image offset mask)
  return some altered != declarations

/-- Changing the parent, abstract flag or virtual flag changes the reconstructed catalog. -/
theorem changedDeclarations :
    change 0x02000006 3 4 = some true ∧ change 0x02000007 0 128 = some true ∧
    change 0x06000007 2 64 = some true := by decide +kernel
#print axioms changedDeclarations
end Tests.StrictBinding.DispatchCatalogs
