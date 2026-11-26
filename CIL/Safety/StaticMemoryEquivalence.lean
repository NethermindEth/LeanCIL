import CIL.Safety.FrameEquivalence
import CIL.Safety.StaticMemory
import CIL.Safety.InstructionMemoryEquivalence

/-!
# Static instructions respect memory equivalence

Equivalent memories (same allocations, bytes, bindings and permissions, however the access
views are listed) give equivalent results for static field resolution and for the static
field instructions.
-/

namespace CIL.Safety

/-- Equivalent memories resolve a static to the same reference in equivalent memories. -/
theorem Memory.Equivalent.staticReference {m n : Memory} (same : m.Equivalent n)
    (descriptor : CIL.StaticDescriptor) :
    ResultEquivalent MemoryFirstEquivalent (CIL.Safety.staticReference descriptor m)
      (CIL.Safety.staticReference descriptor n) := by
  simp only [CIL.Safety.staticReference, same.staticBindings]
  cases found : n.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some binding =>
    obtain ⟨identity, reference⟩ := binding
    simp only [checkedAt, liveAllocation, same.allocations, same.read]
    repeat first
      | exact .ok ⟨same, rfl⟩
      | exact .error _
      | (apply ResultEquivalent.bind_same; intro)
      | split
  | none =>
    dsimp only
    cases flagged : descriptor.opaqueValue
    case true =>
      simp only [↓reduceIte, Bind.bind, Except.bind]
      exact .error _
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply ResultEquivalent.bind (same.allocate _ |>.mapError _)
    intro left right related
    obtain ⟨id, memory⟩ := left
    obtain ⟨other, otherMemory⟩ := right
    obtain ⟨rfl, equivalent⟩ := related
    change memory.Equivalent otherMemory at equivalent
    apply ResultEquivalent.ok
    refine ⟨?_, rfl⟩
    refine ⟨equivalent.allocations, ?_, ?_, equivalent.nextIdentity, ?_,
        equivalent.stackLimit, equivalent.heapBudget, equivalent.slots, equivalent.literals⟩
    · simp only [equivalent.cells]
    · exact (equivalent.prependView _).permissions
    · simp only [equivalent.staticBindings]

/-- Equivalent memories give equivalent results for every static or memory instruction. -/
theorem Memory.Equivalent.staticInstruction {m n : Memory} (same : m.Equivalent n)
    (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (CIL.Safety.staticInstruction body pc operation stack m)
      (CIL.Safety.staticInstruction body pc operation stack n) := by
  unfold CIL.Safety.staticInstruction
  exact same.memoryInstruction _ _

#print axioms Memory.Equivalent.staticInstruction

/-- Equivalent memories give equivalent results for `ldsfld`. -/
theorem Memory.Equivalent.staticLoad {m n : Memory} (same : m.Equivalent n)
    (body : CIL.Method) (pc : Nat) :
    ResultEquivalent MemoryFirstEquivalent (CIL.Safety.staticLoad body pc m)
      (CIL.Safety.staticLoad body pc n) := by
  unfold CIL.Safety.staticLoad
  split
  all_goals repeat first
    | exact .ok ⟨same, rfl⟩
    | exact .error _
    | (apply ResultEquivalent.bind (same.staticReference _)
       intro left right related
       obtain ⟨memory, reference⟩ := left
       obtain ⟨otherMemory, otherReference⟩ := right
       obtain ⟨equivalent, rfl⟩ := related
       simp only [checkedAt, equivalent.read]
       repeat first
         | exact .ok ⟨equivalent, rfl⟩
         | exact .error _
         | (apply ResultEquivalent.bind_same; intro)
         | split)
    | split

#print axioms Memory.Equivalent.staticLoad

/-- Equivalent memories give equivalent results for `ldsflda` and a field `ldtoken`. -/
theorem Memory.Equivalent.staticAddress {m n : Memory} (same : m.Equivalent n)
    (body : CIL.Method) (pc : Nat) :
    ResultEquivalent MemoryFirstEquivalent (CIL.Safety.staticAddress body pc m)
      (CIL.Safety.staticAddress body pc n) := by
  unfold CIL.Safety.staticAddress
  split
  · apply ResultEquivalent.bind (same.staticReference _)
    intro left right related
    obtain ⟨memory, reference⟩ := left
    obtain ⟨otherMemory, otherReference⟩ := right
    obtain ⟨equivalent, rfl⟩ := related
    exact .ok ⟨equivalent, rfl⟩
  · exact .error _

#print axioms Memory.Equivalent.staticAddress
#print axioms Memory.Equivalent.staticReference
end CIL.Safety
