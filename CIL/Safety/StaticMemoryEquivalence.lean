import CIL.Safety.FrameEquivalence
import CIL.Safety.StaticMemory
import CIL.Safety.InstructionMemoryEquivalence

/-!
# Static instructions respect memory equivalence

Equivalent memories (same allocations, bytes, bindings and permissions, however the access
views are listed) give equivalent results for static field resolution and for the static
and span instructions.
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
    apply ResultEquivalent.bind (same.allocate _ |>.mapError _)
    intro left right related
    obtain ⟨id, memory⟩ := left
    obtain ⟨other, otherMemory⟩ := right
    obtain ⟨rfl, equivalent⟩ := related
    change memory.Equivalent otherMemory at equivalent
    apply ResultEquivalent.ok
    refine ⟨?_, rfl⟩
    refine ⟨equivalent.allocations, ?_, ?_, equivalent.nextIdentity, ?_⟩
    · simp only [equivalent.cells]
    · exact (equivalent.prependView _).permissions
    · simp only [equivalent.staticBindings]

/-- Equivalent memories give equivalent results for every static or span instruction. -/
theorem Memory.Equivalent.staticInstruction {m n : Memory} (same : m.Equivalent n)
    (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp) (stack : List Value) :
    ResultEquivalent MemoryFirstEquivalent (CIL.Safety.staticInstruction body pc operation stack m)
      (CIL.Safety.staticInstruction body pc operation stack n) := by
  unfold CIL.Safety.staticInstruction
  split <;> try simp only [checkedAt, liveAllocation, same.allocations, same.formValue]
  all_goals repeat first
    | exact same.memoryInstruction _ _
    | exact .ok ⟨same, rfl⟩
    | exact .error _
    | (apply ResultEquivalent.bind_same; intro)
    | (apply ResultEquivalent.bind (same.staticReference _)
       intro left right related
       obtain ⟨memory, reference⟩ := left
       obtain ⟨otherMemory, otherReference⟩ := right
       obtain ⟨equivalent, rfl⟩ := related
       exact .ok ⟨equivalent, rfl⟩)
    | split

#print axioms Memory.Equivalent.staticInstruction
#print axioms Memory.Equivalent.staticReference
end CIL.Safety
