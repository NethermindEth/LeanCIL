import Reference
import CIL.Safety.DecodedSegment

/-! Separate contracts for the two load-and-return regions of the compiled Choose method. -/

namespace SavedArms
open CIL CIL.Safety

/-- The three arguments in the compiled method's Boolean and word representations. -/
def arguments (flag : Bool) (x y : W64) : List CIL.Safety.Value :=
  [.scalar (.i32 (if flag then 1 else 0)), .scalar (.i64 x), .scalar (.i64 y)]

/-- A return arm consumes an empty stack and leaves the caller's memory intact. -/
def returnsWord (flag : Bool) (x y result : W64) : SegmentContract where
  pre args state := args = arguments flag x y ∧ state.stack = [] ∧ state.frame.owned = []
  post _ before exit := exit = .returns before.memory [.scalar (.i64 result)]

/-- Each arm binds its two instructions and its result to the producer's method evidence. -/
theorem checked (left flag : Bool) (x y : W64) :
    DecodedSegmentSummary Reference.program Reference.methodEvidence Reference.profile
      Reference.environment 0 (if left then 4 else 2) Reference.assembly0
      Reference.method0Original.token [] (.ldarg (if left then 1 else 2)) [.ret]
      (returnsWord flag x y (if left then x else y)) := by
  refine ⟨DecodedAt.of_translation Reference.translation_valid ⟨0, by decide⟩
    Reference.program_method0, ⟨Reference.method0, Reference.program_method0, ?_⟩, ?_⟩
  · cases left <;> rfl
  · rintro args ⟨frame, stack, memory⟩ ⟨rfl, rfl, owned⟩
    refine ⟨.returns memory [.scalar (.i64 (if left then x else y))], ⟨2, ?_⟩,
      Confined.refl [] memory, rfl⟩
    change frame.owned = [] at owned
    cases left <;>
      change Except.ok (leaveFrame frame memory, _) = Except.ok (memory, _) <;>
      simp [leaveFrame, owned]

#print axioms checked
end SavedArms
