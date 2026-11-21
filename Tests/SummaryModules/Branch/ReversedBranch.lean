import Extracted
import SavedArms

/-! Reuse the producer's two compiled return regions after reversing the branch before them. -/

namespace ReversedBranch
open CIL CIL.Safety SavedArms

/-- Both return regions start after the method's condition and branch. -/
private abbrev suffix (method pc : Nat) := inStarts [(0, 2)] method pc = true

/-- The new branch instruction precedes both saved return regions. -/
theorem reused (left flag : Bool) (x y : W64) :
    DecodedSegmentSummary Extracted.program Extracted.methodEvidence Extracted.profile
      Extracted.environment 0 (if left then 4 else 2) Extracted.assembly0
      Extracted.method0Original.token [] (.ldarg (if left then 1 else 2)) [.ret]
      (returnsWord flag x y (if left then x else y)) := by
  apply (SavedArms.checked left flag x y).congr_region (region := suffix)
    (DecodedAt.of_translation Extracted.translation_valid ⟨0, by decide⟩ Extracted.program_method0)
    (RegionClosed.of_check (by decide +kernel))
  · exact AgreesOn.set (program := Reference.program) (index := 0) Reference.program_method0
      Extracted.method0.code fun _ inside =>
        code_agrees_of_drop (lower := 2) rfl (by simpa [suffix, inStarts] using inside)
  · intro i _
    cases left <;> simp [suffix, inStarts] <;> omega
  · intro args before pc after _ post
    cases post

#print axioms reused

/-- The changed condition at the branch selects the input the original method would skip. -/
def branchContract (flag : Bool) (x y : W64) : SegmentContract where
  pre args s := args = arguments flag x y ∧
    s.stack = [.scalar (.i32 (if flag then 1 else 0))] ∧ s.frame.owned = []
  post _ before exit := exit = .returns before.memory [.scalar (.i64 (if flag then y else x))]

/-- The changed branch selects the other result while preserving arbitrary caller memory. -/
theorem composed (flag : Bool) (x y : W64) : (branchContract flag x y).Holds Extracted.program 0 1 := by
  let next := fun pc => if pc = 4 then returnsWord flag x y x else
    if pc = 2 then returnsWord flag x y y else SegmentContract.unreachable
  have successors : ∀ pc, (next pc).Holds Extracted.program 0 pc := by
    intro pc
    by_cases left : pc = 4
    · subst pc
      exact (reused true flag x y).holds
    by_cases right : pc = 2
    · subst pc
      exact (reused false flag x y).holds
    simpa [next, left, right] using SegmentContract.unreachable_holds Extracted.program 0 pc
  apply SegmentContract.branch_seq (pc := 1) (target := 4) (op := .brfalse 4)
    (branchContract flag x y).pre (fun _ _ => flag = false) (fun _ _ => [])
    Extracted.program_method0 (by rfl) (next := next) (rest := successors)
  · rintro args before ⟨rfl, stack, _⟩
    rw [stack]
    cases flag <;> rfl
  · exact fun _ _ h => h
  · rintro args before ⟨rfl, _, owned⟩
    cases flag <;> exact ⟨rfl, rfl, owned⟩
  · intro args before exit _ post confined
    cases flag <;> exact ⟨confined, post⟩

#print axioms composed
/-- Both compiled branch arms return the selected word and preserve all caller memory. -/
theorem invocation (memory : CIL.Safety.Memory) (flag : Bool) (x y : W64) :
    ∃ fuel, invoke Extracted.program fuel 0 (arguments flag x y) memory =
      .ok (memory, [.scalar (.i64 (if flag then y else x))]) := by
  let frame : Frame := ⟨memory.nextIdentity, [], [], 0⟩
  let before : SegmentState := ⟨frame, [.scalar (.i32 (if flag then 1 else 0))], memory⟩
  obtain ⟨exit, ran, _, post⟩ := composed flag x y (arguments flag x y) before ⟨rfl, rfl, rfl⟩
  cases post
  obtain ⟨fuel, result⟩ := ran
  refine ⟨fuel + 1, ?_⟩
  cases flag <;> exact result

#print axioms invocation

/-- The original Choose contract requires 11 on this input. Every successful run returns 22. -/
theorem rejects_original : ¬ ∃ fuel, invoke Extracted.program fuel 0 (arguments true 11 22)
    Memory.empty = .ok (Memory.empty, [.scalar (.i64 11)]) := by
  rintro ⟨fuel, original⟩
  obtain ⟨_, changed⟩ := invocation Memory.empty true 11 22
  cases invoke_ok_unique changed original

#print axioms rejects_original
end ReversedBranch
