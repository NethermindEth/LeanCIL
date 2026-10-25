import CIL.Safety.RenamedMemoryBelow
import CIL.Safety.MemoryRenamingOperations
import CIL.Safety.ValueRenaming
import CIL.Safety.FrameEntryRenaming
import CIL.Safety.StackAllocationRenaming
import CIL.Safety.LocalStoreRenaming
import CIL.Safety.ValueMemoryRenaming
import CIL.Safety.RenamedConfinement

/-!
# Allocation renaming regressions

Actual checked allocations create a private target hole and then a paired home.
Caller storage stays exact, later references map around the hole, and private homes
cannot become visible when the map extends again.
-/

namespace Tests.AllocationRenaming

open CIL.Safety

/-- One caller-owned byte, with explicit read/write authority and allocation watermark one. -/
def caller : Memory := {
  allocations := fun identity => if identity = 0 then
    some ⟨.callerStack, ⟨1, 1, []⟩, true, []⟩ else none
  cells := fun _ _ => ⟨42, true⟩
  views := [⟨0, 0, 1, true, true⟩]
  nextIdentity := 1 }

/-- The test starts from allocated, well-formed caller storage. -/
theorem caller_formed : caller.WellFormed := by
  constructor
  · intro identity allocation found
    simp only [caller] at found
    split at found
    · rename_i same
      subst identity
      cases found
      exact ⟨by decide, by simp [Allocation.WellFormed, nativeLimit]⟩
    · cases found
  · intro view member
    simp only [caller, List.mem_cons, List.not_mem_nil, or_false] at member
    subst view
    exact ⟨_, rfl, by decide⟩
#print axioms caller_formed

/-- A one-byte local home carrying its frame's activation label. -/
def home (activation : Nat) : Allocation := ⟨.frame activation, ⟨1, 1, []⟩, true, []⟩

/-- The child activation may shift independently of the allocation identity map. -/
def scopes (source target : Nat) : Prop := source = target ∨ source = 1 ∧ target = 2

/-- A private home followed by paired allocation preserves the original caller byte exactly. -/
theorem private_then_paired : ∃ privateMemory sourceAfter targetAfter,
    allocate caller (home 1) = .ok (1, privateMemory) ∧
    allocate caller (home 1) = .ok (1, sourceAfter) ∧
    allocate privateMemory (home 2) = .ok (2, targetAfter) ∧
    MemoryBelow 1 caller targetAfter ∧ sourceAfter.nextIdentity = 2 ∧
    targetAfter.nextIdentity = 3 := by
  have initial := Memory.RenamedBelow.refl caller scopes
  obtain ⟨privateMemory, privateAllocated, privateRelated⟩ :=
    initial.skipTarget caller_formed (home 1) (by decide)
  have privateFormed := allocate_preserves_wellFormed caller privateMemory (home 1) 1
    caller_formed privateAllocated
  have next : privateMemory.nextIdentity = 2 := privateRelated.targetLimit.symm
  have descriptors : Allocation.Related scopes (home 1) (home 2) :=
    ⟨.frame (Or.inr ⟨rfl, rfl⟩), rfl, rfl, rfl⟩
  obtain ⟨sourceAfter, targetAfter, sourceAllocated, targetAllocated, related⟩ :=
    privateRelated.allocate caller_formed privateFormed (by simp [caller])
      (home 1) (home 2) descriptors (by decide)
  refine ⟨privateMemory, sourceAfter, targetAfter, privateAllocated, sourceAllocated, ?_, ?_,
    related.sourceLimit.symm, related.targetLimit.symm⟩
  · simpa only [next] using targetAllocated
  · exact related.confined (allocate_preserves_memory_below _ _ _ _ sourceAllocated)
#print axioms private_then_paired

/-- The later source home maps around the target-only dead home. -/
theorem later_reference :
    (((AllocationRenaming.identity 1).skipTarget).allocate).reference ⟨1, 0⟩ = ⟨2, 0⟩ := rfl
#print axioms later_reference

/-- Additional calls cannot reuse the earlier private hole as an image of a source identity. -/
theorem private_stays_hidden : ∀ identity,
    identity < (((AllocationRenaming.identity 1).skipTarget).allocate).allocate.sourceLimit →
      (((AllocationRenaming.identity 1).skipTarget).allocate).allocate.image identity ≠ 1 := by
  have first : ∀ identity, identity < (AllocationRenaming.identity 1).skipTarget.sourceLimit →
      (AllocationRenaming.identity 1).skipTarget.image identity ≠ 1 := by
    intro identity bound
    exact Nat.ne_of_lt bound
  have extension := (AllocationRenaming.identity 1).skipTarget.allocate_extends.trans
    ((AllocationRenaming.identity 1).skipTarget.allocate).allocate_extends
  exact extension.private 1 (by decide) first
#print axioms private_stays_hidden

/-- A scalar result survives an arbitrary allocation map exactly. -/
theorem scalar_result (mapping : AllocationRenaming) :
    mapping.value (.scalar (.i32 7)) = .scalar (.i32 7) := mapping.scalar _
#print axioms scalar_result

/-- The retained body declares one live numeric local. -/
def sourceBody : CIL.Method := {
  returnsValue := true
  locals := [.unmodeled]
  localKinds := [.word64]
  code := [.local 0, .ret] }

/-- Dead numeric declarations occur both before and after the retained local. -/
def targetBody : CIL.Method := {
  returnsValue := true
  locals := [.unmodeled, .unmodeled, .unmodeled]
  localKinds := [.word32, .word64, .word32]
  code := [.local 1, .ret] }

/-- The first source operand relocates past the preceding dead numeric local. -/
def indices : LocalIndexMap := .skip (.keep (.skip .nil))

/-- All entry readiness obligations follow from the concrete extracted-style metadata. -/
theorem entry_ready : UnmodeledFrame sourceBody ∧ UnmodeledFrame targetBody := by
  constructor <;> constructor <;> first
    | rfl
    | (intro kind member
       simp only [sourceBody, targetBody, List.mem_cons, List.not_mem_nil, or_false] at member
       rcases member with rfl | rfl | rfl <;> simp [localWidth, nativeLimit])
#print axioms entry_ready

/-- The actual frame allocator establishes non-trailing local and ownership correspondence. -/
theorem interleaved_frames :
    ∃ later sourceFrame targetFrame sourceAfter targetAfter,
      (AllocationRenaming.identity caller.nextIdentity).Extends later ∧
      enterFrame sourceBody [] caller = .ok (sourceFrame, sourceAfter) ∧
      enterFrame targetBody [] caller = .ok (targetFrame, targetAfter) ∧
      Memory.Renamed later (enterScopes Eq 1 1) sourceAfter targetAfter ∧
      Frame.Renamed indices later (enterScopes Eq 1 1) sourceFrame targetFrame := by
  have selected : indices.Selects Eq sourceBody.localKinds targetBody.localKinds :=
    .skip CIL.LocalKind.word32 (.keep rfl (.skip CIL.LocalKind.word32 .nil))
  exact (Memory.Renamed.refl caller Eq).enterFrameUnmodeled caller_formed caller_formed
    (by simp [caller]) entry_ready.1 entry_ready.2 indices selected [] []
#print axioms interleaved_frames

/-- Independent source execution allocates only its retained word64 home. -/
theorem source_frame_shape :
    (enterFrame sourceBody [] caller).map (fun result => (result.1.locals, result.2.nextIdentity)) =
      .ok ([.bytes .word64 ⟨1, 0⟩], 2) := rfl
#print axioms source_frame_shape

/-- Independent target execution allocates both dead homes and relocates the live home to two. -/
theorem target_frame_shape :
    (enterFrame targetBody [] caller).map (fun result => (result.1.locals, result.2.nextIdentity)) =
      .ok ([.bytes .word32 ⟨1, 0⟩, .bytes .word64 ⟨2, 0⟩, .bytes .word32 ⟨3, 0⟩], 4) := rfl
#print axioms target_frame_shape

/-- The reachable Multiply helper's extracted word64 zero remains an initialized retained home. -/
def initializedSource : CIL.Method := { sourceBody with locals := [.i64 0] }

/-- Dead numeric homes may surround the initialized helper declaration. -/
def initializedTarget : CIL.Method := {
  targetBody with locals := [.unmodeled, .i64 0, .unmodeled] }

/-- The actual word64 initializer is preserved while its allocation identity changes. -/
theorem initialized_helper_frames :
    ∃ later sourceFrame targetFrame sourceAfter targetAfter,
      (AllocationRenaming.identity caller.nextIdentity).Extends later ∧
      enterFrame initializedSource [] caller = .ok (sourceFrame, sourceAfter) ∧
      enterFrame initializedTarget [] caller = .ok (targetFrame, targetAfter) ∧
      Memory.Renamed later (enterScopes Eq 1 1) sourceAfter targetAfter ∧
      Frame.Renamed indices later (enterScopes Eq 1 1) sourceFrame targetFrame := by
  have sourceReady : OrdinaryFrame initializedSource :=
    ⟨rfl, rfl, rfl, entry_ready.1.layouts⟩
  have targetReady : OrdinaryFrame initializedTarget :=
    ⟨rfl, rfl, rfl, entry_ready.2.layouts⟩
  have selected : LocalDeclarations indices initializedSource.localKinds initializedSource.locals
      initializedTarget.localKinds initializedTarget.locals :=
    .skip .word32 .unmodeled (by simp [InitializerFits])
      (.keep .word64 (.i64 0) (.skip .word32 .unmodeled (by simp [InitializerFits]) .nil))
  have sourceEntry : ∃ frame after, enterFrame initializedSource [] caller = .ok (frame, after) :=
    ⟨_, _, rfl⟩
  obtain ⟨frame, after, entered⟩ := sourceEntry
  exact (Memory.Renamed.refl caller Eq).enterFrameInitialized caller_formed caller_formed
    (by simp [caller]) sourceReady targetReady indices selected [] [] entered
#print axioms initialized_helper_frames

/-- Keeping the old operand would address a dead word32 declaration, so it is rejected. -/
theorem old_operand_rejected : indices.index 0 ≠ 0 := by decide
#print axioms old_operand_rejected

/-- Empty source activations can share a label while target dead homes separate those labels. -/
theorem distinct_target_activations :
    enterScopes (enterScopes Eq 1 1) 1 2 1 1 ∧
    enterScopes (enterScopes Eq 1 1) 1 2 1 2 :=
  ⟨enterScopes_existing _ _ _ _ _ (enterScopes_new _ _ _), enterScopes_new _ _ _⟩
#print axioms distinct_target_activations

end Tests.AllocationRenaming
