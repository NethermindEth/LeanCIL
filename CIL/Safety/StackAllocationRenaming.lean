import CIL.Safety.FrameRenaming
import CIL.Safety.ResultRenaming
import CIL.Safety.StackAllocation

/-!
# Dynamic stack allocation under renaming

Successful dynamic allocations extend the allocation correspondence, preserve the
per-activation quota and initialization mode, and add corresponding frame ownership.
-/

namespace CIL.Safety

/-- Successful stack allocation preserves its exact quota checks and mapped ownership. -/
theorem Memory.Renamed.allocateStack {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target sourceAfter : Memory}
    {indices : LocalIndexMap} {sourceFrame targetFrame sourceFinal : Frame}
    (related : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    (size : Nat) (initLocals : Bool) (reference : ManagedReference)
    (allocated : allocateStack source sourceFrame size initLocals =
      .ok (reference, sourceFinal, sourceAfter)) :
    ∃ later targetReference targetFinal targetAfter,
      mapping.Extends later ∧
      allocateStack target targetFrame size initLocals =
        .ok (targetReference, targetFinal, targetAfter) ∧
      targetReference = later.managedReference reference ∧
      Frame.Renamed indices later scopes sourceFinal targetFinal ∧
      Memory.Renamed later scopes sourceAfter targetAfter := by
  by_cases malformed : (size ≥ nativeLimit || source.stackLimit > maxDynamicStack) = true
  · simp [CIL.Safety.allocateStack, malformed, Bind.bind, Except.bind] at allocated
  have bounded : size < nativeLimit := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at malformed
    exact Nat.lt_of_not_ge malformed.1
  by_cases zero : (size == 0) = true
  · simp only [CIL.Safety.allocateStack, malformed, Bool.false_eq_true, ite_false, zero, ite_true,
      Bind.bind, Except.bind, Pure.pure, Except.pure] at allocated
    cases allocated
    refine ⟨mapping, .null, targetFrame, target, .refl mapping, ?_, rfl, frames, related⟩
    simp only [CIL.Safety.allocateStack, related.stackLimit, malformed,
      Bool.false_eq_true, ite_false, zero,
      ite_true, Bind.bind, Except.bind, Pure.pure, Except.pure]
  by_cases exhausted : (sourceFrame.stackBytes > source.stackLimit ||
      stackReservation size > source.stackLimit - sourceFrame.stackBytes) = true
  · simp [CIL.Safety.allocateStack, malformed, zero, exhausted, Bind.bind, Except.bind] at allocated
  obtain ⟨sourceHome, targetHome, sourceMade, targetMade, homes⟩ :=
    related.allocateHome sourceFormed targetFormed staticBounds sourceFrame.activation
      targetFrame.activation size stackAlignment frames.activation bounded (by decide)
  have freshBound : source.nextIdentity < mapping.allocate.sourceLimit := by
    change source.nextIdentity < mapping.sourceLimit + 1
    rw [related.sourceLimit]
    exact Nat.lt_succ_self _
  have freshImage : mapping.allocate.image source.nextIdentity = target.nextIdentity := by
    rw [← related.sourceLimit, mapping.allocate_fresh, related.targetLimit]
  have grownFrames := frames.extend mapping.allocate_extends (fun _ _ scope => scope)
  have finalFrames := grownFrames.addOwned source.nextIdentity freshBound (stackReservation size)
  simp only [freshImage] at finalFrames
  cases initLocals with
  | false =>
    simp only [CIL.Safety.allocateStack, malformed, zero, exhausted, sourceMade,
      Bool.false_eq_true, ite_false, Bind.bind, Except.bind, Pure.pure, Except.pure] at allocated
    cases allocated
    refine ⟨mapping.allocate, .address ⟨target.nextIdentity, 0⟩, _, targetHome,
      mapping.allocate_extends, ?_, ?_, finalFrames, homes⟩
    · simp only [CIL.Safety.allocateStack, related.stackLimit, frames.stackBytes,
        malformed, zero, exhausted, targetMade, Bool.false_eq_true, ite_false, Bool.false_eq_true,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp only [AllocationRenaming.managedReference, AllocationRenaming.reference, freshImage]
  | true =>
    simp only [CIL.Safety.allocateStack, malformed, zero, exhausted, sourceMade,
      Bool.false_eq_true, ite_false, ite_true, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at allocated
    cases sourceWritten : CIL.Safety.write sourceHome ⟨source.nextIdentity, 0⟩
        (List.replicate size 0) stackAlignment with
    | error fault =>
      simp only [checkedAt, sourceWritten, Except.mapError, Bind.bind, Except.bind] at allocated
      cases allocated
    | ok stored =>
      simp only [checkedAt, sourceWritten, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at allocated
      cases allocated
      have writes := homes.write ⟨source.nextIdentity, 0⟩ freshBound
        (List.replicate size 0) stackAlignment
      rw [sourceWritten] at writes
      obtain ⟨targetStored, targetWritten, memories⟩ := writes.success
      simp only [AllocationRenaming.reference, freshImage] at targetWritten
      refine ⟨mapping.allocate, .address ⟨target.nextIdentity, 0⟩, _, targetStored,
        mapping.allocate_extends, ?_, ?_, finalFrames, memories⟩
      · simp only [CIL.Safety.allocateStack, related.stackLimit, frames.stackBytes,
          malformed, zero, exhausted, targetMade, targetWritten,
          Bool.false_eq_true, ite_false, ite_true,
          checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · simp only [AllocationRenaming.managedReference, AllocationRenaming.reference, freshImage]
#print axioms Memory.Renamed.allocateStack

end CIL.Safety
