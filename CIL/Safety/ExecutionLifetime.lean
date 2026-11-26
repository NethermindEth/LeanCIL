import CIL.Safety.ExecutionAllocations
import CIL.Safety.ExecutionPrefixes

/-!
# Callees cannot expire caller storage

A call may allocate and expire its own homes, but every allocation below the caller's
watermark keeps exactly its lifetime and layout (`AllocationsBelow`). This holds across a
successful run, a whole invocation, and every observed memory of a run that later faults
(`runVisits_preserves_caller_allocations`), so a caller's references stay formable.
-/

namespace CIL.Safety

/-- Calls may expire their own homes. Only identities below the caller's
    allocation watermark must retain exactly the same lifetime and layout. -/
structure AllocationsBelow (before after : Memory) (watermark : Nat) : Prop where
  next : before.nextIdentity ≤ after.nextIdentity
  lookup : ∀ id, id < watermark → after.allocations id = before.allocations id

theorem AllocationExtension.below {before after : Memory} (ext : AllocationExtension before after)
    (watermark : Nat) (bound : watermark ≤ before.nextIdentity) :
    AllocationsBelow before after watermark :=
  ⟨ext.next, fun id old => ext.lookup id (Nat.lt_of_lt_of_le old bound)⟩

theorem AllocationsBelow.trans {first middle last : Memory} {watermark : Nat}
    (left : AllocationsBelow first middle watermark)
    (right : AllocationsBelow middle last watermark) :
    AllocationsBelow first last watermark := by
  refine ⟨Nat.le_trans left.next right.next, ?_⟩
  intro id bound
  rw [right.lookup id bound, left.lookup id bound]

theorem AllocationsBelow.preserves_reference {m result : Memory} {watermark : Nat}
    (ext : AllocationsBelow m result watermark) (r formed : Reference)
    (old : r.allocation < watermark) (h : form m r = .ok formed) :
    form result r = .ok formed := by
  rw [form_allocation_congr _ _ _ (ext.lookup r.allocation old)]
  exact h

theorem programStep_extends_allocations {program : CIL.Program} {method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (h : ProgramStep program method pc args frame stack m action) :
    AllocationExtension m action.memory := by
  obtain ⟨body, op, _, _, h⟩ := h
  exact step_extends_allocations _ _ _ _ _ _ _ _ h

theorem programStep_ownedAbove {program : CIL.Program} {method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    {watermark : Nat} (h : ProgramStep program method pc args frame stack m action)
    (bound : watermark ≤ m.nextIdentity) (owned : frame.OwnedAbove watermark) :
    action.OwnedAbove watermark := by
  obtain ⟨body, op, _, _, h⟩ := h
  exact step_ownedAbove _ _ _ _ _ _ _ _ _ owned bound h


/-- Leaving a frame that owns only allocations at or above `watermark` keeps every allocation
    below it. -/
theorem AllocationsBelow.leaveFrame {frame : Frame} {memory : Memory} {watermark : Nat}
    (owned : frame.OwnedAbove watermark) :
    AllocationsBelow memory (CIL.Safety.leaveFrame frame memory) watermark :=
  ⟨by rw [leaveFrame_nextIdentity]; exact Nat.le_refl _,
    fun id old => leaveFrame_preserves_older_allocations _ _ _ owned id old⟩

/-- A run whose frame owns only allocations at or above `watermark`, through caught faults and
    calls, keeps every allocation below it in the memory it ends in or a fault leaves. -/
theorem OutcomeTrace.callerAllocations {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {memory : Memory}
    {outcome : Except FaultState (Memory × List Value)}
    (trace : OutcomeTrace program fuel method pc args frame stack memory outcome)
    (watermark : Nat) (bound : watermark ≤ memory.nextIdentity)
    (owned : frame.OwnedAbove watermark) :
    OutcomeHolds (fun after => AllocationsBelow memory after watermark) outcome := by
  induction trace with
  | exhausted | missing =>
    exact ⟨(AllocationExtension.refl _).below watermark bound, .leaveFrame owned⟩
  | faulted _ _ _ recovered =>
    have here := (AllocationExtension.refl _).below watermark bound
    rcases recover_error_state recovered with rfl | ⟨same, unwound⟩
    · exact ⟨here, .leaveFrame owned⟩
    · exact ⟨same ▸ here, unwound ▸ .leaveFrame owned⟩
  | caught _ _ _ recovered _ ih =>
    have kept := recover_ok_frame recovered
    exact ih bound (by simpa [Frame.OwnedAbove, kept.2.2.1] using owned)
  | next _ _ stepped _ ih =>
    have first := step_extends_allocations _ _ _ _ _ _ _ _ stepped
    have later := ih (Nat.le_trans bound first.next)
      (step_ownedAbove _ _ _ _ _ _ _ _ _ owned bound stepped)
    exact OutcomeHolds.mono (fun _ below => (first.below watermark bound).trans below) later
  | raised _ _ stepped recovered =>
    have first := (step_extends_allocations _ _ _ _ _ _ _ _ stepped).below watermark bound
    have raisedOwned := step_ownedAbove _ _ _ _ _ _ _ _ _ owned bound stepped
    rcases recover_error_state recovered with rfl | ⟨same, unwound⟩
    · exact ⟨first, first.trans (.leaveFrame raisedOwned)⟩
    · exact ⟨same ▸ first, unwound ▸ first.trans (.leaveFrame raisedOwned)⟩
  | raiseCaught _ _ stepped recovered _ ih =>
    have first := step_extends_allocations _ _ _ _ _ _ _ _ stepped
    have raisedOwned := step_ownedAbove _ _ _ _ _ _ _ _ _ owned bound stepped
    have kept := recover_ok_frame recovered
    exact OutcomeHolds.mono (fun _ below => (first.below watermark bound).trans below)
      (ih (Nat.le_trans bound first.next)
        (by simpa [FrameAction.OwnedAbove, Frame.OwnedAbove, kept.2.2.1] using raisedOwned))
  | callMissing _ _ stepped | callUnentered _ _ stepped | tailMissing _ _ stepped
  | tailMismatched _ _ stepped =>
    have first := (step_extends_allocations _ _ _ _ _ _ _ _ stepped).below watermark bound
    exact ⟨first, first.trans (.leaveFrame owned)⟩
  | constructMissing _ _ stepped | constructUnentered _ _ stepped =>
    have first := (step_extends_allocations _ _ _ _ _ _ _ _ stepped).below watermark bound
    have nextOwned := step_ownedAbove _ _ _ _ _ _ _ _ _ owned bound stepped
    exact ⟨first, first.trans (.leaveFrame nextOwned)⟩
  | tailUnchecked _ _ stepped | tailUnentered _ _ stepped | returnUnchecked _ _ stepped =>
    have retired := ((step_extends_allocations _ _ _ _ _ _ _ _ stepped).below watermark
      bound).trans (.leaveFrame owned)
    exact ⟨retired, retired⟩
  | returned _ _ stepped =>
    exact ((step_extends_allocations _ _ _ _ _ _ _ _ stepped).below watermark bound).trans
      (.leaveFrame owned)
  | tailed _ _ stepped _ _ _ enter _ ih =>
    have retired := ((step_extends_allocations _ _ _ _ _ _ _ _ stepped).below watermark
      bound).trans (.leaveFrame owned)
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have retiredBound := Nat.le_trans bound retired.next
    exact OutcomeHolds.mono
      (fun _ below => (retired.trans (fresh.1.below watermark retiredBound)).trans below)
      (ih (Nat.le_trans retiredBound fresh.1.next)
        (fun id member => Nat.le_trans retiredBound (fresh.2 id member).1))
  | called _ _ stepped _ enter _ _ childIH ih
  | constructed _ _ stepped _ enter _ _ _ childIH ih =>
    have first := step_extends_allocations _ _ _ _ _ _ _ _ stepped
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have setup := first.trans fresh.1
    have child := childIH (Nat.le_trans bound setup.next)
      (fun id member => Nat.le_trans (Nat.le_trans bound first.next) (fresh.2 id member).1)
    have prior := (setup.below watermark bound).trans child
    exact OutcomeHolds.mono (fun _ below => prior.trans below)
      (ih (Nat.le_trans bound prior.next)
        (by first | exact owned | exact step_ownedAbove _ _ _ _ _ _ _ _ _ owned bound stepped))
  | constructValued _ _ stepped _ enter _ _ childIH
  | constructUnloaded _ _ stepped _ enter _ _ childIH =>
    have first := step_extends_allocations _ _ _ _ _ _ _ _ stepped
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have setup := first.trans fresh.1
    have child := childIH (Nat.le_trans bound setup.next)
      (fun id member => Nat.le_trans (Nat.le_trans bound first.next) (fresh.2 id member).1)
    have prior := (setup.below watermark bound).trans child
    exact ⟨prior, prior.trans
      (.leaveFrame (step_ownedAbove _ _ _ _ _ _ _ _ _ owned bound stepped))⟩
  | callFaulted _ _ stepped _ enter _ recovered childIH =>
    have first := step_extends_allocations _ _ _ _ _ _ _ _ stepped
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have setup := first.trans fresh.1
    have child := childIH (Nat.le_trans bound setup.next)
      (fun id member => Nat.le_trans (Nat.le_trans bound first.next) (fresh.2 id member).1)
    have unwound := ((setup.below watermark bound).trans child.2).trans
      (.leaveFrame owned)
    rcases recover_error_state recovered with rfl | ⟨same, after⟩
    · exact ⟨(setup.below watermark bound).trans child.1, unwound⟩
    · exact ⟨same ▸ (setup.below watermark bound).trans child.2, after ▸ unwound⟩
  | constructFaulted _ _ stepped _ enter _ recovered childIH =>
    have first := step_extends_allocations _ _ _ _ _ _ _ _ stepped
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have setup := first.trans fresh.1
    have child := childIH (Nat.le_trans bound setup.next)
      (fun id member => Nat.le_trans (Nat.le_trans bound first.next) (fresh.2 id member).1)
    have unwound := ((setup.below watermark bound).trans child.2).trans
      (.leaveFrame (step_ownedAbove _ _ _ _ _ _ _ _ _ owned bound stepped))
    rcases recover_error_state recovered with rfl | ⟨same, after⟩
    · exact ⟨(setup.below watermark bound).trans child.1, unwound⟩
    · exact ⟨same ▸ (setup.below watermark bound).trans child.2, after ▸ unwound⟩
  | callCaught _ _ stepped _ enter _ recovered _ childIH ih =>
    have first := step_extends_allocations _ _ _ _ _ _ _ _ stepped
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have setup := first.trans fresh.1
    have child := childIH (Nat.le_trans bound setup.next)
      (fun id member => Nat.le_trans (Nat.le_trans bound first.next) (fresh.2 id member).1)
    have prior := (setup.below watermark bound).trans child.2
    have kept := recover_ok_frame recovered
    exact OutcomeHolds.mono (fun _ below => prior.trans below)
      (ih (Nat.le_trans bound prior.next)
        (by simpa [FrameAction.OwnedAbove, Frame.OwnedAbove, kept.2.2.1] using owned))
  | constructCaught _ _ stepped _ enter _ recovered _ childIH ih =>
    have first := step_extends_allocations _ _ _ _ _ _ _ _ stepped
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have setup := first.trans fresh.1
    have child := childIH (Nat.le_trans bound setup.next)
      (fun id member => Nat.le_trans (Nat.le_trans bound first.next) (fresh.2 id member).1)
    have prior := (setup.below watermark bound).trans child.2
    have kept := recover_ok_frame recovered
    exact OutcomeHolds.mono (fun _ below => prior.trans below)
      (ih (Nat.le_trans bound prior.next)
        (by
          simpa [FrameAction.OwnedAbove, Frame.OwnedAbove, kept.2.2.1] using
            (step_ownedAbove _ _ _ _ _ _ _ _ _ owned bound stepped)))
#print axioms OutcomeTrace.callerAllocations

/-- A successful run whose frame owns only allocations at or above `watermark` leaves every
    allocation below it unchanged. -/
theorem run_preserves_caller_allocations (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory)
    (values : List Value) (watermark : Nat) (bound : watermark ≤ m.nextIdentity)
    (owned : frame.OwnedAbove watermark)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    AllocationsBelow m final watermark := by
  exact (run_ok_trace h).callerAllocations watermark bound owned

/-- A run entered from `memory` keeps every allocation `memory` had, in the memory it ends in and
    in both memories a fault leaves. -/
theorem OutcomeTrace.enteredExtends {program : CIL.Program} {fuel method : Nat}
    {body : CIL.Method} {args : List Value} {frame : Frame} {memory entered : Memory}
    {outcome : Except FaultState (Memory × List Value)}
    (trace : OutcomeTrace program fuel method 0 args frame [] entered outcome)
    (setup : enterFrame body args memory = .ok (frame, entered)) :
    OutcomeHolds (AllocationExtension memory) outcome := by
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  exact (trace.callerAllocations memory.nextIdentity fresh.1.next
    (fun id member => (fresh.2 id member).1)).mono fun _ preserved =>
      ⟨Nat.le_trans fresh.1.next preserved.next,
        fun id old => (preserved.lookup id old).trans (fresh.1.lookup id old)⟩

#print axioms OutcomeTrace.enteredExtends

/-- A child may mutate caller bytes, but cannot expire or replace caller storage. -/
theorem entered_run_preserves_caller_allocations (program : CIL.Program) (fuel method : Nat)
    (body : CIL.Method) (args values : List Value) (frame : Frame) (m entered final : Memory)
    (setup : enterFrame body args m = .ok (frame, entered))
    (finish : run program fuel method 0 args frame [] entered = .ok (final, values)) :
    AllocationExtension m final := by
  exact (run_ok_trace finish).enteredExtends setup

theorem invoke_preserves_caller_allocations (program : CIL.Program) (fuel method : Nat)
    (args values : List Value) (m final : Memory)
    (h : invoke program fuel method args m = .ok (final, values)) :
    AllocationExtension m final := by
  obtain ⟨_, _, _, _, _, _, setup, executed⟩ := invoke_success_setup h
  exact entered_run_preserves_caller_allocations _ _ _ _ _ _ _ _ _ _ setup executed

/-- A successful call's `MemoryBelow` postcondition composes with anything that keeps the memory
    below the call's final watermark, such as a second call's postcondition. -/
theorem MemoryBelow.compose_invoke {program : CIL.Program} {fuel method : Nat}
    {args values : List Value} {memory middle last : Memory}
    (called : invoke program fuel method args memory = .ok (middle, values))
    (left : MemoryBelow memory.nextIdentity memory middle)
    (right : MemoryBelow middle.nextIdentity middle last) :
    MemoryBelow memory.nextIdentity memory last :=
  left.compose right (invoke_preserves_caller_allocations _ _ _ _ _ _ _ called).next

#print axioms MemoryBelow.compose_invoke

theorem invoke_preserves_caller_reference (program : CIL.Program) (fuel method : Nat)
    (args values : List Value) (m final : Memory) (r formed : Reference) (hm : m.WellFormed)
    (valid : form m r = .ok formed)
    (h : invoke program fuel method args m = .ok (final, values)) :
    form final r = .ok formed :=
  (invoke_preserves_caller_allocations _ _ _ _ _ _ _ h).preserves_reference hm r formed valid

/-- Caller lifetimes are preserved even at prefixes of runs which later fault.
    Each observation uses actual fetched steps and actual nested execution. -/
theorem runVisits_preserves_caller_allocations {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m observed : Memory}
    (visit : RunVisits program fuel method pc args frame stack m observed)
    (watermark : Nat) (bound : watermark ≤ m.nextIdentity) (owned : frame.OwnedAbove watermark) :
    AllocationsBelow m observed watermark := by
  induction visit with
  | initial => exact (AllocationExtension.refl _).below watermark bound
  | tailExpired step _ _ _ =>
    have first := (programStep_extends_allocations step).below watermark bound
    exact first.trans ⟨by rw [leaveFrame_nextIdentity]; exact Nat.le_refl _,
      fun id old => leaveFrame_preserves_older_allocations _ _ _ owned id old⟩
  | tailChild step _ _ _ _ enter _ ih =>
    have first := (programStep_extends_allocations step).below watermark bound
    have retired := first.trans
      (show AllocationsBelow _ _ watermark from
        ⟨by rw [leaveFrame_nextIdentity]; exact Nat.le_refl _,
          fun id old => leaveFrame_preserves_older_allocations _ _ _ owned id old⟩)
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have retiredBound := Nat.le_trans bound retired.next
    exact (retired.trans (fresh.1.below watermark retiredBound)).trans
      (ih (Nat.le_trans retiredBound fresh.1.next)
        (fun id member => Nat.le_trans retiredBound (fresh.2 id member).1))
  | stepped step => exact (programStep_extends_allocations step).below watermark bound
  | next step later ih =>
    have first := programStep_extends_allocations step
    exact (first.below watermark bound).trans
      (ih (Nat.le_trans bound first.next) (programStep_ownedAbove step bound owned))
  | entered step call lookup enter =>
    have first := programStep_extends_allocations step
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    exact (first.trans fresh.1).below watermark bound
  | child step call lookup enter later ih =>
    have first := programStep_extends_allocations step
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have prior := first.trans fresh.1
    exact (prior.below watermark bound).trans
      (ih (Nat.le_trans bound prior.next)
        (fun id member => Nat.le_trans (Nat.le_trans bound first.next) (fresh.2 id member).1))
  | callContinue step lookup enter finish later ih =>
    have first := programStep_extends_allocations step
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have setup := first.trans fresh.1
    have child := run_preserves_caller_allocations _ _ _ _ _ _ _ _ _ _ watermark
      (Nat.le_trans bound setup.next)
      (fun id member => Nat.le_trans (Nat.le_trans bound first.next) (fresh.2 id member).1) finish
    have prior := (setup.below watermark bound).trans child
    exact prior.trans (ih (Nat.le_trans bound prior.next) owned)
  | constructContinue step lookup enter finish load later ih =>
    have first := programStep_extends_allocations step
    have fresh := enterFrame_fresh _ _ _ _ _ enter
    have setup := first.trans fresh.1
    have child := run_preserves_caller_allocations _ _ _ _ _ _ _ _ _ _ watermark
      (Nat.le_trans bound setup.next)
      (fun id member => Nat.le_trans (Nat.le_trans bound first.next) (fresh.2 id member).1) finish
    have prior := (setup.below watermark bound).trans child
    exact prior.trans (ih (Nat.le_trans bound prior.next) (programStep_ownedAbove step bound owned))
  | expired step =>
    have first := (programStep_extends_allocations step).below watermark bound
    exact first.trans ⟨by rw [leaveFrame_nextIdentity]; exact Nat.le_refl _,
      fun id old => leaveFrame_preserves_older_allocations _ _ _ owned id old⟩

theorem runVisits_preserves_caller_reference {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m observed : Memory}
    (visit : RunVisits program fuel method pc args frame stack m observed)
    (watermark : Nat) (bound : watermark ≤ m.nextIdentity) (owned : frame.OwnedAbove watermark)
    (r formed : Reference) (old : r.allocation < watermark) (valid : form m r = .ok formed) :
    form observed r = .ok formed :=
  (runVisits_preserves_caller_allocations visit watermark bound owned).preserves_reference
    r formed old valid

#print axioms run_preserves_caller_allocations
#print axioms invoke_preserves_caller_allocations
#print axioms invoke_preserves_caller_reference
#print axioms runVisits_preserves_caller_allocations
#print axioms runVisits_preserves_caller_reference

end CIL.Safety
