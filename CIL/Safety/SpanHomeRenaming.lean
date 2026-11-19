import CIL.Safety.ActionRenaming
import CIL.Safety.MemoryInstructionRenaming

/-!
# Span homes under allocation renaming

A home names a slot of the frame that holds it, so renaming relocates it with the frame's
locals. Reading through a home reads the corresponding slot of the target frame, which relates
view projection, the operands of span operations and call argument checks.
-/

namespace CIL.Safety

variable {indices : LocalIndexMap} {mapping : AllocationRenaming} {scopes : Nat → Nat → Prop}
  {source target : Memory} {sourceFrame targetFrame : Frame}

/-- A span local's view lies below every limit its slot lies below. -/
theorem loadLocal_span_below {memory : Memory} {width : Nat} {writable : Bool}
    {held : Option SpanView} {limit : Nat} {result : Value}
    (bound : (LocalSlot.span width writable held).Below limit)
    (loaded : loadLocal memory (.span width writable held) = .ok result) : result.Below limit := by
  cases held with
  | none => cases loaded
  | some view =>
    simp only [loadLocal, Bind.bind, Except.bind, Pure.pure, Except.pure] at loaded
    repeat' first
      | (cases loaded <;> exact bound view rfl)
      | split at loaded

#print axioms loadLocal_span_below

/-- A home reads the corresponding slot and any other value passes as renamed; the view is
    bounded in the source. -/
theorem Frame.Renamed.spanView (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame) (value : Value)
    (bound : value.Below mapping.sourceLimit) :
    ResultRenamed mapping
      (fun left right => right = mapping.value left ∧ left.Below mapping.sourceLimit)
      (spanView sourceFrame source value)
      (spanView targetFrame target (indices.value mapping value)) := by
  cases value with
  | spanHome slot =>
    have slots := frames.locals.getElem?_all slot
    simp only [CIL.Safety.spanView, LocalIndexMap.value]
    generalize sourceFound : sourceFrame.locals[slot]? = sourceSlot at slots ⊢
    generalize targetFound : targetFrame.locals[indices.index slot]? = targetSlot at slots ⊢
    cases slots with
    | none => exact .error .invalidState
    | @some held otherHeld slots =>
      rcases slots with ⟨bounded, rfl⟩
      cases held with
      | span width writable view =>
        refine (memories.loadLocal (.span width writable view) bounded).imp ?_
        intro left right loaded same
        exact ⟨same, loadLocal_span_below bounded loaded⟩
      | _ => exact .error .invalidState
  | _ => exact .ok ⟨rfl, bound⟩
#print axioms Frame.Renamed.spanView

/-- Projecting the operands of a span operation reads corresponding slots, keeps the stack
    below them renamed and leaves every projected operand bounded. -/
theorem Frame.Renamed.viewOperands (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame) :
    ∀ (count : Nat) (stack : List Value), (∀ value ∈ stack, value.Below mapping.sourceLimit) →
    ResultRenamed mapping
      (fun left right => right = left.map (indices.value mapping) ∧
        ∀ value ∈ left, value.Below mapping.sourceLimit)
      (viewOperands sourceFrame source count stack)
      (viewOperands targetFrame target count (stack.map (indices.value mapping)))
  | 0, _, bounds => .ok ⟨rfl, bounds⟩
  | _ + 1, [], _ => .ok ⟨rfl, fun _ member => nomatch member⟩
  | count + 1, value :: rest, bounds => by
    simp only [CIL.Safety.viewOperands, List.map_cons]
    apply (frames.spanView memories value (bounds value (List.mem_cons_self ..))).bindWithSuccess
    intro first second viewed related
    obtain ⟨same, firstBound⟩ := related
    subst same
    apply (Frame.Renamed.viewOperands memories frames count rest
      (fun other member => bounds other (List.mem_cons_of_mem _ member))).bind
    intro others otherTarget related
    obtain ⟨same, otherBounds⟩ := related
    subst same
    refine .ok ⟨indices.push_of_not_home mapping others (spanView_not_spanHome viewed), ?_⟩
    intro other member
    rcases List.mem_cons.mp member with same | inner
    · subst same
      exact firstBound
    · exact otherBounds other inner
#print axioms Frame.Renamed.viewOperands

/-- A call argument reads a home's corresponding slot and checks the renamed value. -/
theorem Frame.Renamed.callArgument (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame) (value : Value)
    (bound : value.Below mapping.sourceLimit) :
    ResultRenamed mapping (fun left right => right = mapping.value left)
      (callArgument sourceFrame source value)
      (callArgument targetFrame target (indices.value mapping value)) := by
  unfold CIL.Safety.callArgument
  apply (frames.spanView memories value bound).bind
  intro viewed otherViewed related
  obtain ⟨same, viewedBound⟩ := related
  subst same
  exact memories.checkedValue viewed viewedBound
#print axioms Frame.Renamed.callArgument

/-- Checking call arguments one by one keeps them renamed and reports the first fault. -/
theorem Frame.Renamed.callArguments (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame) (values : List Value)
    (bounds : ∀ value ∈ values, value.Below mapping.sourceLimit) :
    ResultRenamed mapping (fun left right => right = left.map mapping.value)
      (values.mapM (CIL.Safety.callArgument sourceFrame source))
      ((values.map (indices.value mapping)).mapM
        (CIL.Safety.callArgument targetFrame target)) := by
  induction values with
  | nil => exact .ok rfl
  | cons value rest induction =>
    simp only [List.map_cons, List.mapM_cons]
    apply (frames.callArgument memories value (bounds value (List.mem_cons_self ..))).bind
    intro first otherFirst firstRelated
    apply (induction (fun value member => bounds value (List.mem_cons_of_mem _ member))).bind
    intro remaining otherRemaining remainingRelated
    exact .ok (by simp only [List.map_cons, firstRelated, remainingRelated])
#print axioms Frame.Renamed.callArguments

/-- Checking a frame's stack refuses a home on both sides and otherwise checks each renamed
    value, so a returned stack keeps its values renamed. -/
theorem Memory.Renamed.checkedStack (related : Memory.Renamed mapping scopes source target)
    (values : List Value) (bounds : ∀ value ∈ values, value.Below mapping.sourceLimit) :
    ResultRenamed mapping (fun left right => right = left.map mapping.value)
      (values.mapM (CIL.Safety.checkedValue source))
      ((values.map (indices.value mapping)).mapM (CIL.Safety.checkedValue target)) := by
  induction values with
  | nil => exact .ok rfl
  | cons value rest induction =>
    simp only [List.map_cons, List.mapM_cons]
    have head : ResultRenamed mapping (fun left right => right = mapping.value left)
        (CIL.Safety.checkedValue source value)
        (CIL.Safety.checkedValue target (indices.value mapping value)) := by
      cases value with
      | spanHome slot => exact .error .invalidState
      | _ => exact related.checkedValue _ (bounds _ (List.mem_cons_self ..))
    apply head.bind
    intro first otherFirst firstRelated
    apply (induction (fun value member => bounds value (List.mem_cons_of_mem _ member))).bind
    intro remaining otherRemaining remainingRelated
    exact .ok (by simp only [List.map_cons, firstRelated, remainingRelated])
#print axioms Memory.Renamed.checkedStack

/-- Initializing a span through a home stores the empty view in the corresponding slot of the
    target frame and keeps the stack below renamed. -/
theorem Frame.Renamed.initializeSpanHome (memories : Memory.Renamed mapping scopes source target)
    (frames : Frame.Renamed indices mapping scopes sourceFrame targetFrame) (pc : Nat)
    (stack : List Value) :
    ResultRenamed mapping (FrameAction.Renamed indices mapping scopes)
      (initializeSpanHome pc sourceFrame stack source)
      (initializeSpanHome pc targetFrame (stack.map (indices.value mapping)) target) := by
  cases stack with
  | nil => exact .error _
  | cons value rest =>
    cases value with
    | spanHome position =>
      simp only [CIL.Safety.initializeSpanHome, List.map_cons, LocalIndexMap.value]
      have slots := frames.locals.getElem?_all position
      generalize sourceFound : sourceFrame.locals[position]? = sourceSlot at slots ⊢
      generalize targetFound : targetFrame.locals[indices.index position]? = targetSlot at slots ⊢
      cases slots with
      | none => exact .error .invalidState
      | @some slot otherSlot slots =>
        rcases slots with ⟨bounded, rfl⟩
        cases slot with
        | span width writable view =>
          apply (memories.storeLocal (indices := indices) (.span width writable view)
            (.bufferSpan ⟨.null, 0, width, writable⟩) bounded trivial).bindWithSuccess
          intro result otherResult stored results
          obtain ⟨slotAfter, sourceAfter⟩ := result
          obtain ⟨otherSlotAfter, targetAfter⟩ := otherResult
          rcases results with ⟨slotsEqual, related⟩
          change otherSlotAfter = mapping.localSlot slotAfter at slotsEqual
          subst otherSlotAfter
          have positionBound : position < indices.sourceLength := by
            rw [← frames.locals.lengths.1]
            exact (List.getElem?_eq_some_iff.mp sourceFound).1
          exact .ok (.next related (frames.setLocal position positionBound slotAfter
            (storeLocal_below (value := .bufferSpan ⟨.null, 0, width, writable⟩) bounded trivial
              stored)))
        | _ => exact .error .invalidState
    | _ => exact .error _
#print axioms Frame.Renamed.initializeSpanHome

end CIL.Safety
