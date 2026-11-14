import CIL.Safety.FrameRenaming
import CIL.Safety.Execution
import CIL.Safety.ResultRenaming

/-!
# Relocated local operands

Only instructions that address local slots change their operand. Program counters, argument
indices, arithmetic operations and static sites retain their original meaning.
-/

namespace CIL.Safety

/-- Relocate each local load, address or store through the retained declaration map. -/
def LocalIndexMap.operation (indices : LocalIndexMap) : CIL.Instruction → CIL.Instruction
  | .ldloc position => .ldloc (indices.index position)
  | .ldloca position => .ldloca (indices.index position)
  | .stloc position => .stloc (indices.index position)
  | .initializeSpanLocal position constructor =>
    .initializeSpanLocal (indices.index position) constructor
  | operation => operation

/-- Relocation leaves every instruction's unspecified-operand guard unchanged. -/
theorem LocalIndexMap.operation_observers (indices : LocalIndexMap) (operation : CIL.Instruction) :
    observerCount (indices.operation operation) = observerCount operation := by
  cases operation <;> rfl
#print axioms LocalIndexMap.operation_observers

/-- Local operands never enter the pure arithmetic fallback, whose arity remains exact. -/
theorem LocalIndexMap.operation_pureArity (indices : LocalIndexMap) (operation : CIL.Instruction) :
    pureArity (indices.operation operation) = pureArity operation := by
  cases operation <;> rfl
#print axioms LocalIndexMap.operation_pureArity

/-- A successful local lookup identifies a bounded source operand and its mapped target slot. -/
theorem Frame.Renamed.localFound {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Frame}
    (related : Frame.Renamed indices mapping scopes source target)
    {position : Nat} {slot : LocalSlot} (found : source.locals[position]? = some slot) :
    position < indices.sourceLength ∧ slot.Below mapping.sourceLimit ∧
      target.locals[indices.index position]? = some (mapping.localSlot slot) := by
  have bound : position < indices.sourceLength := by
    rw [← related.locals.lengths.1]
    exact (List.getElem?_eq_some_iff.mp found).1
  have selected := related.locals.getElem? position bound
  rw [found] at selected
  generalize targetFound : target.locals[indices.index position]? = targetSlot at selected ⊢
  cases selected with
  | some slots =>
    exact ⟨bound, slots.1, congrArg some slots.2⟩
#print axioms Frame.Renamed.localFound

/-- Local lookup preserves missing-slot rejection as well as corresponding retained slots. -/
theorem Frame.Renamed.localLookup {indices : LocalIndexMap} {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Frame}
    (related : Frame.Renamed indices mapping scopes source target) (position : Nat) :
    ResultRenamed mapping (LocalSlot.Renamed mapping)
      (match source.locals[position]? with
        | some slot => .ok slot
        | none => .error .invalidState)
      (match target.locals[indices.index position]? with
        | some slot => .ok slot
        | none => .error .invalidState) := by
  have slots := related.locals.getElem?_all position
  generalize sourceFound : source.locals[position]? = sourceSlot at slots ⊢
  generalize targetFound : target.locals[indices.index position]? = targetSlot at slots ⊢
  cases slots with
  | none => exact .error .invalidState
  | some slots => exact .ok slots
#print axioms Frame.Renamed.localLookup

end CIL.Safety
