import CIL.Safety.Segment
import CIL.Safety.LocalSnapshots

/-!
# Framing remembered locals across placed segments

The placed code identifies direct local stores. `SegmentLocalEffects` records actual checked
writes to those homes. The frame rule combines these effects with distinct writable homes to
retain every untouched numeric local, without reproving a disjoint read for each local.
Indirect writes and aliased homes cannot be justified by placement alone.
-/

namespace CIL.Safety

/-- Direct local destinations named by a code segment, including vector local stores. -/
def segmentStores (code : List CIL.Op) : List Nat := code.filterMap fun operation =>
  match operation with
  | .setLocal index _ | .setVectorLocal index | .initializeSpanLocal index _ => some index
  | _ => none

/-- The remembered values of locals outside a segment's direct-store set. -/
def untouchedLocals (code : List CIL.Op) (known : Nat → Option CIL.Value) :
    Nat → Option CIL.Value := fun index =>
  if index ∈ segmentStores code then none else known index

/-- A memory effect consists of actual successful writes to local homes named by the code.
    Slot identities stay fixed. Merely omitting an indirect write from the code is not evidence
    for this relation: every memory transition requires its checked write equation. -/
inductive SegmentLocalEffects (code : List CIL.Op) (slots : List LocalSlot) :
    Memory → Memory → Prop where
  | refl (memory) : SegmentLocalEffects code slots memory memory
  | store {before after} (index : Nat) (kind : CIL.LocalKind) (home : Reference)
      (bytes : List (BitVec 8)) (alignment : Nat)
      (destination : index ∈ segmentStores code)
      (slot : slots[index]? = some (.bytes kind home))
      (written : write before home bytes alignment = .ok after) :
      SegmentLocalEffects code slots before after
  | trans {before middle after}
      (first : SegmentLocalEffects code slots before middle)
      (second : SegmentLocalEffects code slots middle after) :
      SegmentLocalEffects code slots before after

/-- An effect remains valid when the containing placed region permits more destinations. -/
theorem SegmentLocalEffects.mono {small large : List CIL.Op} {slots : List LocalSlot}
    {before after : Memory} (effects : SegmentLocalEffects small slots before after)
    (included : ∀ index ∈ segmentStores small, index ∈ segmentStores large) :
    SegmentLocalEffects large slots before after := by
  induction effects with
  | refl memory => exact .refl memory
  | store index kind home bytes alignment destination slot written =>
    exact .store index kind home bytes alignment (included index destination) slot written
  | trans _ _ first second => exact first.trans second

#print axioms SegmentLocalEffects.mono

/-- Adjacent placed regions combine their checked memory effects. -/
theorem SegmentLocalEffects.append {left right : List CIL.Op} {slots : List LocalSlot}
    {before middle after : Memory}
    (first : SegmentLocalEffects left slots before middle)
    (second : SegmentLocalEffects right slots middle after) :
    SegmentLocalEffects (left ++ right) slots before after :=
  (first.mono (by
    intro index member
    simp only [segmentStores, List.filterMap_append, List.mem_append] at *
    exact Or.inl member)).trans (second.mono (by
      intro index member
      simp only [segmentStores, List.filterMap_append, List.mem_append] at *
      exact Or.inr member))

#print axioms SegmentLocalEffects.append
/-- A checked local-write effect preserves every remembered value outside the placed stores.
    Distinct writable homes rule out aliasing between the stored and retained locals. -/
theorem SegmentLocalEffects.frame {code : List CIL.Op} {slots : List LocalSlot}
    {before after entered : Memory} {boundary : Nat} {kinds : List CIL.LocalKind}
    {known : Nat → Option CIL.Value}
    (effects : SegmentLocalEffects code slots before after)
    (homes : WritableHomes entered boundary kinds slots)
    (snapshots : LocalSnapshots before slots (untouchedLocals code known)) :
    LocalSnapshots after slots (untouchedLocals code known) := by
  induction effects with
  | refl => exact snapshots
  | store index kind home bytes alignment destination slot written =>
    apply snapshots.after_write_apart written
    intro other value otherKind otherHome specified otherSlot
    have outside : other ∉ segmentStores code := by
      intro stored
      simp [untouchedLocals, stored] at specified
    have different : other ≠ index := fun same => outside (same ▸ destination)
    exact Or.inl (homes.distinct other index otherKind kind otherHome home different otherSlot slot)
  | trans first second firstIH secondIH => exact secondIH (firstIH snapshots)

#print axioms SegmentLocalEffects.frame

/-- Forgetting destinations from a snapshot map preserves all other snapshot evidence. -/
theorem LocalSnapshots.untouched {code : List CIL.Op} {memory : Memory}
    {slots : List LocalSlot} {known : Nat → Option CIL.Value}
    (snapshots : LocalSnapshots memory slots known) :
    LocalSnapshots memory slots (untouchedLocals code known) := by
  intro index value specified
  by_cases stored : index ∈ segmentStores code
  · simp [untouchedLocals, stored] at specified
  · exact snapshots index value (by simpa [untouchedLocals, stored] using specified)

#print axioms LocalSnapshots.untouched

/-- Actual writes, writable-home separation and a placement derive the untouched local values
    at a segment boundary. No final snapshot or per-local disjointness proof is required. -/
theorem SegmentRun.frameLocals {program : CIL.Program} {method start finish cost : Nat}
    {arguments : List Value} {before after : SegmentState} {body : CIL.Method}
    {code : List CIL.Op} {entered : Memory} {boundary : Nat} {kinds : List CIL.LocalKind}
    {known : Nat → Option CIL.Value}
    (execution : SegmentRun program method start finish cost arguments before after)
    (_found : program[method]? = some body)
    (_placed : CodeAt body start code) (_finish : finish = start + code.length)
    (homes : WritableHomes entered boundary kinds before.frame.locals)
    (snapshots : LocalSnapshots before.memory before.frame.locals known)
    (slots : after.frame.locals = before.frame.locals)
    (effects : SegmentLocalEffects code before.frame.locals before.memory after.memory) :
    SegmentRun program method start finish cost arguments before after ∧
      LocalSnapshots after.memory after.frame.locals (untouchedLocals code known) := by
  refine ⟨execution, ?_⟩
  rw [slots]
  exact effects.frame homes snapshots.untouched

#print axioms SegmentRun.frameLocals

/-- A segment with checked local-write effects inherits untouched input snapshots. The effect
    summary replaces repeated disjoint-read proofs at each of its numeric local stores. -/
theorem Segment.frameLocals {program : CIL.Program} {method start finish : Nat}
    {body : CIL.Method} {code : List CIL.Op} {slots : List LocalSlot}
    {initial entered : Memory} {boundary : Nat} {kinds : List CIL.LocalKind}
    {known : Nat → Option CIL.Value} {pre post : List Value → SegmentState → Prop}
    (_found : program[method]? = some body)
    (_placed : CodeAt body start code) (_finish : finish = start + code.length)
    (homes : WritableHomes entered boundary kinds slots)
    (snapshots : LocalSnapshots initial slots known)
    (contract : Segment program method start finish pre fun arguments state =>
      post arguments state ∧ state.frame.locals = slots ∧
        SegmentLocalEffects code slots initial state.memory) :
    Segment program method start finish pre fun arguments state =>
      post arguments state ∧ LocalSnapshots state.memory state.frame.locals
        (untouchedLocals code known) := by
  apply contract.consequence (fun _ _ valid => valid)
  intro arguments state result
  refine ⟨result.1, ?_⟩
  rw [result.2.1]
  exact result.2.2.frame homes snapshots.untouched

#print axioms Segment.frameLocals
end CIL.Safety
