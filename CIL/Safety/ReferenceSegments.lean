import CIL.Safety.ObjectFields

/-!
# Segments of linked instances

An intrusive list, such as a pool's free list, links instances through one reference field.
`ReferenceField.Segment field memory start stop nodes` states that following `field` from
`start` visits exactly the instances `nodes`, each readable, and arrives at `stop`. A segment is
a finite inductive path, so a segment to null proves that the chain from `start` ends: no cycle
is reachable from it, and `nodes.length` is a termination measure for a loop that walks it,
falling by one at each hop (`Segment.next`).

A segment is a precondition the caller states about its memory, not a property every memory
has: a program can link a cycle, and then no segment to null exists. A walk that never stores
keeps the memory and so the segment it started from; frame entry keeps it as well
(`Segment.after_below`).
-/

namespace CIL.Safety

namespace ReferenceField

/-- Following `field` from `start` in `memory` visits the readable instances `nodes`, in order,
    and arrives at `stop`. -/
inductive Segment (field : ReferenceField) (memory : Memory) :
    ManagedReference → ManagedReference → List Reference → Prop
  /-- Every reference reaches itself, visiting nothing. -/
  | nil (stop : ManagedReference) : Segment field memory stop stop []
  /-- A readable instance whose field starts a segment heads one more node. -/
  | cons {node : Reference} {stop : ManagedReference} {nodes : List Reference}
      (readable : field.Readable memory node)
      (rest : Segment field memory (field.of memory node) stop nodes) :
      Segment field memory (.address node) stop (node :: nodes)

/-- A segment to null from an instance heads at that instance: its field is readable, and the
    rest of the chain, one node shorter, starts at what the field holds. -/
theorem Segment.next {field : ReferenceField} {memory : Memory} {node : Reference}
    {nodes : List Reference} (segment : field.Segment memory (.address node) .null nodes) :
    ∃ rest, nodes = node :: rest ∧ field.Readable memory node ∧
      field.Segment memory (field.of memory node) .null rest := by
  cases segment with
  | cons readable rest => exact ⟨_, rfl, readable, rest⟩
#print axioms Segment.next

/-- A segment from null to null visits no instance. -/
theorem Segment.null_nil {field : ReferenceField} {memory : Memory} {nodes : List Reference}
    (segment : field.Segment memory .null .null nodes) : nodes = [] := by
  cases segment with
  | nil => rfl
#print axioms Segment.null_nil

/-- The start of a segment to null forms as an object reference, so a walk can load and compare
    it: null forms everywhere, and an instance heading a segment is live. -/
theorem Segment.formed {field : ReferenceField} {memory : Memory} {start : ManagedReference}
    {nodes : List Reference} (segment : field.Segment memory start .null nodes) :
    formObject memory start = .ok (.object start) := by
  cases segment with
  | nil => rfl
  | cons readable _ => exact readable.live.formed
#print axioms Segment.formed

/-- A segment holds in memory that keeps every allocation below a watermark above the
    instances it visits and has allocated up to the watermark, as frame entry leaves the
    caller's memory. -/
theorem Segment.after_below {watermark : Nat} {field : ReferenceField} {before after : Memory}
    {start stop : ManagedReference} {nodes : List Reference}
    (segment : field.Segment before start stop nodes)
    (preserved : MemoryBelow watermark before after)
    (covered : before.nextIdentity ≤ watermark) (grows : watermark ≤ after.nextIdentity) :
    field.Segment after start stop nodes := by
  induction segment with
  | nil stop => exact .nil stop
  | cons readable _ kept =>
    have moved := readable.below preserved (Nat.lt_of_lt_of_le readable.old covered) grows
    exact .cons moved.1 (moved.2 ▸ kept)
#print axioms Segment.after_below

end ReferenceField

end CIL.Safety
