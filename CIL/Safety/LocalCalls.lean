import CIL.Safety.LoopFrames

/-!
# Checked calls that write private local homes

These rules extend the existing frame and snapshot evidence to helper outputs. A written home
gets its value from the helper's checked postcondition; every retained snapshot needs separation
from the complete helper footprint. Writable storage alone never supplies initialized contents.
-/

namespace CIL.Safety

/-- Complete typed storage remains complete after a confined helper, even when the helper
    initializes previously unknown homes. -/
theorem CompleteWritableHomes.after_confined {before after : Memory} {lower : Nat}
    {kinds slots} {footprint : List (Reference × Nat)}
    (homes : CompleteWritableHomes before lower kinds slots)
    (confined : Confined footprint before after) (formed : before.WellFormed) :
    CompleteWritableHomes after lower kinds slots :=
  ⟨homes.writable.after_confined confined formed, homes.complete⟩

#print axioms CompleteWritableHomes.after_confined

/-- A helper's checked readback replaces the destination's previous snapshot. Only other
    homes proved apart from every helper write retain their previous values. -/
theorem LocalSnapshots.after_helper_write {before after : Memory}
    {slots : List LocalSlot} {known : Nat → Option CIL.Value}
    {footprint : List (Reference × Nat)}
    (snapshots : LocalSnapshots before slots known) (formed : before.WellFormed)
    (confined : Confined footprint before after)
    (index : Nat) (kind : CIL.LocalKind) (home : Reference) (stored : CIL.Value) (number : Nat)
    (slot : slots[index]? = some (.bytes kind home))
    (fits : localNumber kind stored = .ok number)
    (loaded : read after home (localWidth kind) 1 = .ok (numberBytes number (localWidth kind)))
    (apart : ∀ other value otherKind otherHome, other ≠ index → known other = some value →
      slots[other]? = some (.bytes otherKind otherHome) →
      ∀ entry ∈ footprint, Apart otherHome (localWidth otherKind) entry) :
    LocalSnapshots after slots (rememberLocal known index (localResult kind stored)) := by
  apply snapshots.after_effect index kind home stored number slot fits loaded
  intro other value otherKind otherHome _ different previous otherSlot readback
  exact confined.read_apart formed readback
    (apart other value otherKind otherHome different previous otherSlot)

#print axioms LocalSnapshots.after_helper_write

/-- A helper may write one private home and the caller footprint. The home readback replaces
    its snapshot; other homes remain known only with full helper-footprint separation. -/
theorem LoopFrame.after_helper_write {footprint called : List (Reference × Nat)}
    {caller current after : Memory} {kinds : List CIL.LocalKind} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value}
    (context : LoopFrame footprint caller current kinds slots known)
    (confined : Confined called current after) (formed : after.WellFormed)
    (index : Nat) (kind : CIL.LocalKind) (home : Reference) (stored : CIL.Value) (number : Nat)
    (slot : slots[index]? = some (.bytes kind home))
    (fits : localNumber kind stored = .ok number)
    (loaded : read after home (localWidth kind) 1 = .ok (numberBytes number (localWidth kind)))
    (covered : ∀ entry ∈ called,
      ∃ outer ∈ (home, localWidth kind) :: footprint, Within entry outer)
    (apart : ∀ other value otherKind otherHome, other ≠ index → known other = some value →
      slots[other]? = some (.bytes otherKind otherHome) →
      ∀ entry ∈ called, Apart otherHome (localWidth otherKind) entry) :
    LoopFrame footprint caller after kinds slots
      (rememberLocal known index (localResult kind stored)) := by
  have expanded := context.confined.widen (large := (home, localWidth kind) :: footprint)
    (fun entry member => List.mem_cons_of_mem _ member)
  have combined := expanded.trans (confined.widen_within covered)
  have callerConfined : Confined footprint caller after :=
    combined.forget_fresh (fresh := [(home, localWidth kind)]) (by
      intro entry member
      have same : entry = (home, localWidth kind) := List.mem_singleton.mp member
      subst entry
      exact context.homes.home_bound index kind home slot)
  exact ⟨callerConfined, formed, context.homes.after_confined confined context.wellFormed,
    context.snapshots.after_helper_write context.wellFormed confined index kind home stored
      number slot fits loaded apart⟩

#print axioms LoopFrame.after_helper_write

/-- A helper confined to one local home preserves every other home by the allocation evidence
    already held in the frame. No caller-input separation is required. -/
theorem LoopFrame.after_local_write {footprint : List (Reference × Nat)}
    {caller current after : Memory} {kinds : List CIL.LocalKind} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value}
    (context : LoopFrame footprint caller current kinds slots known)
    (index : Nat) (kind : CIL.LocalKind) (home : Reference) (stored : CIL.Value) (number : Nat)
    (slot : slots[index]? = some (.bytes kind home))
    (confined : Confined [(home, localWidth kind)] current after) (formed : after.WellFormed)
    (fits : localNumber kind stored = .ok number)
    (loaded : read after home (localWidth kind) 1 = .ok (numberBytes number (localWidth kind))) :
    LoopFrame footprint caller after kinds slots
      (rememberLocal known index (localResult kind stored)) := by
  apply context.after_helper_write confined formed index kind home stored number slot fits loaded
  · intro entry member
    have same : entry = (home, localWidth kind) := List.mem_singleton.mp member
    subst entry
    exact ⟨(home, localWidth kind), List.mem_cons_self, rfl, Nat.le_refl _, Nat.le_refl _⟩
  · intro other value otherKind otherHome different _ otherSlot entry member
    have same : entry = (home, localWidth kind) := List.mem_singleton.mp member
    subst entry
    exact Or.inl (context.homes.distinct other index otherKind kind otherHome home
      different otherSlot slot)

#print axioms LoopFrame.after_local_write

/-- A fetched contract call updates a private home and carries its typed output and named
    preservation evidence into the caller proof. The helper is actually invoked. -/
theorem WP.local_call {Input Output : Type} {contract : MethodContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method}
    {operation : CIL.Op} {args stack rest : List Value} {frame : Frame}
    {footprint : List (Reference × Nat)} {caller current : Memory}
    {kinds : List CIL.LocalKind} {known : Nat → Option CIL.Value}
    {post : Memory → List Value → Prop}
    (context : LoopFrame footprint caller current kinds frame.locals known)
    (holds : contract.Holds program callee) (input : Input)
    (found : program[method]? = some body) (fetched : body.code[pc]? = some operation)
    (stepped : Safety.step body operation pc args frame stack current =
      .ok (.call callee (contract.args input) rest current))
    (permitted : contract.pre input current)
    (index : Nat) (kind : CIL.LocalKind) (home : Reference)
    (slot : frame.locals[index]? = some (.bytes kind home))
    (writes : contract.footprint input = [(home, localWidth kind)])
    (stored : Output → CIL.Value) (number : Output → Nat)
    (fits : ∀ output, localNumber kind (stored output) = .ok (number output))
    (readback : ∀ final output, contract.post input current final output →
      read final home (localWidth kind) 1 = .ok (numberBytes (number output) (localWidth kind)))
    (suffix : ∀ final output, CallResult contract program callee input current final output →
      LoopFrame footprint caller final kinds frame.locals
        (rememberLocal known index (localResult kind (stored output))) →
      WP (fun fuel => run program fuel method (pc + 1) args frame
        (contract.results output ++ rest) final) post) :
    WP (fun fuel => run program fuel method pc args frame stack current) post := by
  apply run_call_of_contract holds input found fetched stepped rfl permitted
  intro final output result
  have invariants := result.frame_invariants found fetched stepped context.wellFormed
  have confined : Confined [(home, localWidth kind)] current final := writes ▸ result.framed
  exact suffix final output result
    (context.after_local_write index kind home (stored output) (number output) slot confined
      invariants.formed (fits output) (readback final output result.post))

#print axioms WP.local_call

end CIL.Safety
