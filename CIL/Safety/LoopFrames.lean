import CIL.Safety.LoopVC
import CIL.Safety.ConfinedSnapshots
import CIL.Safety.BufferContents

/-!
# Frame facts of loop invariants

A loop over a frame entered from symbolic caller memory needs the same bookkeeping at every
cutpoint: caller storage changes only inside the method's footprint, the memory stays well
formed, each local home stays writable and the locals hold the values the state names.
`LoopFrame` is that conjunction, and `FrameState` carries it in the loop state, so an invariant
states only the loop's property. Its slots are the frame's `locals`, so the lemmas about
`frame.locals` apply to it, and a local without a byte home is remembered as `none`.
`bind_entry ... allocating` proves the entered frame's `LoopFrame` from `LoopFrame.ofEntry`,
`WritableHomes.entry`, `LocalSnapshots.entry` and, for the other locals, `WritableHomes.skip` and
`LocalSnapshots.skip`.

Each lemma proves the frame facts after one kind of step from the semantics of that step: a
local store (`LoopFrame.store`), a write to caller storage inside the footprint
(`LoopFrame.write`), a confined call (`LoopFrame.after_confined`) and the return
(`LoopFrame.leave`). Homes are allocated above the caller's memory, so a write or callee
footprint proved to lie in caller storage cannot reach them. A write or call that names a home,
as through a local's address or a by-reference argument, has no such proof, and then the frame
facts stay the author's obligation.
-/

namespace CIL.Safety

/-- Locals `0, 1, ...` remembered as holding `values` in order; a `none` entry, as for a local
    without a byte home, remembers nothing. -/
def knownLocals (values : List (Option CIL.Value)) : Nat → Option CIL.Value :=
  fun index => values[index]?.join

/-- Remembering a new value of a listed local lists that value in its place. -/
theorem rememberLocal_knownLocals {values : List (Option CIL.Value)} {index : Nat}
    (present : index < values.length) (value : CIL.Value) :
    rememberLocal (knownLocals values) index value =
      knownLocals (values.set index (some value)) := by
  funext other
  by_cases same : other = index
  · subst same
    simp [rememberLocal, knownLocals, present]
  · simp [rememberLocal, knownLocals, same, Ne.symm same]

/-- A write keeps write access to every home. -/
theorem WritableHomes.after_write {memory after : Memory} {lower : Nat} {kinds slots}
    {target : Reference} {bytes : List (BitVec 8)} {alignment : Nat}
    (homes : WritableHomes memory lower kinds slots)
    (written : write memory target bytes alignment = .ok after) :
    WritableHomes after lower kinds slots := by
  induction homes with
  | nil lower => exact .nil lower
  | cons reference kind fresh writable _ tail =>
    obtain ⟨_, ready⟩ := access_requirements writable
    exact .cons reference kind fresh (ready.after_write written).access tail
  | skip notHome _ tail => exact .skip notHome tail

/-- A confined call keeps write access to every home that existed before it. -/
theorem WritableHomes.after_confined {before after : Memory} {lower : Nat} {kinds slots}
    {footprint : List (Reference × Nat)} (homes : WritableHomes before lower kinds slots)
    (framed : Confined footprint before after) (formed : before.WellFormed) :
    WritableHomes after lower kinds slots := by
  induction homes with
  | nil lower => exact .nil lower
  | cons reference kind fresh writable _ tail =>
    exact .cons reference kind fresh
      ((framed.access_write reference (formed.access_bound writable) _ 1).trans writable) tail
  | skip notHome _ tail => exact .skip notHome tail

/-- The home of each slot of `WritableHomes` is writable. -/
theorem WritableHomes.writable_at {memory : Memory} {lower : Nat} {kinds slots}
    (homes : WritableHomes memory lower kinds slots) {index : Nat} {kind : CIL.LocalKind}
    {home : Reference} (slot : slots[index]? = some (.bytes kind home)) :
    access memory home (localWidth kind) 1 true = .ok () := by
  induction homes generalizing index with
  | nil => simp at slot
  | cons reference kind' fresh writable _ tail =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, LocalSlot.bytes.injEq] at slot
      obtain ⟨rfl, rfl⟩ := slot
      exact writable
    | succ index => exact tail (by simpa using slot)
  | skip notHome _ tail =>
    cases index with
    | zero => exact absurd (by simpa using slot) (notHome kind home)
    | succ index => exact tail (by simpa using slot)

/-- A numeric entry home lies below every home frame entry allocates after it. -/
theorem NumericEntryHome.before_made {caller current result : Memory} {kind later : CIL.LocalKind}
    {number activation : Nat} {home next : Reference} {value : CIL.Value}
    (holds : NumericEntryHome caller current kind number home)
    (made : makeLocal activation later value current =
      .ok (.bytes later next, [next.allocation], result)) :
    home.allocation + 1 ≤ next.allocation :=
  Nat.le_trans holds.bounded ((makeLocal_fresh _ _ _ _ _ _ _ made).2 next.allocation (by simp)).1

/-- A numeric entry home heads the writable homes allocated after it. -/
theorem WritableHomes.entry {caller current : Memory} {lower number : Nat}
    {kind : CIL.LocalKind} {home : Reference} {kinds slots}
    (holds : NumericEntryHome caller current kind number home) (fresh : lower ≤ home.allocation)
    (tail : WritableHomes current (home.allocation + 1) kinds slots) :
    WritableHomes current lower (kind :: kinds) (.bytes kind home :: slots) :=
  .cons home kind fresh holds.writable tail

/-- An empty value list remembers no local. -/
theorem LocalSnapshots.knownLocals_nil (memory : Memory) (slots : List LocalSlot) :
    LocalSnapshots memory slots (knownLocals []) := by
  intro index value listed
  simp [knownLocals] at listed

/-- A numeric entry home holding its initializer `stored`, which loads as `value`, heads the
    snapshots of the locals after it. -/
theorem LocalSnapshots.entry {caller current : Memory} {kind : CIL.LocalKind} {number : Nat}
    {home : Reference} {stored value : CIL.Value} {slots : List LocalSlot}
    {values : List (Option CIL.Value)} (holds : NumericEntryHome caller current kind number home)
    (fits : localNumber kind stored = .ok number) (result : localResult kind stored = value)
    (tail : LocalSnapshots current slots (knownLocals values)) :
    LocalSnapshots current (.bytes kind home :: slots) (knownLocals (some value :: values)) := by
  intro index remembered listed
  cases index with
  | zero =>
    exact ⟨kind, home, stored, number, rfl, fits,
      by simpa [knownLocals, result] using listed, holds.loaded⟩
  | succ index => simpa using tail index remembered (by simpa [knownLocals] using listed)

/-- A local remembered as nothing heads the snapshots of the locals after it. -/
theorem LocalSnapshots.skip {memory : Memory} {slot : LocalSlot} {slots : List LocalSlot}
    {values : List (Option CIL.Value)} (tail : LocalSnapshots memory slots (knownLocals values)) :
    LocalSnapshots memory (slot :: slots) (knownLocals (none :: values)) := by
  intro index remembered listed
  cases index with
  | zero => simp [knownLocals] at listed
  | succ index => simpa using tail index remembered (by simpa [knownLocals] using listed)

/-- Replacing a slot with one that has no byte home keeps the other homes writable. -/
theorem WritableHomes.set_slot {memory : Memory} {lower : Nat} {kinds slots}
    (homes : WritableHomes memory lower kinds slots) (index : Nat) {slot : LocalSlot}
    (notHome : ∀ stored reference, slot ≠ .bytes stored reference) :
    WritableHomes memory lower kinds (slots.set index slot) := by
  induction homes generalizing index with
  | nil lower => exact .nil lower
  | cons reference kind fresh writable tail ih =>
    cases index with
    | zero => exact .skip notHome (tail.weaken (Nat.le_trans fresh (Nat.le_succ _)))
    | succ index => exact .cons reference kind fresh writable (ih index)
  | skip other tail ih =>
    cases index with
    | zero => exact .skip notHome tail
    | succ index => exact .skip other (ih index)

/-- Replacing the slot of a local remembered as nothing keeps every snapshot. -/
theorem LocalSnapshots.set_slot {memory : Memory} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known)
    {index : Nat} (slot : LocalSlot) (unknown : known index = none) :
    LocalSnapshots memory (slots.set index slot) known := by
  intro other value remembered
  have different : index ≠ other := fun same => by simp_all
  obtain ⟨kind, home, stored, number, found, fits, result, loaded⟩ :=
    snapshots other value remembered
  exact ⟨kind, home, stored, number, by rw [List.getElem?_set_ne different]; exact found, fits,
    result, loaded⟩

#print axioms rememberLocal_knownLocals
#print axioms WritableHomes.after_write
#print axioms WritableHomes.after_confined
#print axioms WritableHomes.writable_at
#print axioms NumericEntryHome.before_made
#print axioms WritableHomes.entry
#print axioms LocalSnapshots.knownLocals_nil
#print axioms LocalSnapshots.entry
#print axioms LocalSnapshots.skip
#print axioms WritableHomes.set_slot
#print axioms LocalSnapshots.set_slot

/-- The frame part of a loop invariant at memory `current` of a frame entered from `caller`:
    caller storage changed only inside `footprint`, the memory is well formed, every home among
    the frame's local `slots` lies above the caller's memory and stays writable, and the locals
    of `known` hold their values. `kinds`, `slots` and `known` follow the frame's local indices. -/
structure LoopFrame (footprint : List (Reference × Nat)) (caller current : Memory)
    (kinds : List CIL.LocalKind) (slots : List LocalSlot) (known : Nat → Option CIL.Value) :
    Prop where
  confined : Confined footprint caller current
  wellFormed : current.WellFormed
  homes : WritableHomes current caller.nextIdentity kinds slots
  snapshots : LocalSnapshots current slots known

/-- A loop state over a frame entered from `caller`: the author's `values`, the memory, and the
    frame facts proved there with the frame's locals `slots values` holding `locals values`. -/
structure FrameState (footprint : List (Reference × Nat)) (caller : Memory)
    (kinds : List CIL.LocalKind) (α : Type) (slots : α → List LocalSlot)
    (locals : α → List (Option CIL.Value)) where
  values : α
  memory : Memory
  frame : LoopFrame footprint caller memory kinds (slots values) (knownLocals (locals values))

variable {footprint : List (Reference × Nat)} {caller current : Memory}
  {kinds : List CIL.LocalKind} {slots : List LocalSlot}

/-- Frame entry keeps the caller's memory, so the entered frame starts the frame facts for any
    footprint. -/
theorem LoopFrame.ofEntry (footprint : List (Reference × Nat)) {known : Nat → Option CIL.Value}
    (entered : EntryMemory caller current)
    (homes : WritableHomes current caller.nextIdentity kinds slots)
    (snapshots : LocalSnapshots current slots known) :
    LoopFrame footprint caller current kinds slots known :=
  ⟨Confined.ofMemoryBelow entered.kept (Nat.le_refl _) entered.grown, entered.wellFormed, homes,
    snapshots⟩

/-- The home of each byte slot of a loop frame forms, so its address can be taken. -/
theorem LoopFrame.form_home {known : Nat → Option CIL.Value}
    (frame : LoopFrame footprint caller current kinds slots known) (index : Nat)
    {kind : CIL.LocalKind} {home : Reference}
    (slot : slots[index]? = some (.bytes kind home) := by rfl) :
    form current home = .ok home :=
  access_reference_valid _ _ _ _ _ (frame.homes.writable_at slot)

/-- A listed local loads as its listed value. -/
theorem LoopFrame.load {values : List (Option CIL.Value)}
    (frame : LoopFrame footprint caller current kinds slots (knownLocals values)) (index : Nat)
    {kind : CIL.LocalKind} {home : Reference}
    (slot : slots[index]? = some (.bytes kind home) := by rfl) {value : CIL.Value}
    (present : values[index]? = some (some value) := by rfl) :
    loadLocal current (.bytes kind home) = .ok (.scalar value) := by
  obtain ⟨kind', home', stored, number, found, fits, result, loaded⟩ :=
    frame.snapshots index value (by simp [knownLocals, present])
  rw [slot] at found
  cases found
  rw [← result]
  exact load_numeric_local kind stored number fits loaded

/-- Storing a numeric value into a listed local lists the value it loads as and keeps every
    other frame fact; the store changes nothing below the caller's watermark. -/
theorem LoopFrame.store {values : List (Option CIL.Value)}
    (frame : LoopFrame footprint caller current kinds slots (knownLocals values)) (index : Nat)
    (value : CIL.Value) {kind : CIL.LocalKind} {home : Reference} {number : Nat}
    (fits : localNumber kind value = .ok number)
    (slot : slots[index]? = some (.bytes kind home) := by rfl)
    (present : index < values.length := by simp) :
    ∃ updated, storeLocal current (.bytes kind home) (.scalar value) =
        .ok (.bytes kind home, updated) ∧
      LoopFrame footprint caller updated kinds slots
        (knownLocals (values.set index (some (localResult kind value)))) ∧
      MemoryBelow caller.nextIdentity current updated := by
  have fresh := frame.homes.home_bound index kind home slot
  obtain ⟨updated, written, stored, _⟩ :=
    store_numeric_local kind value number fits (frame.homes.writable_at slot)
  have below := write_preserves_memory_below _ _ _ _ _ _ fresh written
  refine ⟨updated, stored, ⟨frame.confined.then_below below
      (Nat.le_of_eq (write_nextIdentity written).symm),
    write_preserves_wellFormed _ _ _ _ _ frame.wellFormed written,
    frame.homes.after_write written, ?_⟩, below⟩
  rw [← rememberLocal_knownLocals present]
  exact frame.snapshots.after_write frame.homes index kind home value number fits slot written

/-- Assigning a local without a byte home, such as a span or reference local, keeps the frame
    facts over the frame's updated locals; a home or remembered local cannot be replaced. -/
theorem LoopFrame.set_local {known : Nat → Option CIL.Value}
    (frame : LoopFrame footprint caller current kinds slots known) (index : Nat) (slot : LocalSlot)
    (notHome : ∀ stored reference, slot ≠ .bytes stored reference := by
      intro _ _ same; cases same)
    (unknown : known index = none := by rfl) :
    LoopFrame footprint caller current kinds (slots.set index slot) known :=
  ⟨frame.confined, frame.wellFormed, frame.homes.set_slot index notHome,
    frame.snapshots.set_slot slot unknown⟩

/-- A write to caller storage inside `footprint` keeps the frame facts: it is confined, and no
    home lies in caller storage. A target not proved older than the caller's watermark, such as
    a local's own address, gives no frame facts. -/
theorem LoopFrame.write {known : Nat → Option CIL.Value} {after : Memory} {target : Reference}
    {bytes : List (BitVec 8)} {alignment : Nat}
    (frame : LoopFrame footprint caller current kinds slots known)
    (written : write current target bytes alignment = .ok after)
    (within : ∃ entry ∈ footprint, Within (target, bytes.length) entry)
    (old : target.allocation < caller.nextIdentity) :
    LoopFrame footprint caller after kinds slots known :=
  ⟨frame.confined.trans (Confined.write_within written within),
    write_preserves_wellFormed _ _ _ _ _ frame.wellFormed written, frame.homes.after_write written,
    frame.snapshots.after_write_apart written fun index _ kind home _ slot =>
      Or.inl (Nat.ne_of_gt (Nat.lt_of_lt_of_le old (frame.homes.home_bound index kind home slot)))⟩

/-- A write of element `index` of the `count`-element caller buffer at `base` in `footprint`
    keeps the frame facts. -/
theorem LoopFrame.write_element {known : Nat → Option CIL.Value} {after : Memory}
    {base : Reference} {width index count alignment : Nat} {bytes : List (BitVec 8)}
    (frame : LoopFrame footprint caller current kinds slots known)
    (written : CIL.Safety.write current (base.element width index) bytes alignment = .ok after)
    (member : (base, width * count) ∈ footprint) (lower : index < count)
    (old : base.allocation < caller.nextIdentity)
    (sized : bytes.length = width := by simp [numberBytes_length]) :
    LoopFrame footprint caller after kinds slots known :=
  frame.write written ⟨_, member, by
    simpa [Within, sized] using base.element_run_within width (first := index) (count := 1)
      (outer := 0) (total := count) (Nat.zero_le _) (by omega)⟩ old

/-- A call confined to `called` keeps the frame facts when each entry of `called` lies inside
    `footprint` in caller storage. An entry naming a home, as a local passed by reference does,
    gives no frame facts. -/
theorem LoopFrame.after_confined {known : Nat → Option CIL.Value} {after : Memory}
    {called : List (Reference × Nat)}
    (frame : LoopFrame footprint caller current kinds slots known)
    (framed : Confined called current after) (formed : after.WellFormed)
    (covered : ∀ entry ∈ called, ∃ outer ∈ footprint, Within entry outer)
    (old : ∀ entry ∈ called, entry.1.allocation < caller.nextIdentity) :
    LoopFrame footprint caller after kinds slots known :=
  ⟨frame.confined.trans (framed.widen_within covered), formed,
    frame.homes.after_confined framed frame.wellFormed,
    frame.snapshots.after_confined framed frame.wellFormed fun index _ kind home _ slot entry
      member => Or.inl (Nat.ne_of_gt
        (Nat.lt_of_lt_of_le (old entry member) (frame.homes.home_bound index kind home slot)))⟩

/-- A reference formed in well-formed memory names an allocation below its watermark. -/
theorem Memory.WellFormed.form_bound {memory : Memory} {base : Reference}
    (formed : memory.WellFormed) (valid : form memory base = .ok base) :
    base.allocation < memory.nextIdentity := by
  obtain ⟨_, present, _, _⟩ := formed_reference_live _ _ _ valid
  exact (formed.1 _ _ present).1

/-- A caller reference formed before entry stays formed. -/
theorem LoopFrame.form {known : Nat → Option CIL.Value}
    (frame : LoopFrame footprint caller current kinds slots known) {base : Reference}
    (valid : form caller base = .ok base) (old : base.allocation < caller.nextIdentity) :
    form current base = .ok base := by
  simpa only [CIL.Safety.form, liveAllocation, frame.confined.allocations _ old] using valid

/-- Leaving the entered frame keeps the caller's storage outside `footprint`, and changes
    nothing the caller allocated. -/
theorem LoopFrame.leave {known : Nat → Option CIL.Value} {body : CIL.Method} {args : List Value}
    {entered : Memory} {entering : Frame}
    (frame : LoopFrame footprint caller current kinds slots known)
    (setup : enterFrame body args caller = .ok (entering, entered)) :
    Confined footprint caller (leaveFrame entering current) ∧
      MemoryBelow caller.nextIdentity current (leaveFrame entering current) :=
  have owned : ∀ id ∈ entering.owned, caller.nextIdentity ≤ id := fun id member =>
    ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  ⟨frame.confined.after_leaveFrame owned,
    leaveFrame_preserves_memory_below entering current _ owned⟩

/-- A frame confined to no caller storage has kept all of it. -/
theorem LoopFrame.kept {known : Nat → Option CIL.Value}
    (frame : LoopFrame [] caller current kinds slots known) :
    MemoryBelow caller.nextIdentity caller current :=
  frame.confined.nil_memoryBelow

/-- Leaving a frame confined to no caller storage, through any frame that owns what the entry
    allocated, keeps all of the caller's memory. -/
theorem LoopFrame.leave_kept {known : Nat → Option CIL.Value} {body : CIL.Method}
    {args : List Value} {entered : Memory} {entering : Frame}
    (setup : enterFrame body args caller = .ok (entering, entered))
    (frame : LoopFrame [] caller current kinds slots known) (exited : Frame)
    (owned : exited.owned = entering.owned) :
    MemoryBelow caller.nextIdentity caller (leaveFrame exited current) :=
  frame.kept.trans (leaveFrame_preserves_memory_below exited current _ fun id member =>
    ((enterFrame_fresh _ _ _ _ _ setup).2 id (owned ▸ member)).1)

/-- A checked span of well-formed caller memory stays checked in the memory of a frame confined
    to no caller storage, so a loop state keeps its span in caller memory and reads it in frame
    memory. -/
theorem CheckedSpan.within {known : Nat → Option CIL.Value} {view : SpanView} {width : Nat}
    {writable : Bool} {values : List (BitVec (8 * width))}
    (span : CheckedSpan caller view width writable values) (wellFormed : caller.WellFormed)
    (frame : LoopFrame [] caller current kinds slots known) :
    CheckedSpan current view width writable values :=
  span.below wellFormed frame.kept

#print axioms LoopFrame.ofEntry
#print axioms LoopFrame.kept
#print axioms LoopFrame.leave_kept
#print axioms CheckedSpan.within
#print axioms LoopFrame.form_home
#print axioms LoopFrame.load
#print axioms LoopFrame.store
#print axioms LoopFrame.set_local
#print axioms LoopFrame.write
#print axioms LoopFrame.write_element
#print axioms Memory.WellFormed.form_bound
#print axioms LoopFrame.after_confined
#print axioms LoopFrame.form
#print axioms LoopFrame.leave

/-- An `int` index below `2^31` is its natural value as a signed native offset. -/
theorem int_offset {index : CIL.W32} (small : index.toNat < 2^31) :
    BitVec.ofInt 64 index.toInt = BitVec.ofNat 64 index.toNat := by
  have : index.toInt = (index.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]
    simp [show 2 * index.toNat < 2^32 by omega]
  rw [this, BitVec.ofInt_natCast]

/-- Below a count under `2^31`, the signed `int` comparison agrees with the natural one. -/
theorem int_lt {index count : CIL.W32} (small : count.toNat < 2^31)
    (lower : index.toNat < count.toNat) : index.toInt < count.toInt := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  simp only [show 2 * index.toNat < 2^32 by omega, show 2 * count.toNat < 2^32 by omega,
    ite_true]
  omega

/-- An index below another value of its width increments without wrapping. -/
theorem toNat_succ {width : Nat} {index count : BitVec width}
    (lower : index.toNat < count.toNat) : (index + 1).toNat = index.toNat + 1 := by
  have bound := count.isLt
  rw [BitVec.toNat_add]
  cases width with
  | zero => omega
  | succ width =>
    have one : (1 : BitVec (width + 1)).toNat = 1 := by simp
    rw [one, Nat.mod_eq_of_lt (by omega)]

/-- Adding an `int` index below `2^31` to a formed base addresses the element at that index,
    when that element is accessible. -/
theorem add_int_element {memory : Memory} {base : Reference} {width : Nat} {index : CIL.W32}
    {writing : Bool} (formed : memory.WellFormed) (valid : form memory base = .ok base)
    (small : index.toNat < 2^31)
    (target : access memory (base.element width index.toNat) width 1 writing = .ok ()) :
    add memory base width (BitVec.ofInt 64 index.toInt) =
      .ok (base.element width index.toNat) := by
  rw [int_offset small]
  exact add_element formed valid target

/-- `store64` through an address whose eight-byte write succeeds steps to that write. The step
    holds in any method and frame. -/
theorem step_store64_of_write {memory after : Memory} {target : Reference} {word : CIL.W64}
    (written : write memory target (numberBytes word.toNat 8) 1 = .ok after) :
    ∀ body pc args frame rest,
      step body .store64 pc args frame
        (.scalar (.i64 word) :: .reference (.address target) :: rest) memory =
        .ok (.next (pc + 1) rest frame after) := by
  intro body pc args frame rest
  rw [step_store64_reference_eq]
  simp [storeValue, referenceAt, ordinaryAccessAlignment, written, checkedAt,
    CIL.Value.hasUnspecified, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms step_store64_of_write
#print axioms int_offset
#print axioms int_lt
#print axioms toNat_succ
#print axioms add_int_element

end CIL.Safety
