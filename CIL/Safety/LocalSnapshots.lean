import CIL.Safety.WordSnapshots
import CIL.Safety.NumericHomes

/-!
# Remembered numeric locals of every kind

`LocalSnapshots memory slots known` records that each local whose index has
`known index = some value` is a numeric home whose bytes load as `value`, for every numeric
`LocalKind`: narrow and 32-bit integers, words, aggregates and vectors. It generalizes
`WordSnapshots`, which covers `.word64` homes only, and converts to and from it. A store
updates one entry with `rememberLocal`; writes, frame changes and confined calls that miss
every remembered home keep the rest, so a consumer proof steps each load to its exact value.
-/

namespace CIL.Safety

/-- Every local with `known index = some value` is a numeric home holding the bytes of a
    stored value that loads as `value`. A missing entry grants no initialization or value
    fact. -/
def LocalSnapshots (memory : Memory) (slots : List LocalSlot)
    (known : Nat → Option CIL.Value) : Prop :=
  ∀ index value, known index = some value →
    ∃ kind home stored number, slots[index]? = some (.bytes kind home) ∧
      localNumber kind stored = .ok number ∧ localResult kind stored = value ∧
      read memory home (localWidth kind) 1 = .ok (numberBytes number (localWidth kind))

/-- `known` updated so local `index` holds `value`. -/
def rememberLocal (known : Nat → Option CIL.Value) (index : Nat) (value : CIL.Value) :
    Nat → Option CIL.Value := fun other => if other = index then some value else known other

theorem LocalSnapshots.empty (memory : Memory) (slots : List LocalSlot) :
    LocalSnapshots memory slots (fun _ => none) := by
  intro index value impossible
  cases impossible

/-- Snapshots survive any change that keeps authority and initialization below the watermark
    and leaves every byte of each remembered home's allocation unchanged. -/
theorem LocalSnapshots.after_unchanged {before after : Memory} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots before slots known)
    (formed : before.WellFormed) (authority : AccessBelow before.nextIdentity before after)
    (unchanged : ∀ index value kind home, known index = some value →
      slots[index]? = some (.bytes kind home) → ∀ offset,
        after.cells home.allocation offset = before.cells home.allocation offset) :
    LocalSnapshots after slots known := by
  intro index value specified
  obtain ⟨kind, home, stored, number, slot, fits, result, loaded⟩ :=
    snapshots index value specified
  exact ⟨kind, home, stored, number, slot, fits, result,
    authority.read_eq loaded (formed.access_bound (read_access loaded))
      (fun _ _ => unchanged index value kind home specified slot _)⟩

/-- A write that shares no byte with any remembered home keeps every snapshot. The write
    may land in the same allocation as a home, at disjoint offsets. -/
theorem LocalSnapshots.after_write_apart {before after : Memory} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} {target : Reference} {bytes : List (BitVec 8)}
    {alignment : Nat} (snapshots : LocalSnapshots before slots known)
    (written : write before target bytes alignment = .ok after)
    (apart : ∀ index value kind home, known index = some value →
      slots[index]? = some (.bytes kind home) →
      home.allocation ≠ target.allocation ∨ home.offset + localWidth kind ≤ target.offset ∨
        target.offset + bytes.length ≤ home.offset) :
    LocalSnapshots after slots known := by
  intro index value specified
  obtain ⟨kind, home, stored, number, slot, fits, result, loaded⟩ :=
    snapshots index value specified
  exact ⟨kind, home, stored, number, slot, fits, result,
    write_preserves_disjoint_read written loaded (apart index value kind home specified slot)⟩

/-- Snapshots survive any change that keeps all memory older than `before`, such as frame
    entry or exit; well-formedness places every remembered home in that memory. -/
theorem LocalSnapshots.after_below {before after : Memory} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots before slots known)
    (preserved : MemoryBelow before.nextIdentity before after) (formed : before.WellFormed) :
    LocalSnapshots after slots known := by
  intro index value specified
  obtain ⟨kind, home, stored, number, slot, fits, result, loaded⟩ :=
    snapshots index value specified
  exact ⟨kind, home, stored, number, slot, fits, result,
    (preserved.read home (formed.access_bound (read_access loaded)) _ 1).trans loaded⟩

/-- Writing the bytes of `stored` to the home of local `index` remembers the value it loads
    as and keeps every other snapshot, since distinct writable homes never share an
    allocation. -/
theorem LocalSnapshots.after_write {entered before after : Memory} {boundary : Nat}
    {kinds slots} {known : Nat → Option CIL.Value}
    (snapshots : LocalSnapshots before slots known)
    (homes : WritableHomes entered boundary kinds slots)
    (index : Nat) (kind : CIL.LocalKind) (home : Reference) (stored : CIL.Value)
    (number : Nat) (fits : localNumber kind stored = .ok number)
    (slot : slots[index]? = some (.bytes kind home))
    (written : write before home (numberBytes number (localWidth kind)) 1 = .ok after) :
    LocalSnapshots after slots (rememberLocal known index (localResult kind stored)) := by
  intro other value specified
  by_cases same : other = index
  · subst other
    have sameValue : localResult kind stored = value := by
      simpa [rememberLocal] using specified
    have readback := write_readback _ _ _ _ _ written
    have length : (numberBytes number (localWidth kind)).length = localWidth kind := by
      simp [numberBytes]
    rw [length] at readback
    exact ⟨kind, home, stored, number, slot, fits, sameValue, readback⟩
  · have previous : known other = some value := by simpa [rememberLocal, same] using specified
    obtain ⟨otherKind, otherHome, otherStored, otherNumber, otherSlot, otherFits, result,
      loaded⟩ := snapshots other value previous
    exact ⟨otherKind, otherHome, otherStored, otherNumber, otherSlot, otherFits, result,
      write_preserves_disjoint_read written loaded
        (Or.inl (homes.distinct other index otherKind kind otherHome home same otherSlot slot))⟩

/-- A checked local read pushes the remembered value. -/
theorem LocalSnapshots.load {body : CIL.Method} {pc index : Nat} {args stack : List Value}
    {frame : Frame} {memory : Memory} {known : Nat → Option CIL.Value}
    (snapshots : LocalSnapshots memory frame.locals known) (value : CIL.Value)
    (specified : known index = some value) :
    step body (.local index) pc args frame stack memory =
      .ok (.next (pc + 1) (.scalar value :: stack) frame memory) := by
  obtain ⟨kind, home, stored, number, slot, fits, result, loaded⟩ :=
    snapshots index value specified
  have stepped := step_load_numeric_local (body := body) (pc := pc) (args := args)
    (stack := stack) kind stored number fits slot loaded
  rwa [result] at stepped

/-- Storing a numeric value initializes precisely its home, remembers the value it loads as
    and keeps the caller's memory and the other snapshots. No prior read permission is
    needed. -/
theorem LocalSnapshots.store {body : CIL.Method} {pc index : Nat} {args stack : List Value}
    {frame : Frame} {entered memory : Memory} {boundary : Nat} {kinds}
    {known : Nat → Option CIL.Value}
    (snapshots : LocalSnapshots memory frame.locals known)
    (homes : WritableHomes entered boundary kinds frame.locals) (formed : memory.WellFormed)
    (kind : CIL.LocalKind) (home : Reference) (value : CIL.Value) (number : Nat)
    (fits : localNumber kind value = .ok number)
    (slot : frame.locals[index]? = some (.bytes kind home))
    (ready : access memory home (localWidth kind) 1 true = .ok ()) :
    ∃ after,
      step body (.setLocal index) pc args frame (.scalar value :: stack) memory =
        .ok (.next (pc + 1) stack frame after) ∧
      LocalSnapshots after frame.locals (rememberLocal known index (localResult kind value)) ∧
      after.WellFormed ∧ MemoryBelow boundary memory after ∧
      AccessBelow memory.nextIdentity memory after ∧
      write memory home (numberBytes number (localWidth kind)) 1 = .ok after := by
  obtain ⟨after, stepped, written, _⟩ := step_store_numeric_local
    (body := body) (pc := pc) (args := args) (rest := stack) kind value number fits slot ready
  exact ⟨after, stepped,
    snapshots.after_write homes index kind home value number fits slot written,
    write_preserves_wellFormed _ _ _ _ _ formed written,
    write_preserves_memory_below _ _ _ _ _ _ (homes.home_bound index kind home slot) written,
    write_preserves_access_below written _, written⟩

/-- The remembered words of `known`, as the values their word homes load as. -/
def wordLocals (known : Nat → Option (BitVec 64)) : Nat → Option CIL.Value :=
  fun index => (known index).map .i64

/-- The remembered 64-bit integers of `known`; every other remembered value is dropped. -/
def localWords (known : Nat → Option CIL.Value) : Nat → Option (BitVec 64) :=
  fun index => match known index with
    | some (.i64 word) => some word
    | _ => none

/-- Remembered words are remembered locals. -/
theorem WordSnapshots.toLocalSnapshots {memory : Memory} {slots : List LocalSlot}
    {known : Nat → Option (BitVec 64)} (snapshots : WordSnapshots memory slots known) :
    LocalSnapshots memory slots (wordLocals known) := by
  intro index value specified
  cases present : known index with
  | none => simp [wordLocals, present] at specified
  | some word =>
    have sameValue : CIL.Value.i64 word = value := by
      simpa [wordLocals, present] using specified
    obtain ⟨home, slot, loaded⟩ := snapshots index word present
    exact ⟨.word64, home, .i64 word, word.toNat, slot, rfl, sameValue, loaded⟩

/-- Remembered 64-bit integer locals are remembered words: only a word home loads as
    `.i64`. -/
theorem LocalSnapshots.toWordSnapshots {memory : Memory} {slots : List LocalSlot}
    {known : Nat → Option CIL.Value} (snapshots : LocalSnapshots memory slots known) :
    WordSnapshots memory slots (localWords known) := by
  intro index word specified
  have present : known index = some (.i64 word) := by
    unfold localWords at specified
    split at specified <;> simp_all
  obtain ⟨kind, home, stored, number, slot, fits, result, loaded⟩ :=
    snapshots index (.i64 word) present
  have wordHome : kind = .word64 ∧ number = word.toNat := by
    cases kind <;> cases stored <;>
      simp_all [localResult, localNumber, CIL.Value.hasUnspecified] <;>
      (split at fits <;> simp_all)
  obtain ⟨rfl, rfl⟩ := wordHome
  exact ⟨home, slot, loaded⟩

/-- Remembering a word and then viewing the words as locals is remembering its value. -/
theorem wordLocals_rememberWord (known : Nat → Option (BitVec 64)) (index : Nat)
    (word : BitVec 64) :
    wordLocals (rememberWord known index word) =
      rememberLocal (wordLocals known) index (.i64 word) := by
  funext other
  by_cases same : other = index <;> simp [wordLocals, rememberWord, rememberLocal, same]

/-- Numeric homes are writable homes of their kinds. -/
theorem NumericHomes.writable {memory : Memory} {lower : Nat} {specs slots}
    (homes : NumericHomes memory lower specs slots) :
    WritableHomes memory lower (numericKinds specs) slots := by
  induction homes with
  | nil lower => exact .nil lower
  | cons reference spec fresh _ writable _ tail =>
    exact .cons reference spec.kind fresh writable tail

/-- The values the initialized locals of `specs` load as, before any store. -/
def numericKnown (specs : List NumericLocalSpec) : Nat → Option CIL.Value :=
  fun index => specs[index]?.map fun spec => localResult spec.kind spec.value

/-- A fresh numeric frame remembers every local's initial value. -/
theorem NumericHomes.snapshots {memory : Memory} {lower : Nat} {specs slots}
    (homes : NumericHomes memory lower specs slots) :
    LocalSnapshots memory slots (numericKnown specs) := by
  intro index value specified
  cases present : specs[index]? with
  | none => simp [numericKnown, present] at specified
  | some spec =>
    have sameValue : localResult spec.kind spec.value = value := by
      simpa [numericKnown, present] using specified
    obtain ⟨home, slot, _, loaded, _⟩ := homes.home_at index spec present
    exact ⟨spec.kind, home, spec.value, spec.number, slot, spec.fits, sameValue, loaded⟩

#print axioms LocalSnapshots.empty
#print axioms LocalSnapshots.after_unchanged
#print axioms LocalSnapshots.after_write_apart
#print axioms LocalSnapshots.after_below
#print axioms LocalSnapshots.after_write
#print axioms LocalSnapshots.load
#print axioms LocalSnapshots.store
#print axioms WordSnapshots.toLocalSnapshots
#print axioms LocalSnapshots.toWordSnapshots
#print axioms wordLocals_rememberWord
#print axioms NumericHomes.writable
#print axioms NumericHomes.snapshots
end CIL.Safety
