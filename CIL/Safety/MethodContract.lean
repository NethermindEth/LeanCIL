import CIL.Verification
import CIL.Safety.SymbolicExecution
import CIL.Safety.Obligations
import CIL.Safety.MemoryBelow
import CIL.Safety.ReturnMemory
import CIL.Safety.ViewReuse
import CIL.Safety.WriteEffects
import CIL.Safety.MemoryLemmas
import CIL.Safety.AccessSlices
import CIL.Safety.WordFootprint
import CIL.Safety.ExecutionInvariants
import CIL.Safety.FrameInvariants

/-!
# Method contracts

A `MethodContract` states what a method needs (`pre`), which bytes of pre-existing memory it
may change (`footprint`, enforced by `Confined`) and what it returns (`post`). `Holds` means
every checked invocation meeting `pre` returns normally within the footprint and satisfies
`post`. Callers compose through `run_call_of_contract` instead of re-executing the callee,
and `Refines` derives a weaker exported contract from a proved internal one.

The tactics at the end drive proofs: `cil_contract_steps` steps the checked interpreter
(`CIL/Safety/Execution.lean`) through a body, and `cil_contract_call` / `cil_formed_call`
discharge each call with the callee's proved contract.
-/

namespace CIL.Safety

/-- Byte `(id, offset)` lies outside every `(reference, width)` interval of `footprint`. -/
def Outside (footprint : List (Reference × Nat)) (id offset : Nat) : Prop :=
  ∀ entry ∈ footprint,
    id ≠ entry.1.allocation ∨ offset < entry.1.offset ∨ entry.1.offset + entry.2 ≤ offset

/-- What a call may change in memory that existed before it: bytes, field references and read
    authority inside `footprint`. Allocations and write authority are kept everywhere. -/
structure Confined (footprint : List (Reference × Nat)) (before after : Memory) : Prop where
  grows : before.nextIdentity ≤ after.nextIdentity
  allocations : ∀ id, id < before.nextIdentity → after.allocations id = before.allocations id
  cells : ∀ id, id < before.nextIdentity → ∀ offset, Outside footprint id offset →
    after.cells id offset = before.cells id offset
  writable : ∀ id, id < before.nextIdentity → ∀ offset,
    permitted after true ⟨id, offset⟩ = permitted before true ⟨id, offset⟩
  readable : ∀ id, id < before.nextIdentity → ∀ offset, Outside footprint id offset →
    permitted after false ⟨id, offset⟩ = permitted before false ⟨id, offset⟩
  slots : ∀ id, id < before.nextIdentity → ∀ offset, Outside footprint id offset →
    after.slots id offset = before.slots id offset

theorem Confined.refl (footprint : List (Reference × Nat)) (m : Memory) :
    Confined footprint m m :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl⟩

theorem Confined.trans {footprint : List (Reference × Nat)} {first middle last : Memory}
    (left : Confined footprint first middle) (right : Confined footprint middle last) :
    Confined footprint first last := by
  have old : ∀ {id}, id < first.nextIdentity → id < middle.nextIdentity :=
    fun bound => Nat.lt_of_lt_of_le bound left.grows
  exact ⟨Nat.le_trans left.grows right.grows,
    fun id bound => (right.allocations id (old bound)).trans (left.allocations id bound),
    fun id bound offset outside => (right.cells id (old bound) offset outside).trans
      (left.cells id bound offset outside),
    fun id bound offset =>
      (right.writable id (old bound) offset).trans (left.writable id bound offset),
    fun id bound offset outside => (right.readable id (old bound) offset outside).trans
      (left.readable id bound offset outside),
    fun id bound offset outside => (right.slots id (old bound) offset outside).trans
      (left.slots id bound offset outside)⟩

/-- A contract with a smaller footprint also holds for any larger one. -/
theorem Confined.widen {small large : List (Reference × Nat)} {before after : Memory}
    (framed : Confined small before after) (covered : ∀ entry ∈ small, entry ∈ large) :
    Confined large before after :=
  have narrow : ∀ {id offset}, Outside large id offset → Outside small id offset :=
    fun outside entry member => outside entry (covered entry member)
  ⟨framed.grows, framed.allocations,
    fun id bound offset outside => framed.cells id bound offset (narrow outside),
    framed.writable,
    fun id bound offset outside => framed.readable id bound offset (narrow outside),
    fun id bound offset outside => framed.slots id bound offset (narrow outside)⟩

/-- Memory left untouched below a watermark covering every old allocation is confined to
    any footprint. -/
theorem Confined.ofMemoryBelow {footprint : List (Reference × Nat)} {before after : Memory}
    {watermark : Nat}
    (preserved : MemoryBelow watermark before after) (covers : before.nextIdentity ≤ watermark)
    (grows : before.nextIdentity ≤ after.nextIdentity) : Confined footprint before after :=
  have old : ∀ {id}, id < before.nextIdentity → id < watermark :=
    fun bound => Nat.lt_of_lt_of_le bound covers
  ⟨grows, fun id bound => preserved.allocations id (old bound),
    fun id bound offset _ => preserved.cells id (old bound) offset,
    fun id bound offset => preserved.permissions id (old bound) offset true,
    fun id bound offset _ => preserved.permissions id (old bound) offset false,
    fun id bound offset _ => preserved.slots id (old bound) offset⟩

/-- A change confined to no storage keeps all memory that existed before it. -/
theorem Confined.nil_memoryBelow {before after : Memory} (framed : Confined [] before after) :
    MemoryBelow before.nextIdentity before after :=
  ⟨framed.allocations,
    fun id bound offset => framed.cells id bound offset (fun _ member => nomatch member),
    fun id bound offset writing => by
      cases writing
      · exact framed.readable id bound offset fun _ member => nomatch member
      · exact framed.writable id bound offset,
    fun id bound offset => framed.slots id bound offset (fun _ member => nomatch member)⟩
#print axioms Confined.nil_memoryBelow

/-- Interval `inner` lies wholly inside interval `outer` of the same allocation. -/
def Within (inner outer : Reference × Nat) : Prop :=
  inner.1.allocation = outer.1.allocation ∧ outer.1.offset ≤ inner.1.offset ∧
    inner.1.offset + inner.2 ≤ outer.1.offset + outer.2

instance (inner outer : Reference × Nat) : Decidable (Within inner outer) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A footprint whose intervals each lie inside an entry of `large` widens to `large`. -/
theorem Confined.widen_within {small large : List (Reference × Nat)} {before after : Memory}
    (framed : Confined small before after)
    (covered : ∀ entry ∈ small, ∃ outer ∈ large, Within entry outer) :
    Confined large before after :=
  have narrow : ∀ {id offset}, Outside large id offset → Outside small id offset :=
    fun outside entry member => by
    obtain ⟨outer, contains, same, start, finish⟩ := covered entry member
    rcases outside outer contains with different | below | above
    · exact Or.inl (same ▸ different)
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))
  ⟨framed.grows, framed.allocations,
    fun id bound offset outside => framed.cells id bound offset (narrow outside),
    framed.writable,
    fun id bound offset outside => framed.readable id bound offset (narrow outside),
    fun id bound offset outside => framed.slots id bound offset (narrow outside)⟩

/-- Footprint entries in identities allocated after `before`, such as a callee's locals,
    can be dropped. -/
theorem Confined.forget_fresh {fresh footprint : List (Reference × Nat)} {before after : Memory}
    (framed : Confined (fresh ++ footprint) before after)
    (young : ∀ entry ∈ fresh, before.nextIdentity ≤ entry.1.allocation) :
    Confined footprint before after :=
  have outside : ∀ {id offset}, id < before.nextIdentity → Outside footprint id offset →
      Outside (fresh ++ footprint) id offset := fun bound outside entry member =>
    (List.mem_append.mp member).elim (fun own => Or.inl (by have := young entry own; omega))
      (outside entry)
  ⟨framed.grows, framed.allocations,
    fun id bound offset o => framed.cells id bound offset (outside bound o),
    framed.writable,
    fun id bound offset o => framed.readable id bound offset (outside bound o),
    fun id bound offset o => framed.slots id bound offset (outside bound o)⟩

/-- A step that keeps all memory older than `first`, such as frame entry or teardown,
    keeps `Confined`. -/
theorem Confined.then_below {footprint : List (Reference × Nat)} {first middle last : Memory}
    (framed : Confined footprint first middle)
    (preserved : MemoryBelow first.nextIdentity middle last)
    (grows : middle.nextIdentity ≤ last.nextIdentity) : Confined footprint first last :=
  ⟨Nat.le_trans framed.grows grows,
    fun id bound => (preserved.allocations id bound).trans (framed.allocations id bound),
    fun id bound offset outside =>
      (preserved.cells id bound offset).trans (framed.cells id bound offset outside),
    fun id bound offset =>
      (preserved.permissions id bound offset true).trans (framed.writable id bound offset),
    fun id bound offset outside => (preserved.permissions id bound offset false).trans
      (framed.readable id bound offset outside),
    fun id bound offset outside =>
      (preserved.slots id bound offset).trans (framed.slots id bound offset outside)⟩

/-- Leaving a frame that owns only identities allocated after `before`, such as the callee's
    own locals, keeps `Confined`. -/
theorem Confined.after_leaveFrame {footprint : List (Reference × Nat)} {before current : Memory}
    {frame : Frame} (framed : Confined footprint before current)
    (owned : ∀ id ∈ frame.owned, before.nextIdentity ≤ id) :
    Confined footprint before (leaveFrame frame current) :=
  framed.then_below (leaveFrame_preserves_memory_below frame current _ owned)
    (Nat.le_of_eq (leaveFrame_nextIdentity frame current).symm)

#print axioms Confined.after_leaveFrame

/-- Changing the reference a field holds is confined to any footprint with an entry starting at
    that field. -/
theorem Confined.setSlot {footprint : List (Reference × Nat)} {m : Memory} {field : Reference}
    {width : Nat} (value : ManagedReference) (member : (field, width) ∈ footprint)
    (positive : 0 < width) : Confined footprint m (setSlot m field value) := by
  refine ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ => rfl, ?_⟩
  intro id _ offset outside
  simp only [CIL.Safety.setSlot]
  by_cases sameId : id = field.allocation
  · by_cases sameOffset : offset = field.offset
    · subst sameId sameOffset
      rcases outside _ member with different | below | above
      · exact absurd rfl different
      · exact absurd below (Nat.lt_irrefl _)
      · simp only at above
        omega
    · simp only [sameId, sameOffset, ite_true, ite_false]
  · simp only [sameId, ite_false]
#print axioms Confined.setSlot

/-- A checked write inside the footprint keeps every other byte and all write authority. -/
theorem Confined.write {footprint : List (Reference × Nat)} {m result : Memory} {r : Reference}
    {bytes : List (BitVec 8)} {alignment : Nat}
    (h : write m r bytes alignment = .ok result) (member : (r, bytes.length) ∈ footprint) :
    Confined footprint m result := by
  have shape := write_views_nextIdentity h
  have authority : ∀ writing q, permitted result writing q =
      permitted { m with views := ⟨r.allocation, r.offset, bytes.length, true, false⟩ :: m.views }
        writing q := by
    intro writing q
    rw [← writeViews_permitted m r bytes.length writing q]
    simp only [permitted, shape.1]
  refine ⟨Nat.le_of_eq shape.2.symm, fun id _ => by rw [write_allocations _ _ _ _ _ h],
    ?_, ?_, ?_, fun id _ offset _ => by rw [write_slots h]⟩
  · intro id _ offset outside
    exact write_outside _ _ _ _ _ _ _ h (outside _ member)
  · intro id _ offset
    rw [authority]
    simp [permitted]
  · intro id _ offset outside
    rw [authority]
    have outside := outside _ member
    simp only at outside
    rcases outside with different | before | after
    · simp [permitted, viewContains, Ne.symm different]
    · simp [permitted, viewContains, show ¬ r.offset ≤ offset by omega]
    · simp [permitted, viewContains, show ¬ offset < r.offset + bytes.length by omega]

/-- A checked write wholly inside one footprint entry is confined to that footprint. -/
theorem Confined.write_within {footprint : List (Reference × Nat)} {m result : Memory}
    {r : Reference} {bytes : List (BitVec 8)} {alignment : Nat}
    (h : CIL.Safety.write m r bytes alignment = .ok result)
    (within : ∃ entry ∈ footprint, Within (r, bytes.length) entry) :
    Confined footprint m result :=
  (Confined.write h (List.mem_singleton_self _)).widen_within
    fun _ member => List.mem_singleton.mp member ▸ within

/-- Write access to memory that existed before the call is unchanged. -/
theorem Confined.access_write {footprint : List (Reference × Nat)} {before after : Memory}
    (framed : Confined footprint before after) (r : Reference)
    (old : r.allocation < before.nextIdentity) (width alignment : Nat) :
    access after r width alignment true = access before r width alignment true := by
  have same : ∀ i, permitted after true { r with offset := r.offset + i } =
      permitted before true { r with offset := r.offset + i } := fun i => framed.writable _ old _
  simp only [CIL.Safety.access, form, liveAllocation, framed.allocations _ old, same]

/-- A read wholly outside the footprint sees the same bytes and authority. -/
theorem Confined.read_eq {footprint : List (Reference × Nat)} {before after : Memory}
    (framed : Confined footprint before after) (r : Reference)
    (old : r.allocation < before.nextIdentity) (width alignment : Nat)
    (outside : ∀ i < width, Outside footprint r.allocation (r.offset + i)) :
    read after r width alignment = read before r width alignment := by
  have authority :
      (List.range width).all (fun i => permitted after false { r with offset := r.offset + i }) =
        (List.range width).all
          (fun i => permitted before false { r with offset := r.offset + i }) := by
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_range]
    constructor
    · intro allowed i bound
      rw [← framed.readable _ old _ (outside i bound)]
      exact allowed i bound
    · intro allowed i bound
      rw [framed.readable _ old _ (outside i bound)]
      exact allowed i bound
  have cells : (List.range width).map (fun i => after.cells r.allocation (r.offset + i)) =
      (List.range width).map (fun i => before.cells r.allocation (r.offset + i)) := by
    apply List.map_congr_left
    intro i member
    exact framed.cells _ old _ (outside i (List.mem_range.mp member))
  simp only [CIL.Safety.read, CIL.Safety.access, form, liveAllocation, framed.allocations _ old,
    authority, cells]

/-- A word disjoint from `r` is outside the one-word footprint at `r`. -/
theorem WordsDisjoint.outside {r q : Reference} (disjoint : WordsDisjoint r q) :
    ∀ i < 8, Outside [(r, 8)] q.allocation (q.offset + i) := by
  intro i bound entry member
  simp only [List.mem_singleton] at member
  subst member
  rcases disjoint with different | after | before
  · exact Or.inl (Ne.symm different)
  · exact Or.inr (Or.inr (by simp only; omega))
  · exact Or.inr (Or.inl (by simp only; omega))

/-- Every byte is outside the empty footprint. -/
@[simp] theorem Outside.nil (id offset : Nat) : Outside [] id offset :=
  fun _ member => nomatch member

/-- A byte is outside a footprint iff it misses the head interval and is outside the rest. -/
@[simp] theorem Outside.cons {entry : Reference × Nat} {rest : List (Reference × Nat)}
    {id offset : Nat} :
    Outside (entry :: rest) id offset ↔
      (id ≠ entry.1.allocation ∨ offset < entry.1.offset ∨ entry.1.offset + entry.2 ≤ offset) ∧
        Outside rest id offset :=
  List.forall_mem_cons

/-- A byte outside the word at `r` and outside `rest` is outside `(r, 8) :: rest`. -/
theorem Outside.word {r : Reference} {rest : List (Reference × Nat)} {id offset : Nat}
    (word : OutsideWord r id offset) (outside : Outside rest id offset) :
    Outside ((r, 8) :: rest) id offset :=
  Outside.cons.mpr ⟨word, outside⟩

/-- Interval `(r, width)` shares no byte with interval `entry`. -/
def Apart (r : Reference) (width : Nat) (entry : Reference × Nat) : Prop :=
  r.allocation ≠ entry.1.allocation ∨ r.offset + width ≤ entry.1.offset ∨
    entry.1.offset + entry.2 ≤ r.offset

/-- Every byte of an interval apart from each footprint entry is outside the footprint. -/
theorem Outside.of_apart {footprint : List (Reference × Nat)} {r : Reference} {width : Nat}
    (apart : ∀ entry ∈ footprint, Apart r width entry) :
    ∀ i < width, Outside footprint r.allocation (r.offset + i) := by
  intro i bound
  induction footprint with
  | nil => exact Outside.nil _ _
  | cons entry rest rest_outside =>
    obtain ⟨head, tail⟩ := List.forall_mem_cons.mp apart
    refine Outside.cons.mpr ⟨?_, rest_outside tail⟩
    rcases head with different | below | above
    · exact Or.inl different
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

/-- A checked read of memory older than the call, apart from every footprint entry, is
    unchanged. -/
theorem Confined.read_apart {footprint : List (Reference × Nat)} {before after : Memory}
    {r : Reference} {width alignment : Nat} {bytes : List (BitVec 8)}
    (framed : Confined footprint before after)
    (formed : before.WellFormed) (loaded : read before r width alignment = .ok bytes)
    (apart : ∀ entry ∈ footprint, Apart r width entry) : read after r width alignment = .ok bytes :=
  (framed.read_eq r (formed.access_bound (read_access loaded)) width alignment
    (Outside.of_apart apart)).trans loaded

/-- An old allocation that no footprint entry names keeps every byte. -/
theorem Confined.cells_apart {footprint : List (Reference × Nat)} {before after : Memory}
    {id : Nat}
    (framed : Confined footprint before after) (old : id < before.nextIdentity)
    (separate : ∀ entry ∈ footprint, id ≠ entry.1.allocation) (offset : Nat) :
    after.cells id offset = before.cells id offset :=
  framed.cells id old offset fun entry member => Or.inl (separate entry member)

/-- A typed method contract. `pre` carries formation, authority and the permitted
    aliasing; `footprint` bounds the bytes of earlier memory the method may change.
    `post` speaks of an `Output` that `results` encodes; by default the returned values. -/
structure MethodContract (Input : Type) (Output : Type := List Value) where
  args : Input → List Value
  results : Output → List Value := by exact fun values => values
  pre : Input → Memory → Prop
  footprint : Input → List (Reference × Nat)
  post : Input → Memory → Memory → Output → Prop

/-- The returned values encode an output satisfying `post`. -/
def MethodContract.Returns {Input Output : Type} (c : MethodContract Input Output)
    (input : Input) (initial final : Memory) (values : List Value) : Prop :=
  ∃ out, values = c.results out ∧ c.post input initial final out

/-- Normal return within the footprint satisfying `post`, for every input meeting `pre`.
    Fuel stays existential, so callers never depend on the callee's step count. -/
def MethodContract.Holds {Input Output : Type} (c : MethodContract Input Output)
    (program : CIL.Program) (method : Nat) : Prop :=
  ∀ input initial, c.pre input initial →
    ∃ fuel final values,
      invoke program fuel method (c.args input) initial = .ok (final, values) ∧
      Confined (c.footprint input) initial final ∧ c.Returns input initial final values

/-- A contract is `Ensures` at each input, with the footprint as part of the postcondition. -/
theorem MethodContract.Holds.ensures {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method : Nat} (holds : c.Holds program method) (input : Input) :
    Ensures program method (fun args m => args = c.args input ∧ c.pre input m)
      (fun _ initial final values =>
        Confined (c.footprint input) initial final ∧ c.Returns input initial final values) := by
  rintro args initial ⟨rfl, permitted⟩
  exact holds input initial permitted

/-- What one invocation of `method` established under contract `c` at `input`: it ran from
    `before` to `final`, returned the encoding of `output`, changed only the footprint and met
    `post`. Proofs select these facts by name, so a fact added here changes no proof. -/
structure CallResult {Input Output : Type} (c : MethodContract Input Output)
    (program : CIL.Program) (method : Nat) (input : Input) (before final : Memory)
    (output : Output) : Prop where
  /-- Some fuel runs the method from `before` to `final`, returning the encoding of `output`. -/
  invoked : ∃ fuel,
    invoke program fuel method (c.args input) before = .ok (final, c.results output)
  /-- Memory that existed in `before` changed only inside the contract's footprint. -/
  framed : Confined (c.footprint input) before final
  /-- The contract's postcondition for `output`. -/
  post : c.post input before final output

/-- Close the goal `Holds` leaves for one input from the final memory and output, named, with the
    invocation, footprint and postcondition they satisfy. -/
theorem MethodContract.Holds.intro {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method : Nat} {input : Input} {initial : Memory}
    (final : Memory) (output : Output)
    (invoked : ∃ fuel,
      invoke program fuel method (c.args input) initial = .ok (final, c.results output))
    (framed : Confined (c.footprint input) initial final)
    (post : c.post input initial final output) :
    ∃ fuel final values,
      invoke program fuel method (c.args input) initial = .ok (final, values) ∧
      Confined (c.footprint input) initial final ∧ c.Returns input initial final values :=
  invoked.elim fun fuel ran => ⟨fuel, final, c.results output, ran, framed, output, rfl, post⟩

/-- What a proved contract establishes for an input meeting `pre`: a final memory and output
    with their `CallResult`. -/
theorem MethodContract.Holds.result {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method : Nat} (holds : c.Holds program method) (input : Input)
    {initial : Memory} (permitted : c.pre input initial) :
    ∃ final output, CallResult c program method input initial final output := by
  obtain ⟨fuel, final, _, invoked, framed, output, rfl, post⟩ := holds input initial permitted
  exact ⟨final, output, { invoked := ⟨fuel, invoked⟩, framed, post }⟩

#print axioms MethodContract.Holds.intro
#print axioms MethodContract.Holds.result

/-- Compose a fetched call through the callee's contract instead of its body. The
    continuation receives the callee's final memory and typed output with their `CallResult`. -/
theorem run_call_of_contract {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (continuation : ∀ final output,
      CallResult c program callee input updated final output →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame (c.results output ++ rest) final =
          .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧
        post result returned := by
  subst encoded
  obtain ⟨final, output, call⟩ := holds.result input permitted
  obtain ⟨parentFuel, result, returned, resumed, finished⟩ := continuation final output call
  obtain ⟨fuel, composed⟩ :=
    run_call_exists methodFound instructionFound stepped call.invoked ⟨parentFuel, resumed⟩
  exact ⟨fuel, result, returned, composed, finished⟩

/-- Compose a separately proved child invocation with a caller postcondition. -/
theorem run_call_post {program : CIL.Program} {method pc callee : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack arguments rest values : List Value}
    {frame : Frame} {memory updated final : Memory} {post : Memory → List Value → Prop}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory =
      .ok (.call callee arguments rest updated))
    (child : ∃ fuel, invoke program fuel callee arguments updated = .ok (final, values))
    (continuation : ∃ fuel result returned,
      run program fuel method (pc + 1) args frame (values ++ rest) final =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧
        post result returned := by
  obtain ⟨parentFuel, result, returned, resumed, satisfied⟩ := continuation
  obtain ⟨fuel, composed⟩ := run_call_exists methodFound instructionFound stepped child
    ⟨parentFuel, resumed⟩
  exact ⟨fuel, result, returned, composed, satisfied⟩
#print axioms run_call_post

/-- A successful call from a well-formed memory returns a well-formed memory and keeps the static
    world and catalog agreement, whatever the callee's contract states. -/
theorem call_frame_invariants {program : CIL.Program} {method pc callee fuel : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack arguments rest values : List Value}
    {frame : Frame} {memory updated final : Memory}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (formed : memory.WellFormed)
    (invoked : invoke program fuel callee arguments updated = .ok (final, values)) :
    FrameInvariants program memory final := by
  have called :
      ProgramStep program method pc args frame stack memory (.call callee arguments rest updated) :=
    ⟨body, op, methodFound, instructionFound, stepped⟩
  have entered : updated.WellFormed :=
    programStep_preserves_wellFormed _ _ _ _ _ _ _ _ formed called
  exact {
    formed := invoke_preserves_wellFormed _ _ _ _ _ _ _ entered invoked
    staticWorld := fun world => invoke_preserves_static_world _ _ _ _ _ _ _ entered
      (programStep_preserves_static_world called formed world) invoked
    classes := fun _ sites consistent => invoke_preserves_classes sites
      (programStep_preserves_classes sites consistent called) invoked }

/-- `run_call_of_contract` from a well-formed memory: the continuation also receives the
    `FrameInvariants` the call keeps from the caller's memory to the callee's final memory. -/
theorem run_call_of_contract_formed {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (formed : memory.WellFormed)
    (continuation : ∀ final output,
      CallResult c program callee input updated final output →
      FrameInvariants program memory final →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame (c.results output ++ rest) final =
          .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧
        post result returned := by
  subst encoded
  exact run_call_of_contract holds input methodFound instructionFound stepped rfl permitted
    fun final output call => call.invoked.elim fun _ invoked =>
      continuation final output call
        (call_frame_invariants methodFound instructionFound stepped formed invoked)

/-- Some fuel runs to a successful return satisfying `post` when the fetched instruction
    returns checked values that satisfy it. -/
theorem run_return_exists {program : CIL.Program} {method pc : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.returned values updated))
    (checked : values.mapM (checkedValue (leaveFrame frame updated)) = .ok values)
    (satisfied : post (leaveFrame frame updated) values) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧
        post result returned :=
  ⟨1, _, _, run_return (fuel := 0) methodFound instructionFound stepped checked, satisfied⟩

/-- Reduces an invocation goal to running the body from pc 0 in the frame `enterFrame`
    builds for checked arguments. -/
theorem invoke_exists_of_run {program : CIL.Program} {method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory entered : Memory}
    {post : Memory → List Value → Prop}
    (found : program[method]? = some body)
    (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (executed : ∃ fuel result returned,
      run program fuel method 0 args frame [] entered = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      invoke program fuel method args memory = .ok (result, returned) ∧ post result returned := by
  obtain ⟨fuel, result, returned, ran, satisfied⟩ := executed
  exact ⟨fuel, result, returned, invoke_of_run found checked setup ran, satisfied⟩

/-- Successful invocations agree at every fuel, so a computed run refutes a contract. -/
theorem invoke_ok_unique {program : CIL.Program} {method left right : Nat} {args : List Value}
    {memory : Memory} {first second : Memory × List Value}
    (one : invoke program left method args memory = .ok first)
    (other : invoke program right method args memory = .ok second) : first = second := by
  have up := invoke_mono program left right method args memory (.ok first) trivial one
  have down := invoke_mono program right left method args memory (.ok second) trivial other
  rw [Nat.add_comm] at down
  exact Except.ok.inj (up.symm.trans down)

/-- One computed observation of a successful invocation fixes that observation for every fuel
    whose invocation succeeds, so a refutation compares only the observed part, such as the
    returned values. -/
theorem invoke_ok_observation_unique {α : Type} {program : CIL.Program}
    {method fuel witnessFuel : Nat}
    {args : List Value} {memory : Memory} (observe : Memory × List Value → α)
    {outcome : Memory × List Value} {observed : α}
    (witness : (invoke program witnessFuel method args memory).map observe = .ok observed)
    (normal : invoke program fuel method args memory = .ok outcome) :
    observe outcome = observed := by
  cases execution : invoke program witnessFuel method args memory with
  | error fault => simp [execution, Except.map] at witness
  | ok actual =>
    rw [invoke_ok_unique normal execution]
    simpa [execution, Except.map] using witness

theorem Within.refl (entry : Reference × Nat) : Within entry entry :=
  ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem Within.trans {inner middle outer : Reference × Nat} (left : Within inner middle)
    (right : Within middle outer) : Within inner outer :=
  ⟨left.1.trans right.1, Nat.le_trans right.2.1 left.2.1, Nat.le_trans left.2.2 right.2.2⟩

/-- A callee confined to fresh frame storage and to entries inside `footprint`, run between a
    frame entry and exit that keep memory below the caller's `nextIdentity`, is confined to
    `footprint` as the caller sees it. -/
theorem Confined.across_frame {footprint inner : List (Reference × Nat)}
    {initial entered final left : Memory}
    (entryBelow : MemoryBelow initial.nextIdentity initial entered)
    (enterGrows : initial.nextIdentity ≤ entered.nextIdentity)
    (framed : Confined inner entered final)
    (exitBelow : MemoryBelow initial.nextIdentity final left)
    (exitGrows : final.nextIdentity ≤ left.nextIdentity)
    (covered : ∀ entry ∈ inner,
      initial.nextIdentity ≤ entry.1.allocation ∨ ∃ outer ∈ footprint, Within entry outer) :
    Confined footprint initial left := by
  have old : ∀ {id}, id < initial.nextIdentity → id < entered.nextIdentity :=
    fun bound => Nat.lt_of_lt_of_le bound enterGrows
  have narrow : ∀ {id offset}, id < initial.nextIdentity → Outside footprint id offset →
      Outside inner id offset := fun bound outside entry member => by
    rcases covered entry member with fresh | ⟨outer, contains, same, start, finish⟩
    · exact Or.inl (by omega)
    · rcases outside outer contains with different | below | above
      · exact Or.inl (same ▸ different)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
  exact ⟨Nat.le_trans enterGrows (Nat.le_trans framed.grows exitGrows),
    fun id bound => (exitBelow.allocations id bound).trans
      ((framed.allocations id (old bound)).trans (entryBelow.allocations id bound)),
    fun id bound offset outside => (exitBelow.cells id bound offset).trans
      ((framed.cells id (old bound) offset (narrow bound outside)).trans
        (entryBelow.cells id bound offset)),
    fun id bound offset => (exitBelow.permissions id bound offset true).trans
      ((framed.writable id (old bound) offset).trans
        (entryBelow.permissions id bound offset true)),
    fun id bound offset outside => (exitBelow.permissions id bound offset false).trans
      ((framed.readable id (old bound) offset (narrow bound outside)).trans
        (entryBelow.permissions id bound offset false)),
    fun id bound offset outside => (exitBelow.slots id bound offset).trans
      ((framed.slots id (old bound) offset (narrow bound outside)).trans
        (entryBelow.slots id bound offset))⟩

#print axioms Confined.across_frame

/-- `exported` follows from `internal`: same encodings, weaker pre, covering footprint,
    implied post. -/
structure MethodContract.Refines {Input Output : Type}
    (internal exported : MethodContract Input Output) : Prop where
  args : ∀ input, exported.args input = internal.args input
  results : ∀ out, exported.results out = internal.results out
  pre : ∀ input initial, exported.pre input initial → internal.pre input initial
  footprint : ∀ input initial, exported.pre input initial →
    ∀ entry ∈ internal.footprint input, ∃ outer ∈ exported.footprint input, Within entry outer
  /-- The internal footprint's `Confined` is available, so the exported post may state frame
      facts. -/
  post : ∀ input initial final out, exported.pre input initial →
    Confined (internal.footprint input) initial final →
    internal.post input initial final out → exported.post input initial final out

theorem MethodContract.Refines.refl {Input Output : Type} (c : MethodContract Input Output) :
    c.Refines c :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ permitted => permitted,
    fun _ _ _ entry member => ⟨entry, member, Within.refl entry⟩,
    fun _ _ _ _ _ _ satisfied => satisfied⟩

theorem MethodContract.Refines.trans {Input Output : Type}
    {first middle last : MethodContract Input Output}
    (left : first.Refines middle) (right : middle.Refines last) : first.Refines last where
  args input := (right.args input).trans (left.args input)
  results out := (right.results out).trans (left.results out)
  pre _ _ permitted := left.pre _ _ (right.pre _ _ permitted)
  footprint _ _ permitted entry member := by
    obtain ⟨between, inside, within⟩ := left.footprint _ _ (right.pre _ _ permitted) entry member
    obtain ⟨outer, contains, enclosed⟩ := right.footprint _ _ permitted between inside
    exact ⟨outer, contains, within.trans enclosed⟩
  post _ _ _ _ permitted framed satisfied :=
    right.post _ _ _ _ permitted
      (framed.widen_within (left.footprint _ _ (right.pre _ _ permitted)))
      (left.post _ _ _ _ (right.pre _ _ permitted) framed satisfied)

/-- Derive a contract from a proved one it refines; the method is neither unfolded nor
    executed. -/
theorem MethodContract.Holds.weaken {Input Output : Type}
    {internal exported : MethodContract Input Output}
    {program : CIL.Program} {method : Nat} (holds : internal.Holds program method)
    (refines : internal.Refines exported) : exported.Holds program method := by
  intro input initial permitted
  obtain ⟨fuel, final, values, invoked, framed, out, encoded, satisfied⟩ :=
    holds input initial (refines.pre _ _ permitted)
  refine ⟨fuel, final, values, ?_, framed.widen_within (refines.footprint _ _ permitted),
    out, ?_, refines.post _ _ _ _ permitted framed satisfied⟩
  · rw [refines.args]; exact invoked
  · rw [refines.results]; exact encoded

#print axioms Within.trans
#print axioms MethodContract.Refines.trans
#print axioms MethodContract.Holds.weaken
#print axioms Confined.forget_fresh
#print axioms Confined.then_below
#print axioms Confined.write
#print axioms Confined.widen_within
#print axioms Confined.write_within
#print axioms Confined.read_eq
#print axioms Outside.nil
#print axioms Outside.cons
#print axioms Outside.word
#print axioms Outside.of_apart
#print axioms Confined.read_apart
#print axioms Confined.cells_apart
#print axioms run_call_of_contract
#print axioms call_frame_invariants
#print axioms run_call_of_contract_formed
#print axioms invoke_ok_unique
#print axioms invoke_ok_observation_unique

/-- Opens a contract goal: tidies the stack and, for an `invoke` goal, enters the frame via
    `invoke_exists_of_run` so stepping can start at pc 0. Used by `cil_contract_steps`. -/
macro "cil_contract_prepare" "[" facts:term,* "]" : tactic =>
  `(tactic| (
    -- A contract continuation resumes at `pc + 1` on `results ++ rest` with projected inputs.
    cil_unfold_contracts
    try dsimp only [Nat.reduceAdd]
    cil_stack_cleanup
    try (cil_strict refine CIL.Safety.invoke_exists_of_run
           (by cil_lookup [$[$facts:term],*])
           (by cil_checked_side [$[$facts:term],*])
           (by cil_checked_side [$[$facts:term],*]) ?_)))

/-- One contract step, selecting the composition rule from the fetched opcode. -/
syntax "cil_contract_step" "[" term,* "]" : tactic

open Lean in
/-- Proved method interfaces available to call stepping across imported modules. -/
initialize contractTheorems : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[] }

open Lean in
/-- Register a theorem whose conclusion is a method contract for its bound callee. -/
initialize registerBuiltinAttribute {
  name := `cil_contract
  descr := "A proved method contract available to checked call composition"
  add := fun name stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == .global do throwError "cil_contract must be global"
    let .thmInfo declaration ← getConstInfo name
      | throwError "cil_contract requires a theorem"
    unless declaration.type.getForallBody.isAppOfArity ``CIL.Safety.MethodContract.Holds 5 do
      throwError "cil_contract requires a MethodContract.Holds conclusion"
    modifyEnv fun environment => contractTheorems.addEntry environment name }

open Lean Elab Tactic Meta in
/-- Recognize successful invocation evidence without elaborating unrelated local hypotheses. -/
def cilInvocationEvidence (type : Expr) : Bool :=
  let type := type.consumeMData
  let invocation := fun statement : Expr =>
    statement.eq?.any fun (_, left, _) => left.isAppOf ``CIL.Safety.invoke
  type.isAppOf `CIL.Safety.InvocationCertificate || type.isAppOf ``CIL.Safety.CallResult ||
    invocation type ||
    (type.isAppOfArity ``Exists 2 && match type.appArg! with
      | .lam _ _ body _ => invocation body
      | _ => false)

open Lean Elab Tactic Meta in
/-- Use supplied or local successful invocation evidence at the fetched call. -/
def cilContractChild (methodFound instructionFound : Term) (facts : Array Term) : TacticM Unit := do
  let mut candidates := facts
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if cilInvocationEvidence declaration.type then
        candidates := candidates.push (← Term.exprToSyntax declaration.toExpr)
  for candidate in candidates do
    let saved ← saveState
    try
      let proof ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm candidate none
      let type ← instantiateMVars (← inferType proof)
      unless cilInvocationEvidence type do throwError "Not a successful invocation fact"
      let child ← if type.isAppOf `CIL.Safety.InvocationCertificate then
        `(⟨_, ($candidate).1⟩)
        else if type.isAppOf ``CIL.Safety.CallResult then `(($candidate).invoked)
        else if type.isAppOfArity ``Exists 2 then pure candidate
        else `(⟨_, $candidate⟩)
      evalTactic (← `(tactic| (
        cil_strict refine CIL.Safety.run_call_post $methodFound $instructionFound
          (by cil_checked_step_normalized [$facts,*]) $child ?_
        cil_stack_cleanup)))
      return
    catch _ => saved.restore
  throwError "Call requires a proved contract or matching child invocation"

open Lean Meta in
/-- A fresh contract input whose single constructor, and the pair constructor of each pair inside
    it, is applied to fresh fields, so the encoded call arguments determine every field. -/
partial def cilContractInput (inputType : Expr) : MetaM Expr := do
  let fresh ← mkFreshExprMVar inputType
  let some name := (← whnf inputType).getAppFn.constName? | return fresh
  let .inductInfo info ← getConstInfo name | return fresh
  unless info.ctors.length == 1 do return fresh
  let constructor ← mkConstWithFreshMVarLevels info.ctors.head!
  let (arguments, _, result) ← forallMetaTelescopeReducing (← inferType constructor)
  unless ← isDefEq result inputType do return fresh
  let mut fields := #[]
  for index in [:arguments.size] do
    let argument := arguments[index]!
    let type ← instantiateMVars (← inferType argument)
    if index ≥ info.numParams && (← whnf type).isAppOfArity ``Prod 2 then
      fields := fields.push (← cilContractInput type)
    else fields := fields.push argument
  return mkAppN constructor fields

open Lean Meta in
/-- The names a composed call takes for its final memory, typed output and `CallResult`:
    `called`, `output` and `call`, or with the first suffix `_1`, `_2` that leaves all three
    unused, so one call's names share a suffix. -/
def cilCallNames : MetaM (Ident × Ident × Ident) := do
  let context ← getLCtx
  let named (index : Nat) (base : String) : Name :=
    Name.mkSimple (if index == 0 then base else s!"{base}_{index}")
  let mut index := 0
  while ["called", "output", "call"].any fun base => context.usesUserName (named index base) do
    index := index + 1
  return (mkIdent (named index "called"), mkIdent (named index "output"),
    mkIdent (named index "call"))

open Lean Elab Tactic Meta in
/-- Apply a matching contract and expose its `CallResult` to the caller continuation. -/
def cilContractApply (methodFound instructionFound : Term) (facts : Array Term) : TacticM Unit := do
  let mut candidates := facts
  for name in contractTheorems.getState (← getEnv) do
    candidates := candidates.push (mkIdent name)
  for candidate in candidates do
    let saved ← saveState
    try
      let proof ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTerm candidate none
      let proofType ← instantiateMVars (← inferType proof)
      unless proofType.getForallBody.isAppOfArity ``CIL.Safety.MethodContract.Holds 5 do
        throwError "Not a method contract"
      let (parameters, _, type) ← forallMetaTelescope proofType
      let type ← instantiateMVars type
      unless type.isAppOfArity ``CIL.Safety.MethodContract.Holds 5 do
        throwError "Not a method contract"
      let input ← cilContractInput type.getAppArgs[0]!
      let inputSyntax ← Term.exprToSyntax input
      let proofSyntax ← Term.exprToSyntax (mkAppN proof parameters)
      let siblings := (← getGoals).tail!
      let tag ← (← getMainGoal).getTag
      evalTactic (← `(tactic| (
        cil_strict refine CIL.Safety.run_call_of_contract $proofSyntax $inputSyntax
          $methodFound $instructionFound
          (by cil_checked_step_normalized [$facts,*]) (by rfl) ?_ ?_)))
      for parameter in parameters do
        unless ← parameter.mvarId!.isAssigned do
          let remaining ← Tactic.run parameter.mvarId! (evalTactic (← `(tactic|
            first | assumption | cil_lookup [$facts,*])))
          unless remaining.isEmpty do throwError "The contract binding could not be established"
      let pending ← getGoals
      unless pending.length == siblings.length + 2 do
        throwError "The contract input could not be inferred from the call arguments"
      let permitted := pending[0]!
      let continuation := pending[1]!
      permitted.setTag (preconditionTag type)
      continuation.setTag tag
      let beforePrecondition ← saveState
      try
        evalTactic (← `(tactic| focus
          first | assumption | trivial | (simp [$[$facts:term],*]; done)))
      catch _ => beforePrecondition.restore
      if (← instantiateMVars input).hasExprMVar then
        throwError "The contract input has fields not determined by the call or precondition"
      setGoals [continuation]
      let (called, output, call) ← continuation.withContext cilCallNames
      evalTactic (← `(tactic| (
        intro $called:ident $output:ident $call:ident
        cil_unfold_contracts
        cil_stack_cleanup)))
      let remaining ← getGoals
      setGoals ((if ← permitted.isAssigned then [] else [permitted]) ++ remaining ++ siblings)
      return
    catch _ => saved.restore
  throwError "No matching contract with an established precondition"

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_contract_step [$facts:term,*]) => withMainContext do
    let (methodFound, instructionFound, operation) ←
      cilFetchedOp ``CIL.Safety.run_next_exists some 4 facts.getElems
    if callsCallee operation then
      let saved ← saveState
      try cilContractApply methodFound instructionFound facts.getElems
      catch _ =>
        saved.restore
        cilContractChild methodFound instructionFound facts.getElems
      return
    if operation == ``CIL.Op.ret then
      evalTactic (← `(tactic| cil_strict refine CIL.Safety.run_return_exists
        $methodFound $instructionFound
        (by cil_checked_step_normalized [$[$facts:term],*])
        (by cil_checked_side [$[$facts:term],*]) ?_))
      -- What is left at a return is the method's postcondition, of the memory the body left
      -- when the frame owns nothing.
      evalTactic (← `(tactic| cil_frame_exit))
      (← getMainGoal).setTag `postcondition
      return
    evalTactic (←
      `(tactic| (
        cil_strict refine CIL.Safety.run_next_exists (post := _)
          $methodFound $instructionFound
          (by cil_checked_step_normalized [$[$facts:term],*]) ?_
        cil_stack_cleanup)))

/-- Step a goal `∃ fuel result returned, run ... ∧ post` through checked instructions,
    composing calls with registered contracts or child evidence. Each composed call names its
    final memory `called`, its typed output `output` and its `CallResult` `call`, all three
    with the suffix `_1`, `_2` once a name is taken. Unmatched calls and the postcondition at
    each return remain explicit goals, a callee's precondition tagged `precondition` and the
    postcondition `postcondition`. -/
syntax "cil_contract_steps" "[" term,* "]" : tactic
/-- As `cil_contract_steps`, naming the first call it composes: its final memory, typed output
    and `CallResult` take the three names given. Fails when it composes no call. -/
syntax "cil_contract_steps" "[" term,* "]" " with " ident ident ident : tactic
/-- As `cil_contract_steps`, but stop silently after at most `count` steps. -/
syntax "cil_contract_steps" num "[" term,* "]" : tactic
/-- As `cil_contract_steps`, but stop silently once `continuation` closes the goal. -/
syntax "cil_contract_steps" "[" term,* "]" " until " term : tactic

open Lean Elab Tactic Meta in
/-- In each goal, give the earliest `CallResult` hypothesis not among `before`, and the final
    memory and output it states when they are variables, the names `called`, `output` and
    `call`; whether any goal had one. -/
def cilNameCall (before : Array FVarId) (called output call : Name) : TacticM Bool := do
  let mut found := false
  let mut goals := #[]
  for goal in ← getGoals do
    let renamed ← goal.withContext do
      for declaration in ← getLCtx do
        if declaration.isImplementationDetail || before.contains declaration.fvarId then continue
        let stated := (← instantiateMVars declaration.type).consumeMData
        unless stated.isAppOf ``CIL.Safety.CallResult do continue
        let arguments := stated.getAppArgs
        let mut current := goal
        if let some (.fvar final) := arguments[arguments.size - 2]? then
          current ← current.rename final called
        if let some (.fvar result) := arguments.back? then current ← current.rename result output
        return some (← current.rename declaration.fvarId call)
      return none
    found := found || renamed.isSome
    goals := goals.push (renamed.getD goal)
  setGoals goals.toList
  return found

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_contract_steps [$facts:term,*] with $called:ident $output:ident $call:ident) =>
    withMainContext do
    let before := (← getLCtx).getFVarIds
    evalTactic (← `(tactic| cil_contract_steps [$facts,*]))
    unless ← cilNameCall before called.getId output.getId call.getId do
      throwError "cil_contract_steps composed no call to name"
  | `(tactic| cil_contract_steps [$facts:term,*]) => do
    let config ← `(Lean.Parser.Tactic.optConfig|)
    let prepared ← normaliseStepFacts config facts.getElems
    withMainContext <| evalTactic (← `(tactic| (
      cil_contract_prepare [$[$prepared:term],*]
      cil_steps_from "cil_contract_steps took no step: the method or instruction lookup, or the \
        first step, did not close; pass the lookup hypothesis, feature facts or step facts"
        cil_contract_step [$[$prepared:term],*])))
  | `(tactic| cil_contract_steps $count:num [$facts:term,*]) => do
    let config ← `(Lean.Parser.Tactic.optConfig|)
    let prepared ← normaliseStepFacts config facts.getElems
    withMainContext <| evalTactic (← `(tactic| cil_contract_prepare [$[$prepared:term],*]))
    let next ← `(tactic| cil_contract_step [$[$prepared:term],*])
    for _ in [:count.getNat] do
      let saved ← saveState
      try
        evalTactic next
      catch _ =>
        saved.restore
        break
  | `(tactic| cil_contract_steps [$facts:term,*] until $continuation) => do
    let config ← `(Lean.Parser.Tactic.optConfig|)
    let prepared ← normaliseStepFacts config facts.getElems
    withMainContext <| evalTactic (← `(tactic| (first
      | (cil_strict exact $continuation)
      | (
        cil_contract_prepare [$[$prepared:term],*]
        repeat first
        | (cil_strict exact $continuation)
        | cil_contract_step [$[$prepared:term],*]))))

/-- Apply a proved contract at the fetched call, optionally checked against a `bind_call`
    site: leaves the `precondition`, then the continuation over the callee's final memory,
    typed output and `CallResult`. -/
syntax "cil_contract_call" term:max term:max (" at " ident)? "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_contract_call $holds $input [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.run_call_of_contract $holds $input
      (by cil_lookup [$[$facts:term],*])
      (by cil_lookup [$[$facts:term],*])
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?precondition ?_
    cil_name_obligations $holds))
  | `(tactic| cil_contract_call $holds $input at $site:ident [$facts:term,*]) =>
  `(tactic| (
    -- The site fixes the body, so the lookup may close during simplification.
    refine CIL.Safety.run_call_of_contract $holds $input
      (by cil_lookup [$[$facts:term],*]) $(Lean.mkIdent (site.getId ++ `call))
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?precondition ?_
    cil_name_obligations $holds))

/-- `cil_contract_call` through `run_call_of_contract_formed`: leaves the `precondition`,
    the caller memory's `wellFormed`, then the continuation, which also takes the call's
    `FrameInvariants`. -/
syntax "cil_formed_call" term:max term:max (" at " ident)? "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_formed_call $holds $input [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.run_call_of_contract_formed $holds $input
      (by cil_lookup [$[$facts:term],*])
      (by cil_lookup [$[$facts:term],*])
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?precondition ?wellFormed ?_
    cil_name_obligations $holds))
  | `(tactic| cil_formed_call $holds $input at $site:ident [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.run_call_of_contract_formed $holds $input
      (by cil_lookup [$[$facts:term],*]) $(Lean.mkIdent (site.getId ++ `call))
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?precondition ?wellFormed ?_
    cil_name_obligations $holds))

end CIL.Safety
