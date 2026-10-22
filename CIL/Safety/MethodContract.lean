import CIL.Verification
import CIL.Safety.SymbolicExecution
import CIL.Safety.MemoryBelow
import CIL.Safety.ViewReuse
import CIL.Safety.WriteEffects
import CIL.Safety.MemoryLemmas
import CIL.Safety.AccessSlices
import CIL.Safety.WordFootprint
import CIL.Safety.ExecutionInvariants
import CIL.Safety.ExecutionStaticWorld

namespace CIL.Safety

/-- Byte `(id, offset)` lies outside every `(reference, width)` interval of `footprint`. -/
def Outside (footprint : List (Reference × Nat)) (id offset : Nat) : Prop :=
  ∀ entry ∈ footprint, id ≠ entry.1.allocation ∨ offset < entry.1.offset ∨ entry.1.offset + entry.2 ≤ offset

/-- What a call may change in memory that existed before it: bytes and read authority
    inside `footprint`. Allocations and write authority are kept everywhere. -/
structure Confined (footprint : List (Reference × Nat)) (before after : Memory) : Prop where
  grows : before.nextIdentity ≤ after.nextIdentity
  allocations : ∀ id, id < before.nextIdentity → after.allocations id = before.allocations id
  cells : ∀ id, id < before.nextIdentity → ∀ offset, Outside footprint id offset →
    after.cells id offset = before.cells id offset
  writable : ∀ id, id < before.nextIdentity → ∀ offset,
    permitted after true ⟨id, offset⟩ = permitted before true ⟨id, offset⟩
  readable : ∀ id, id < before.nextIdentity → ∀ offset, Outside footprint id offset →
    permitted after false ⟨id, offset⟩ = permitted before false ⟨id, offset⟩

theorem Confined.refl (footprint : List (Reference × Nat)) (m : Memory) : Confined footprint m m :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem Confined.trans {footprint : List (Reference × Nat)} {first middle last : Memory}
    (left : Confined footprint first middle) (right : Confined footprint middle last) :
    Confined footprint first last := by
  have old : ∀ {id}, id < first.nextIdentity → id < middle.nextIdentity :=
    fun bound => Nat.lt_of_lt_of_le bound left.grows
  exact ⟨Nat.le_trans left.grows right.grows,
    fun id bound => (right.allocations id (old bound)).trans (left.allocations id bound),
    fun id bound offset outside => (right.cells id (old bound) offset outside).trans
      (left.cells id bound offset outside),
    fun id bound offset => (right.writable id (old bound) offset).trans (left.writable id bound offset),
    fun id bound offset outside => (right.readable id (old bound) offset outside).trans
      (left.readable id bound offset outside)⟩

/-- A contract with a smaller footprint also holds for any larger one. -/
theorem Confined.widen {small large : List (Reference × Nat)} {before after : Memory}
    (framed : Confined small before after) (covered : ∀ entry ∈ small, entry ∈ large) :
    Confined large before after :=
  have narrow : ∀ {id offset}, Outside large id offset → Outside small id offset :=
    fun outside entry member => outside entry (covered entry member)
  ⟨framed.grows, framed.allocations, fun id bound offset outside => framed.cells id bound offset (narrow outside),
    framed.writable, fun id bound offset outside => framed.readable id bound offset (narrow outside)⟩

theorem Confined.ofMemoryBelow {footprint : List (Reference × Nat)} {before after : Memory} {watermark : Nat}
    (preserved : MemoryBelow watermark before after) (covers : before.nextIdentity ≤ watermark)
    (grows : before.nextIdentity ≤ after.nextIdentity) : Confined footprint before after :=
  have old : ∀ {id}, id < before.nextIdentity → id < watermark := fun bound => Nat.lt_of_lt_of_le bound covers
  ⟨grows, fun id bound => preserved.allocations id (old bound),
    fun id bound offset _ => preserved.cells id (old bound) offset,
    fun id bound offset => preserved.permissions id (old bound) offset true,
    fun id bound offset _ => preserved.permissions id (old bound) offset false⟩

/-- Footprint entries in identities allocated after `before`, such as a callee's locals, can be dropped. -/
theorem Confined.forget_fresh {fresh footprint : List (Reference × Nat)} {before after : Memory}
    (framed : Confined (fresh ++ footprint) before after)
    (young : ∀ entry ∈ fresh, before.nextIdentity ≤ entry.1.allocation) :
    Confined footprint before after :=
  have outside : ∀ {id offset}, id < before.nextIdentity → Outside footprint id offset →
      Outside (fresh ++ footprint) id offset := fun bound outside entry member =>
    (List.mem_append.mp member).elim (fun own => Or.inl (by have := young entry own; omega))
      (outside entry)
  ⟨framed.grows, framed.allocations, fun id bound offset o => framed.cells id bound offset (outside bound o),
    framed.writable, fun id bound offset o => framed.readable id bound offset (outside bound o)⟩

/-- A step that keeps all memory older than `first`, such as frame entry or teardown, keeps `Confined`. -/
theorem Confined.then_below {footprint : List (Reference × Nat)} {first middle last : Memory}
    (framed : Confined footprint first middle) (preserved : MemoryBelow first.nextIdentity middle last)
    (grows : middle.nextIdentity ≤ last.nextIdentity) : Confined footprint first last :=
  ⟨Nat.le_trans framed.grows grows,
    fun id bound => (preserved.allocations id bound).trans (framed.allocations id bound),
    fun id bound offset outside => (preserved.cells id bound offset).trans (framed.cells id bound offset outside),
    fun id bound offset => (preserved.permissions id bound offset true).trans (framed.writable id bound offset),
    fun id bound offset outside => (preserved.permissions id bound offset false).trans
      (framed.readable id bound offset outside)⟩

/-- A checked write inside the footprint keeps every other byte and all write authority. -/
theorem Confined.write {footprint : List (Reference × Nat)} {m result : Memory} {r : Reference}
    {bytes : List (BitVec 8)} {alignment : Nat}
    (h : write m r bytes alignment = .ok result) (member : (r, bytes.length) ∈ footprint) :
    Confined footprint m result := by
  have shape : result.views = writeViews m r bytes.length ∧ result.nextIdentity = m.nextIdentity := by
    unfold CIL.Safety.write at h
    cases ha : access m r bytes.length alignment true <;>
      simp only [ha, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    · cases h
    · cases h; exact ⟨rfl, rfl⟩
  have authority : ∀ writing q, permitted result writing q =
      permitted { m with views := ⟨r.allocation, r.offset, bytes.length, true, false⟩ :: m.views } writing q := by
    intro writing q
    rw [← writeViews_permitted m r bytes.length writing q]
    simp only [permitted, shape.1]
  refine ⟨Nat.le_of_eq shape.2.symm, fun id _ => by rw [write_allocations _ _ _ _ _ h], ?_, ?_, ?_⟩
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

/-- Write access to memory that existed before the call is unchanged. -/
theorem Confined.access_write {footprint : List (Reference × Nat)} {before after : Memory}
    (framed : Confined footprint before after) (r : Reference) (old : r.allocation < before.nextIdentity)
    (width alignment : Nat) :
    access after r width alignment true = access before r width alignment true := by
  have same : ∀ i, permitted after true { r with offset := r.offset + i } =
      permitted before true { r with offset := r.offset + i } := fun i => framed.writable _ old _
  simp only [CIL.Safety.access, form, liveAllocation, framed.allocations _ old, same]

/-- A read wholly outside the footprint sees the same bytes and authority. -/
theorem Confined.read_eq {footprint : List (Reference × Nat)} {before after : Memory}
    (framed : Confined footprint before after) (r : Reference) (old : r.allocation < before.nextIdentity)
    (width alignment : Nat) (outside : ∀ i < width, Outside footprint r.allocation (r.offset + i)) :
    read after r width alignment = read before r width alignment := by
  have authority : (List.range width).all (fun i => permitted after false { r with offset := r.offset + i }) =
      (List.range width).all (fun i => permitted before false { r with offset := r.offset + i }) := by
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
  simp only [CIL.Safety.read, CIL.Safety.access, form, liveAllocation, framed.allocations _ old, authority, cells]

theorem read_access {m : Memory} {r : Reference} {width alignment : Nat} {bytes : List (BitVec 8)}
    (h : read m r width alignment = .ok bytes) : access m r width alignment false = .ok () := by
  unfold CIL.Safety.read at h
  cases ha : access m r width alignment false with
  | error fault => simp [ha, Bind.bind, Except.bind] at h
  | ok value => rfl

/-- Any reference a well-formed memory admits names an allocation below its watermark. -/
theorem Memory.WellFormed.access_bound {m : Memory} {r : Reference} {width alignment : Nat} {writing : Bool}
    (formed : m.WellFormed) (h : access m r width alignment writing = .ok ()) : r.allocation < m.nextIdentity := by
  obtain ⟨_, ready⟩ := access_requirements h
  exact (formed.1 _ _ ready.present).1

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

/-- A typed method contract. `pre` carries formation, authority and the permitted
    aliasing; `footprint` bounds the bytes of earlier memory the method may change. -/
structure MethodContract (Input : Type) where
  args : Input → List Value
  pre : Input → Memory → Prop
  footprint : Input → List (Reference × Nat)
  post : Input → Memory → Memory → List Value → Prop

/-- Normal return within the footprint satisfying `post`, for every input meeting `pre`.
    Fuel stays existential, so callers never depend on the callee's step count. -/
def MethodContract.Holds {Input : Type} (c : MethodContract Input) (program : CIL.Program) (method : Nat) : Prop :=
  ∀ input initial, c.pre input initial →
    ∃ fuel final values, invoke program fuel method (c.args input) initial = .ok (final, values) ∧
      Confined (c.footprint input) initial final ∧ c.post input initial final values

/-- A contract is `Ensures` at each input, with the footprint as part of the postcondition. -/
theorem MethodContract.Holds.ensures {Input : Type} {c : MethodContract Input} {program : CIL.Program}
    {method : Nat} (holds : c.Holds program method) (input : Input) :
    Ensures program method (fun args m => args = c.args input ∧ c.pre input m)
      (fun _ initial final values => Confined (c.footprint input) initial final ∧ c.post input initial final values) := by
  rintro args initial ⟨rfl, permitted⟩
  exact holds input initial permitted

/-- Compose a fetched call through the callee's contract instead of its body. The
    continuation also receives the checked invocation for facts outside the contract. -/
theorem run_call_of_contract {Input : Type} {c : MethodContract Input} {program : CIL.Program}
    {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op} {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (continuation : ∀ final values,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, values)) →
      Confined (c.footprint input) updated final → c.post input updated final values →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame (values ++ rest) final = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧ post result returned := by
  subst encoded
  obtain ⟨childFuel, final, values, invoked, framed, satisfied⟩ := holds input updated permitted
  obtain ⟨parentFuel, result, returned, resumed, finished⟩ :=
    continuation final values ⟨childFuel, invoked⟩ framed satisfied
  obtain ⟨fuel, composed⟩ := run_call_exists methodFound instructionFound stepped ⟨childFuel, invoked⟩
    ⟨parentFuel, resumed⟩
  exact ⟨fuel, result, returned, composed, finished⟩

/-- A successful call from a well-formed memory returns a well-formed memory and keeps
    the static world, whatever the callee's contract states. -/
theorem call_frame_invariants {program : CIL.Program} {method pc callee fuel : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack arguments rest values : List Value}
    {frame : Frame} {memory updated final : Memory}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (formed : memory.WellFormed) (invoked : invoke program fuel callee arguments updated = .ok (final, values)) :
    final.WellFormed ∧ (StaticWorldValid (programStaticDescriptors program) memory →
      StaticWorldValid (programStaticDescriptors program) final) := by
  have called : ProgramStep program method pc args frame stack memory (.call callee arguments rest updated) :=
    ⟨body, op, methodFound, instructionFound, stepped⟩
  have entered : updated.WellFormed := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ formed called
  exact ⟨invoke_preserves_wellFormed _ _ _ _ _ _ _ entered invoked, fun world =>
    invoke_preserves_static_world _ _ _ _ _ _ _ entered (programStep_preserves_static_world called formed world) invoked⟩

/-- `run_call_of_contract` from a well-formed memory: the continuation also receives the
    callee's well-formed final memory and static-world preservation across the call. -/
theorem run_call_of_contract_formed {Input : Type} {c : MethodContract Input} {program : CIL.Program}
    {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op} {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated) (formed : memory.WellFormed)
    (continuation : ∀ final values,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, values)) → final.WellFormed →
      (StaticWorldValid (programStaticDescriptors program) memory →
        StaticWorldValid (programStaticDescriptors program) final) →
      Confined (c.footprint input) updated final → c.post input updated final values →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame (values ++ rest) final = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧ post result returned :=
  run_call_of_contract holds input methodFound instructionFound stepped encoded permitted
    fun final values ⟨fuel, invoked⟩ =>
      have kept := call_frame_invariants methodFound instructionFound stepped formed invoked
      continuation final values ⟨fuel, invoked⟩ kept.1 kept.2

theorem run_return_exists {program : CIL.Program} {method pc : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.returned values updated))
    (checked : values.mapM (checkedValue (leaveFrame frame updated)) = .ok values)
    (satisfied : post (leaveFrame frame updated) values) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧ post result returned :=
  ⟨1, _, _, run_return (fuel := 0) methodFound instructionFound stepped checked, satisfied⟩

theorem invoke_exists_of_run {program : CIL.Program} {method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory entered : Memory} {post : Memory → List Value → Prop}
    (found : program[method]? = some body)
    (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (executed : ∃ fuel result returned,
      run program fuel method 0 args frame [] entered = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned, invoke program fuel method args memory = .ok (result, returned) ∧ post result returned := by
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

#print axioms Confined.forget_fresh
#print axioms Confined.then_below
#print axioms Confined.write
#print axioms Confined.read_eq
#print axioms run_call_of_contract
#print axioms call_frame_invariants
#print axioms run_call_of_contract_formed
#print axioms invoke_ok_unique

/-- Step a goal `∃ fuel result returned, run ... ∧ post` through checked instructions,
    leaving each `.call` for `cil_contract_call` and the postcondition at each return. -/
syntax "cil_contract_steps" "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_contract_steps [$facts:term,*]) =>
  `(tactic| (
    -- A contract continuation resumes at `pc + 1` on `values ++ rest` with projected inputs.
    try dsimp only [List.nil_append, List.cons_append, Nat.reduceAdd]
    try (cil_strict refine CIL.Safety.invoke_exists_of_run
           (by simp only [cil_code, Nat.reduceAdd]; rfl)
           (by first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl))
           (by first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl)) ?_)
    repeat first
    | (cil_strict refine CIL.Safety.run_return_exists (op := .ret _)
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by cil_checked_step [$[$facts:term],*])
        (by first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl)) ?_)
    | (cil_strict refine CIL.Safety.run_next_exists (post := _)
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by simp only [cil_code, Nat.reduceAdd]; rfl)
        (by cil_checked_step [$[$facts:term],*]) ?_)))

/-- Apply a proved contract at the fetched call, optionally checked against a `bind_call`
    site: leaves the precondition, then the continuation over the callee's final memory,
    values, invocation, footprint and postcondition. -/
syntax "cil_contract_call" term:max term:max (" at " ident)? "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_contract_call $holds $input [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.run_call_of_contract $holds $input
      (by simp only [cil_code, Nat.reduceAdd]; rfl)
      (by simp only [cil_code, Nat.reduceAdd]; rfl)
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_))
  | `(tactic| cil_contract_call $holds $input at $site:ident [$facts:term,*]) =>
  `(tactic| (
    -- The site fixes the body, so the lookup may close during simplification.
    refine CIL.Safety.run_call_of_contract $holds $input
      (by first | rfl | (simp only [cil_code, Nat.reduceAdd] <;> rfl)) $(Lean.mkIdent (site.getId ++ `call))
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_))

/-- `cil_contract_call` through `run_call_of_contract_formed`: leaves the precondition,
    the caller memory's `WellFormed`, then the continuation with both invariants. -/
syntax "cil_formed_call" term:max term:max (" at " ident)? "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_formed_call $holds $input [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.run_call_of_contract_formed $holds $input
      (by simp only [cil_code, Nat.reduceAdd]; rfl)
      (by simp only [cil_code, Nat.reduceAdd]; rfl)
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_ ?_))
  | `(tactic| cil_formed_call $holds $input at $site:ident [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.run_call_of_contract_formed $holds $input
      (by first | rfl | (simp only [cil_code, Nat.reduceAdd] <;> rfl)) $(Lean.mkIdent (site.getId ++ `call))
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_ ?_))

end CIL.Safety
