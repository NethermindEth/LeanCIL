import CIL.Safety.MethodContract
import CIL.Safety.ConstructSetup
import CIL.Safety.ConstructComposition

namespace CIL.Safety

/-- `c` contracts a void constructor whose `post` reads back all `size` bytes at `this` as `value`. -/
structure MethodContract.Constructs {Input Output : Type} (c : MethodContract Input Output)
    (size : Fin (2^64)) (this : Input → Reference) (value : Input → Output → List (BitVec 8)) : Prop where
  void : ∀ out, c.results out = []
  readback : ∀ input initial final out, c.post input initial final out →
    read final (this input) size 1 = .ok (value input out)

/-- Storage `newobj` hands its constructor: all `size` bytes zeroed, readable and writable, above `memory`. -/
structure ConstructStorage (memory updated : Memory) (temporary : Reference) (size : Nat) : Prop where
  zeroed : read updated temporary size 1 = .ok (List.replicate size 0)
  writable : access updated temporary size 1 true = .ok ()
  preserved : MemoryBelow memory.nextIdentity memory updated
  fresh : temporary.allocation = memory.nextIdentity
  formed : updated.WellFormed

/-- A constructor's footprint, seen from the caller's memory before `newobj` allocated its storage. -/
theorem ConstructStorage.confined {memory updated final : Memory} {temporary : Reference} {size : Nat}
    {footprint : List (Reference × Nat)} (storage : ConstructStorage memory updated temporary size)
    (framed : Confined footprint updated final) : Confined footprint memory final := by
  have bound := storage.formed.access_bound storage.writable
  rw [storage.fresh] at bound
  exact (Confined.ofMemoryBelow storage.preserved (Nat.le_refl _) (Nat.le_of_lt bound)).trans framed

/-- Compose a fetched constructor through its contract: it returns void, and the continuation resumes on the read-back value. -/
theorem run_construct_of_contract {Input Output : Type} {c : MethodContract Input Output} {program : CIL.Program}
    {method pc callee : Nat} {size : Fin (2^64)} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value} {frame constructedFrame : Frame} {temporary : Reference}
    {memory updated : Memory} {this : Input → Reference} {value : Input → Output → List (BitVec 8)}
    {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (constructs : c.Constructs size this value) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory =
      .ok (.construct callee arguments rest constructedFrame temporary (.aggregate size) updated))
    (located : this input = temporary) (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (continuation : ∀ final out,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, [])) →
      Confined (c.footprint input) updated final → c.post input updated final out →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args constructedFrame
          (.scalar (.aggregate (value input out)) :: rest) final = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧ post result returned := by
  subst encoded
  obtain ⟨childFuel, final, values, invoked, framed, out, returned, satisfied⟩ := holds input updated permitted
  rw [constructs.void out] at returned
  subst returned
  have readback := constructs.readback _ _ _ _ satisfied
  rw [located] at readback
  obtain ⟨parentFuel, result, values, resumed, finished⟩ :=
    continuation final out ⟨childFuel, invoked⟩ framed satisfied
  obtain ⟨fuel, composed⟩ := run_construct_exists methodFound instructionFound stepped ⟨childFuel, invoked⟩
    (load_local_aggregate_of_read readback) ⟨parentFuel, resumed⟩
  exact ⟨fuel, result, values, composed, finished⟩

/-- A successful construction from a well-formed memory returns a well-formed memory and keeps the static world. -/
theorem construct_frame_invariants {program : CIL.Program} {method pc callee fuel : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack arguments rest values : List Value}
    {frame constructedFrame : Frame} {temporary : Reference} {kind : CIL.LocalKind} {memory updated final : Memory}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory =
      .ok (.construct callee arguments rest constructedFrame temporary kind updated))
    (formed : memory.WellFormed) (invoked : invoke program fuel callee arguments updated = .ok (final, values)) :
    final.WellFormed ∧ (StaticWorldValid (programStaticDescriptors program) memory →
      StaticWorldValid (programStaticDescriptors program) final) := by
  have constructed : ProgramStep program method pc args frame stack memory
      (.construct callee arguments rest constructedFrame temporary kind updated) :=
    ⟨body, op, methodFound, instructionFound, stepped⟩
  have entered : updated.WellFormed := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ formed constructed
  exact ⟨invoke_preserves_wellFormed _ _ _ _ _ _ _ entered invoked, fun world =>
    invoke_preserves_static_world _ _ _ _ _ _ _ entered
      (programStep_preserves_static_world constructed formed world) invoked⟩

/-- `run_construct_of_contract` from a well-formed memory: the continuation also receives both invariants. -/
theorem run_construct_of_contract_formed {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {size : Fin (2^64)} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value} {frame constructedFrame : Frame} {temporary : Reference}
    {memory updated : Memory} {this : Input → Reference} {value : Input → Output → List (BitVec 8)}
    {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (constructs : c.Constructs size this value) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory =
      .ok (.construct callee arguments rest constructedFrame temporary (.aggregate size) updated))
    (located : this input = temporary) (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (formed : memory.WellFormed)
    (continuation : ∀ final out,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, [])) → final.WellFormed →
      (StaticWorldValid (programStaticDescriptors program) memory →
        StaticWorldValid (programStaticDescriptors program) final) →
      Confined (c.footprint input) updated final → c.post input updated final out →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args constructedFrame
          (.scalar (.aggregate (value input out)) :: rest) final = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧ post result returned :=
  run_construct_of_contract holds constructs input methodFound instructionFound stepped located encoded permitted
    fun final out ⟨fuel, invoked⟩ =>
      have kept := construct_frame_invariants methodFound instructionFound stepped formed invoked
      continuation final out ⟨fuel, invoked⟩ kept.1 kept.2

/-- Construct at a fetched `newobj` from its constructor's contract alone; `input` names the fresh storage `newobj` zeroes. -/
theorem run_newAggregate_of_contract {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method pc callee argc : Nat} {size : Fin (2^64)} {body : CIL.Method}
    {args stack arguments : List Value} {frame : Frame} {memory : Memory}
    {this : Input → Reference} {value : Input → Output → List (BitVec 8)} {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (constructs : c.Constructs size this value) (input : Reference → Input)
    (methodFound : program[method]? = some body)
    (instructionFound : body.code[pc]? = some (.newAggregate callee argc size))
    (positive : 0 < size.val) (formed : memory.WellFormed) (enough : argc ≤ stack.length)
    (checked : (stack.take argc).reverse.mapM (checkedValue memory) = .ok arguments)
    (located : ∀ temporary, this (input temporary) = temporary)
    (encoded : ∀ temporary, c.args (input temporary) = .reference (.address temporary) :: arguments)
    (permitted : ∀ temporary updated, ConstructStorage memory updated temporary size →
      c.pre (input temporary) updated)
    (continuation : ∀ temporary updated final out, ConstructStorage memory updated temporary size →
      (∃ fuel, invoke program fuel callee (c.args (input temporary)) updated = .ok (final, [])) →
      final.WellFormed →
      (StaticWorldValid (programStaticDescriptors program) memory →
        StaticWorldValid (programStaticDescriptors program) final) →
      Confined (c.footprint (input temporary)) updated final → c.post (input temporary) updated final out →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args { frame with owned := temporary.allocation :: frame.owned }
          (.scalar (.aggregate (value (input temporary) out)) :: stack.drop argc) final = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧ post result returned := by
  have same := (checkedValues_valid _ _ _ checked).1
  have length : arguments.length = argc := by
    rw [same, List.length_reverse, List.length_take, Nat.min_eq_left enough]
  have split : arguments.reverse ++ stack.drop argc = stack := by
    rw [same, List.reverse_reverse, List.take_append_drop]
  rw [same] at checked
  obtain ⟨temporary, updated, stepped, zeroed, writable, preserved, fresh⟩ :=
    step_newAggregate (body := body) (pc := pc) (callee := callee) size positive args arguments
      (stack.drop argc) frame memory formed (by rw [same]; exact checked)
  rw [length, split] at stepped
  have entered : updated.WellFormed := programStep_preserves_wellFormed _ _ _ _ _ _ _ _ formed
    ⟨body, _, methodFound, instructionFound, stepped⟩
  have storage : ConstructStorage memory updated temporary size :=
    ⟨zeroed, writable, preserved, fresh, entered⟩
  refine run_construct_of_contract_formed holds constructs (input temporary) methodFound instructionFound stepped
    (located temporary) (encoded temporary).symm (permitted temporary updated storage) formed ?_
  intro final out invoked
  exact continuation temporary updated final out storage (by rw [encoded temporary]; exact invoked)

#print axioms ConstructStorage.confined
#print axioms run_construct_of_contract
#print axioms construct_frame_invariants
#print axioms run_construct_of_contract_formed
#print axioms run_newAggregate_of_contract

/-- Apply a constructor contract at the fetched `newobj`, leaving `WellFormed`, the precondition and the continuation. -/
syntax "cil_contract_construct" term:max term:max term:max "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_contract_construct $holds $constructs $input [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.run_newAggregate_of_contract $holds $constructs $input
      (by simp only [cil_code, Nat.reduceAdd]; rfl)
      (by simp only [cil_code, Nat.reduceAdd]; rfl)
      (by decide) ?_ (by simp)
      (by first | rfl | (simp [CIL.Safety.checkedValue, CIL.Safety.numericValue, $[$facts:term],*] <;>
        (repeat constructor) <;> rfl))
      (by intro _; rfl) (by intro _; rfl) ?_ ?_))

end CIL.Safety
