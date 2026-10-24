import CIL.Safety.CallingTransport

/-!
Consumer uses of the `ValidCall` transport lemmas on one 24-byte caller allocation with an
8-byte input at offset 0 and an 8-byte output at offset 16: the same buffers stay valid for
a second call after writes, frame entry and a call confined apart from the input, and a call
confined over the input can revoke its read authority, so `after_confined` needs `Apart`.
-/

namespace Tests.ValidCallTransport

open CIL.Safety

/-- The size of the only allocation in `sample`. -/
abbrev size : Nat := 24

/-- One `size`-byte caller allocation, readable and writable, holding initialized zeros. -/
def sample : Memory := {
  allocations := fun id =>
    if id = 0 then some ⟨.callerStack, ⟨size, 1, []⟩, true, [size]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, size, true, true⟩]
  nextIdentity := 1 }

/-- `sample` after a callee revokes read authority over the whole allocation. -/
def revoked : Memory := { sample with views := [⟨0, 0, size, false, true⟩] }

/-- The input: bytes 0 to 7 of the allocation. -/
def source : ArgumentView := ⟨⟨0, 0⟩, 8⟩

/-- The output: bytes 16 to 23, apart from the input. -/
def target : ArgumentView := ⟨⟨0, 16⟩, 8⟩

/-- Well-formed whenever the only view lies inside the only allocation. -/
theorem formed_of_view {views : List View} (inside : views = [⟨0, 0, size, true, true⟩] ∨
    views = [⟨0, 0, size, false, true⟩]) : ({ sample with views } : Memory).WellFormed := by
  refine ⟨fun id allocation found => ?_, fun view member => ?_⟩
  · by_cases zero : id = 0
    · subst zero
      simp only [sample, ite_true, Option.some.injEq] at found
      subst found
      exact ⟨Nat.zero_lt_one, (allocation_valid_iff _).mp rfl⟩
    · simp [sample, zero] at found
  · rcases inside with rfl | rfl <;> simp only [List.mem_singleton] at member <;> subst member <;>
      exact ⟨_, rfl, by decide⟩

/-- The caller passes a readable input and a writable output. -/
theorem sample_valid : ValidCall sample [source] [target] := by
  refine ⟨formed_of_view (.inl rfl), fun input member => ?_, fun output member => ?_⟩
  · simp only [List.mem_singleton] at member
    subst member
    exact ⟨_, rfl⟩
  · simp only [List.mem_singleton] at member
    subst member
    rfl

/-! The identity bounds feed the `old` premise of the memory relations. -/

example : source.reference.allocation < sample.nextIdentity :=
  sample_valid.input_bound (List.mem_singleton_self _)

example : target.reference.allocation < sample.nextIdentity :=
  sample_valid.output_bound (List.mem_singleton_self _)

/-- Dropping buffers keeps the call valid. -/
example : ValidCall sample [] [target] :=
  sample_valid.mono (fun _ member => nomatch member) fun _ member => member

/-! The same buffers stay valid for a second call. -/

/-- Writing the output does not invalidate it or the input. -/
theorem valid_after_output_write {result : Memory}
    (written : write sample target.reference (numberBytes 5 8) 1 = .ok result) :
    ValidCall result [source] [target] :=
  sample_valid.after_write written

/-- Writing the input itself keeps it readable: a write only initializes bytes. -/
theorem valid_after_input_write {result : Memory}
    (written : write sample source.reference (numberBytes 5 8) 1 = .ok result) :
    ValidCall result [source] [target] :=
  sample_valid.after_write written

/-- A callee's frame adds only fresh allocations. -/
theorem valid_after_enterFrame {body : CIL.Method} {args : List Value} {frame : Frame}
    {entered : Memory} (setup : enterFrame body args sample = .ok (frame, entered)) :
    ValidCall entered [source] [target] :=
  sample_valid.after_enterFrame setup

/-- Memory fixed below the caller's watermark, as a frame round trip leaves it. -/
theorem valid_after_below {result : Memory}
    (preserved : MemoryBelow sample.nextIdentity sample result) (formed : result.WellFormed) :
    ValidCall result [source] [target] :=
  sample_valid.after_below preserved.accessBelow (Nat.le_refl _) formed

/-- A callee confined to the output leaves the input apart from its footprint. -/
theorem valid_after_confined {result : Memory}
    (framed : Confined [(target.reference, target.width)] sample result)
    (formed : result.WellFormed) : ValidCall result [source] [target] :=
  sample_valid.after_confined framed formed fun input member entry inside => by
    simp only [List.mem_singleton] at member inside
    subst member inside
    exact Or.inr (Or.inl (by decide))

#print axioms formed_of_view
#print axioms sample_valid
#print axioms valid_after_output_write
#print axioms valid_after_input_write
#print axioms valid_after_enterFrame
#print axioms valid_after_below
#print axioms valid_after_confined

/-! Without `Apart`, a confined callee may revoke the input's read authority. -/

/-- Revoking read authority over the whole allocation is confined to it. -/
theorem revoke_confined : Confined [(source.reference, size)] sample revoked := by
  refine ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ _ _ => rfl, ?_, ?_⟩
  · intro id _ offset
    simp [permitted, viewContains, revoked, sample]
  · intro id old offset outside
    have zero : id = 0 := by simp only [sample] at old; omega
    subst zero
    have beyond : size ≤ offset := by
      have := outside _ (List.mem_singleton_self _)
      simp only [source, ne_eq, not_true_eq_false, Nat.not_lt_zero, false_or] at this
      omega
    have outsideView : ¬ offset < size := by omega
    simp [permitted, viewContains, revoked, sample, outsideView]

/-- With read authority revoked, the input can no longer be read. -/
theorem revoked_invalid : ¬ ValidCall revoked [source] [target] := fun valid => by
  obtain ⟨bytes, loaded⟩ := valid.2.1 source (List.mem_singleton_self _)
  rw [show read revoked source.reference source.width 1 = .error .unreadable from rfl] at loaded
  cases loaded

/-- Every premise of `after_confined` except `Apart` holds, and the conclusion fails. -/
theorem confined_needs_apart :
    ValidCall sample [source] [target] ∧ Confined [(source.reference, size)] sample revoked ∧
      revoked.WellFormed ∧ ¬ ValidCall revoked [source] [target] :=
  ⟨sample_valid, revoke_confined, formed_of_view (.inr rfl), revoked_invalid⟩

#print axioms revoke_confined
#print axioms revoked_invalid
#print axioms confined_needs_apart

end Tests.ValidCallTransport
