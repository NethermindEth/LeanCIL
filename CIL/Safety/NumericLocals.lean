import CIL.Safety.NumericLocalLoad
import CIL.Safety.HomeProgress
import CIL.Safety.FrameMemoryBelow

/-!
# Numeric local steps

Creating a numeric local gives a fresh, initialized, writable home, and the checked `ldloc`
and `stloc` steps on such a home are given in closed form for stepping proofs. During frame
entry, `EntryMemory` and `NumericEntryHome` carry the caller's memory and each home's facts
across later allocations to the entered memory.
-/

namespace CIL.Safety

/-- Fresh typed numeric storage has initialized readback and preserves older memory. -/
theorem make_numeric_local (memory : Memory) (activation : Nat)
    (kind : CIL.LocalKind) (value : CIL.Value) (number : Nat)
    (wellFormed : memory.WellFormed) (fits : localNumber kind value = .ok number) :
    ∃ reference result,
      makeLocal activation kind value memory =
        .ok (.bytes kind reference, [reference.allocation], result) ∧
      read result reference (localWidth kind) 1 = .ok (numberBytes number (localWidth kind)) ∧
      access result reference (localWidth kind) 1 true = .ok () ∧
      MemoryBelow memory.nextIdentity memory result := by
  have numeric : kind ≠ .reference := by
    cases kind <;> cases value <;> simp_all [localNumber, CIL.Value.hasUnspecified]
  have modeled : value ≠ .unmodeled := by
    cases kind <;> cases value <;> simp_all [localNumber, CIL.Value.hasUnspecified]
  have notSpan : ∀ width writable, kind ≠ .span width writable := by
    cases kind <;> cases value <;> simp_all [localNumber, CIL.Value.hasUnspecified]
  have notArray : ∀ element, kind ≠ .array element := by
    cases kind <;> cases value <;> simp_all [localNumber, CIL.Value.hasUnspecified]
  have notPointer : ∀ signature, kind ≠ .methodPointer signature := by
    cases kind <;> cases value <;> simp_all [localNumber, CIL.Value.hasUnspecified]
  have notTable : ∀ signature, kind ≠ .methodTable signature := by
    cases kind <;> cases value <;> simp_all [localNumber, CIL.Value.hasUnspecified]
  have bounded : localWidth kind < nativeLimit := by
    cases kind <;> simp only [localWidth, nativeLimit] <;>
      first | exact CIL.NarrowKind.width_lt _ | simp
  obtain ⟨reference, allocated, home⟩ := allocateHome_succeeds memory activation
    (localWidth kind) wellFormed bounded (localAlignment_pos kind)
  have ready := allocateHome_write_access _ _ _ _ _ home
  obtain ⟨result, written, stored, readback⟩ :=
    store_numeric_local kind value number fits ready.access
  have created : makeLocal activation kind value memory =
      .ok (.bytes kind reference, [reference.allocation], result) := by
    cases kind <;> simp_all [makeLocal, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨reference, result, created, readback, (ready.after_write written).access,
    makeLocal_preserves_caller_memory _ _ _ _ _ _ _ created⟩

/-- `ldloc` of a numeric home holding `value`'s bytes pushes the normalized value. -/
theorem step_load_numeric_local {body : CIL.Method} {pc index : Nat} {args stack : List Value}
    {frame : Frame} {memory : Memory} {reference : Reference}
    (kind : CIL.LocalKind) (value : CIL.Value) (number : Nat)
    (fits : localNumber kind value = .ok number)
    (slot : frame.locals[index]? = some (.bytes kind reference))
    (loaded : read memory reference (localWidth kind) 1 =
      .ok (numberBytes number (localWidth kind))) :
    step body (.local index) pc args frame stack memory =
      .ok (.next (pc + 1) (.scalar (localResult kind value) :: stack) frame memory) := by
  simp only [step, observerCount, unspecifiedOperands, List.take_zero, List.any_nil,
    Bool.false_or, Bool.false_eq_true, ite_false, slot,
    load_numeric_local kind value number fits loaded,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- `stloc` of a numeric value into a writable home continues with the bytes written and
    readable back. -/
theorem step_store_numeric_local {body : CIL.Method} {pc index : Nat} {args rest : List Value}
    {frame : Frame} {memory : Memory} {reference : Reference}
    (kind : CIL.LocalKind) (value : CIL.Value) (number : Nat)
    (fits : localNumber kind value = .ok number)
    (slot : frame.locals[index]? = some (.bytes kind reference))
    (ready : access memory reference (localWidth kind) 1 true = .ok ()) :
    ∃ result,
      step body (.setLocal index) pc args frame (.scalar value :: rest) memory =
        .ok (.next (pc + 1) rest frame result) ∧
      write memory reference (numberBytes number (localWidth kind)) 1 = .ok result ∧
      read result reference (localWidth kind) 1 = .ok (numberBytes number (localWidth kind)) := by
  obtain ⟨result, written, stored, readback⟩ := store_numeric_local kind value number fits ready
  have unchanged : frame.locals.set index (.bytes kind reference) = frame.locals := by
    apply List.ext_getElem?
    intro other
    by_cases same : index = other
    · subst other
      simp only [List.getElem?_set_self', slot]
      rfl
    · simp only [List.getElem?_set_ne same]
  refine ⟨result, ?_, written, readback⟩
  simp only [step, observerCount, unspecifiedOperands, List.take_zero, List.any_nil,
    Bool.false_or, Bool.false_eq_true, ite_false, slot, stored, unchanged,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms make_numeric_local
#print axioms step_load_numeric_local
#print axioms step_store_numeric_local

/-- Memory during frame entry: the caller's memory below its watermark is kept, identities only
    grow, and the memory stays well formed. -/
structure EntryMemory (caller memory : Memory) : Prop where
  kept : MemoryBelow caller.nextIdentity caller memory
  grown : caller.nextIdentity ≤ memory.nextIdentity
  wellFormed : memory.WellFormed

/-- Frame entry starts from well-formed caller memory. -/
theorem EntryMemory.start {memory : Memory} (wellFormed : memory.WellFormed) :
    EntryMemory memory memory :=
  ⟨MemoryBelow.refl _ _, Nat.le_refl _, wellFormed⟩

/-- Successive frame-entry allocations compose. -/
theorem EntryMemory.trans {caller middle last : Memory} (first : EntryMemory caller middle)
    (second : EntryMemory middle last) : EntryMemory caller last :=
  ⟨first.kept.trans (second.kept.weaken first.grown), Nat.le_trans first.grown second.grown,
    second.wellFormed⟩

/-- A numeric local's home in the entered memory: allocated above the caller, holding its
    initializer's bytes, and writable. -/
structure NumericEntryHome (caller entered : Memory) (kind : CIL.LocalKind) (number : Nat)
    (home : Reference) : Prop where
  fresh : caller.nextIdentity ≤ home.allocation
  bounded : home.allocation < entered.nextIdentity
  loaded : read entered home (localWidth kind) 1 = .ok (numberBytes number (localWidth kind))
  writable : access entered home (localWidth kind) 1 true = .ok ()

/-- Later frame-entry allocations keep an earlier home's bytes and authority. -/
theorem NumericEntryHome.after {caller middle last : Memory} {kind : CIL.LocalKind}
    {number : Nat} {home : Reference} (entered : NumericEntryHome caller middle kind number home)
    (later : EntryMemory middle last) : NumericEntryHome caller last kind number home :=
  ⟨entered.fresh, Nat.lt_of_lt_of_le entered.bounded later.grown,
    by rw [later.kept.read home entered.bounded (localWidth kind) 1]; exact entered.loaded,
    by rw [later.kept.access home entered.bounded (localWidth kind) 1 true]
       exact entered.writable⟩

/-- Creating a numeric local during frame entry yields its home and extends entry memory. -/
theorem make_numeric_entry_local {caller memory : Memory} (entered : EntryMemory caller memory)
    (activation : Nat) (kind : CIL.LocalKind) (value : CIL.Value) (number : Nat)
    (fits : localNumber kind value = .ok number) :
    ∃ home result,
      makeLocal activation kind value memory =
        .ok (.bytes kind home, [home.allocation], result) ∧
      NumericEntryHome caller result kind number home ∧ EntryMemory memory result := by
  obtain ⟨home, result, made, loaded, writable, kept⟩ :=
    make_numeric_local memory activation kind value number entered.wellFormed fits
  have owned := makeLocal_fresh _ _ _ _ _ _ _ made
  have fresh := owned.2 home.allocation (by simp)
  exact ⟨home, result, made, ⟨Nat.le_trans entered.grown fresh.1, fresh.2, loaded, writable⟩,
    ⟨kept, owned.1.next,
      makeLocal_preserves_wellFormed _ _ _ _ _ _ _ entered.wellFormed made⟩⟩

#print axioms EntryMemory.trans
#print axioms NumericEntryHome.after
#print axioms make_numeric_entry_local
end CIL.Safety
