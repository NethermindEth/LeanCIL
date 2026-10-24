import CIL.Safety.HomeProgress

/-!
# Frame setup succeeds

Sufficient conditions for `enterFrame` (in `CIL/Safety/Frames.lean`) not to fault: memory is
well formed, the arguments are valid, and the method's metadata fits its arguments
(`FrameSetupFits`). These are signature and type compatibility conditions, independent of
what the method later does. `enterFrame_live_succeeds` also yields the `LiveState` that
the checked execution invariants start from.
-/

namespace CIL.Safety

/-- Metadata/type compatibility, independent of caller memory and execution.
    Unknown initializers remain unknown; numeric initializers must fit their
    physical home, and a managed root may start null. -/
def InitializerFits (kind : CIL.LocalKind) (initial : CIL.Value) : Prop :=
  initial = .unmodeled ∨ match kind, initial with
  | .aggregate size, .aggregate bytes => bytes.length = size.val
  | .reference, .nullRef => True
  | .byte, .i32 bits => bits.toNat < 256
  | .narrow _, .i32 _ => True
  | .word32, .i32 _ | .word64, .i64 _ | .vector128, .v128 _ | .vector256, .v256 _
  | .vector512, .v512 _ => True
  | _, _ => False

theorem initializer_numeric_number {kind : CIL.LocalKind} {initial : CIL.Value}
    (fits : InitializerFits kind initial) (numeric : kind ≠ .reference)
    (known : initial ≠ .unmodeled) : ∃ number, localNumber kind initial = .ok number := by
  cases kind <;> cases initial <;>
    simp_all [InitializerFits, localNumber, CIL.Value.hasUnspecified]

theorem localWidth_bounded (kind : CIL.LocalKind) : localWidth kind < nativeLimit := by
  cases kind <;> simp only [localWidth, nativeLimit] <;>
    first | exact CIL.NarrowKind.width_lt _ | simp

theorem makeLocal_succeeds (m : Memory) (activation : Nat) (kind : CIL.LocalKind)
    (initial : CIL.Value) (wellFormed : m.WellFormed) (fits : InitializerFits kind initial) :
    ∃ slot owned result, makeLocal activation kind initial m = .ok (slot, owned, result) := by
  by_cases root : kind = .reference
  · subst kind
    cases initial <;> simp_all [InitializerFits, makeLocal]
  · obtain ⟨reference, memory, home⟩ :=
      allocateHome_succeeds m activation (localWidth kind) wellFormed (localWidth_bounded kind)
        (localAlignment_pos kind)
    by_cases unknown : initial = .unmodeled
    · refine ⟨.bytes kind reference, [reference.allocation], memory, ?_⟩
      cases kind <;> simp_all [makeLocal, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · obtain ⟨number, value⟩ := initializer_numeric_number fits root unknown
      obtain ⟨slot, result, stored⟩ := fresh_home_storeLocal_succeeds _ _ _ _ _ _ _ home value
      refine ⟨slot, [reference.allocation], result, ?_⟩
      cases kind <;> simp_all [makeLocal, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- `InitializerFits` for each local, with exactly one initializer per local kind. -/
def InitializersFit : List CIL.LocalKind → List CIL.Value → Prop
  | [], [] => True
  | kind :: kinds, initial :: initializers =>
    InitializerFits kind initial ∧ InitializersFit kinds initializers
  | _, _ => False

theorem makeLocals_succeeds (m : Memory) (activation : Nat)
    (kinds : List CIL.LocalKind) (initializers : List CIL.Value) (wellFormed : m.WellFormed)
    (fits : InitializersFit kinds initializers) :
    ∃ slots owned result,
      makeLocals activation kinds initializers m = .ok (slots, owned, result) := by
  induction kinds generalizing m initializers with
  | nil =>
    cases initializers with
    | nil => exact ⟨[], [], m, rfl⟩
    | cons initial rest => cases fits
  | cons kind kinds ih =>
    cases initializers with
    | nil => cases fits
    | cons initial initials =>
      obtain ⟨slot, ids, memory, prepared⟩ := makeLocal_succeeds m activation _ _ wellFormed fits.1
      have valid := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ wellFormed prepared
      obtain ⟨slots, other, result, rest⟩ := ih memory initials valid fits.2
      exact ⟨slot :: slots, ids ++ other, result, by
        simp [makeLocals, prepared, rest, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

/-- Aggregate-home indices must designate actual by-value aggregate arguments.
    This is signature/type compatibility, not an access or future-run condition. -/
def AggregateArgumentsFit (indices : List Nat) (args : List Value) : Prop :=
  ∀ index ∈ indices, ∃ bits, args[index]? = some (.scalar (.v256 bits))

theorem makeArgumentHomes_succeeds (m : Memory) (activation : Nat) (indices : List Nat)
    (args : List Value) (wellFormed : m.WellFormed) (fits : AggregateArgumentsFit indices args) :
    ∃ homes owned result,
      makeArgumentHomes activation indices args m = .ok (homes, owned, result) := by
  induction indices generalizing m with
  | nil => exact ⟨[], [], m, rfl⟩
  | cons index indices ih =>
    obtain ⟨bits, argument⟩ := fits index (by simp)
    obtain ⟨reference, memory, home⟩ :=
      allocateHome_succeeds (alignment := 1) m activation (localWidth .vector256) wellFormed
        (localWidth_bounded _) (by decide)
    obtain ⟨slot, stored, store⟩ := fresh_home_storeLocal_succeeds m memory activation .vector256
      reference (.v256 bits) bits.toNat home rfl
    have valid := storeLocal_preserves_wellFormed _ _ _ _ _
      (allocateHome_preserves_wellFormed _ _ _ _ _ wellFormed home) store
    obtain ⟨homes, owned, result, rest⟩ :=
      ih stored valid (fun i member => fits i (by simp [member]))
    exact ⟨(index, slot) :: homes, reference.allocation :: owned, result, by
      simp [makeArgumentHomes, argument, home, store, rest,
        Value.hasUnspecified, CIL.Value.hasUnspecified,
        Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

/-- An argument can initialize a parameter home of `kind`: a scalar that stores as that
    numeric kind, or a reference for a reference parameter. -/
def ParameterFits (kind : CIL.LocalKind) : Value → Prop
  | .scalar value => kind ≠ .reference ∧ ∃ number, localNumber kind value = .ok number
  | .reference _ => kind = .reference
  | .span _ _ => False

/-- Every parameter home names an existing argument that fits its kind. -/
def ParameterArgumentsFit (parameters : List (Nat × CIL.LocalKind)) (args : List Value) :
    Prop :=
  ∀ parameter ∈ parameters,
    ∃ value, args[parameter.1]? = some value ∧ ParameterFits parameter.2 value

theorem initializeParameter_succeeds (m : Memory) (activation : Nat) (kind : CIL.LocalKind)
    (value : Value) (hm : m.WellFormed) (valid : value.Valid m) (fits : ParameterFits kind value) :
    ∃ slot owned home final result,
      makeLocal activation kind .unmodeled m = .ok (slot, owned, home) ∧
      storeLocal home slot value = .ok (final, result) := by
  cases value with
  | span r length => cases fits
  | reference r =>
    change kind = .reference at fits
    subst kind
    have formed := checkedValue_of_valid m (.reference r) valid
    exact ⟨.root none, [], m, .root (some r), m, rfl, by
      simp only [checkedValue] at formed
      simp [storeLocal, formed, Value.hasUnspecified,
        Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
  | scalar value =>
    obtain ⟨numeric, number, numbered⟩ := fits
    obtain ⟨r, home, allocated⟩ := allocateHome_succeeds m activation (localWidth kind) hm
      (localWidth_bounded kind) (localAlignment_pos kind)
    obtain ⟨final, result, stored⟩ :=
      fresh_home_storeLocal_succeeds _ _ _ _ _ _ _ allocated numbered
    refine ⟨.bytes kind r, [r.allocation], home, final, result, ?_, stored⟩
    cases kind <;> simp_all [makeLocal, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem makeParameterHomes_succeeds (m : Memory) (activation : Nat)
    (parameters : List (Nat × CIL.LocalKind)) (args : List Value)
    (hm : m.WellFormed) (valid : ValuesValid m args)
    (fits : ParameterArgumentsFit parameters args) :
    ∃ homes owned result,
      makeParameterHomes activation parameters args m = .ok (homes, owned, result) := by
  induction parameters generalizing m with
  | nil => exact ⟨[], [], m, rfl⟩
  | cons parameter parameters ih =>
    obtain ⟨index, kind⟩ := parameter
    obtain ⟨value, argument, compatible⟩ := fits (index, kind) (by simp)
    obtain ⟨slot, ids, home, final, stored, made, store⟩ :=
      initializeParameter_succeeds m activation kind value hm
        (valid value (List.mem_of_getElem? argument)) compatible
    have homeWF := makeLocal_preserves_wellFormed _ _ _ _ _ _ _ hm made
    have storedWF := storeLocal_preserves_wellFormed _ _ _ _ _ homeWF store
    have ext := (makeLocal_fresh _ _ _ _ _ _ _ made).1.trans
      (storeLocal_extends_allocations _ _ _ _ _ store)
    obtain ⟨homes, other, result, rest⟩ := ih stored storedWF (valid.preserve hm ext)
      (fun p member => fits p (by simp [member]))
    exact ⟨(index, final) :: homes, ids ++ other, result, by
      simp [makeParameterHomes, argument, made, store, rest,
        Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

/-- Every local selected as opaque, numbering from `index`, is a 128-bit vector. -/
def SelectedKindsFit (indices : List Nat) (index : Nat) : List CIL.LocalKind → Prop
  | [] => True
  | kind :: kinds =>
    (index ∈ indices → kind = .vector128) ∧ SelectedKindsFit indices (index + 1) kinds

theorem makeSelectedLocalsFrom_succeeds (m : Memory) (activation : Nat) (indices : List Nat)
    (index : Nat) (kinds : List CIL.LocalKind) (initializers : List CIL.Value)
    (wellFormed : m.WellFormed) (fits : InitializersFit kinds initializers)
    (selected : SelectedKindsFit indices index kinds) :
    ∃ slots owned result, makeSelectedLocalsFrom activation indices index kinds initializers m =
      .ok (slots, owned, result) := by
  induction kinds generalizing index m initializers with
  | nil => cases initializers with
    | nil => exact ⟨[], [], m, rfl⟩
    | cons _ _ => cases fits
  | cons kind kinds ih =>
    cases initializers with
    | nil => cases fits
    | cons initial initials =>
      have prepared : ∃ slot ids memory,
          (if index ∈ indices then
              if kind == .vector128 then makeOpaque128 initial m else .error .invalidState
            else makeLocal activation kind initial m) = .ok (slot, ids, memory) ∧
            memory.WellFormed := by
        by_cases member : index ∈ indices
        · have same := selected.1 member
          subst kind
          have compatible : InitializerFits .vector128 initial := fits.1
          rcases compatible with unknown | known
          · subst initial
            exact ⟨.opaque128 none, [], m, by rw [ite_eq_left member]; rfl, wellFormed⟩
          · cases initial with
            | v128 bits =>
              exact ⟨.opaque128 (some (.known bits)), [], m,
                by rw [ite_eq_left member]; rfl, wellFormed⟩
            | _ => cases known
        · obtain ⟨slot, ids, memory, made⟩ :=
            makeLocal_succeeds m activation kind initial wellFormed fits.1
          exact ⟨slot, ids, memory, by simpa [member] using made,
            makeLocal_preserves_wellFormed _ _ _ _ _ _ _ wellFormed made⟩
      obtain ⟨slot, ids, memory, made, valid⟩ := prepared
      obtain ⟨slots, other, result, rest⟩ := ih memory (index + 1) initials valid fits.2 selected.2
      refine ⟨slot :: slots, ids ++ other, result, ?_⟩
      by_cases member : index ∈ indices
      · have same := selected.1 member
        subst kind
        simp [member] at made
        simp [makeSelectedLocalsFrom, member, made, rest, Bind.bind, Except.bind, Pure.pure,
          Except.pure]
      · simp only [member, ite_false] at made
        simp [makeSelectedLocalsFrom, member, made, rest, Bind.bind, Except.bind, Pure.pure,
          Except.pure]

theorem makeSelectedLocals_succeeds (m : Memory) (activation : Nat) (indices : List Nat)
    (kinds : List CIL.LocalKind) (initializers : List CIL.Value) (wellFormed : m.WellFormed)
    (fits : InitializersFit kinds initializers) (selected : SelectedKindsFit indices 0 kinds) :
    ∃ slots owned result,
      makeSelectedLocals activation indices kinds initializers m = .ok (slots, owned, result) := by
  unfold makeSelectedLocals
  split
  · exact makeLocals_succeeds _ _ _ _ wellFormed fits
  · exact makeSelectedLocalsFrom_succeeds _ _ _ _ _ _ wellFormed fits selected

/-- A method's frame metadata fits its arguments, so `enterFrame` cannot fault on a
    well-formed memory with valid arguments (`enterFrame_succeeds`). -/
def FrameSetupFits (body : CIL.Method) (args : List Value) : Prop :=
  InitializersFit body.localKinds body.locals ∧ AggregateArgumentsFit body.vectorArgs args ∧
    ParameterArgumentsFit body.parameterHomes args ∧
    SelectedKindsFit body.opaqueVectorLocals 0 body.localKinds

@[simp] theorem selectedKindsFit_nil (index : Nat) (kinds : List CIL.LocalKind) :
    SelectedKindsFit [] index kinds := by
  induction kinds generalizing index with
  | nil => trivial
  | cons kind kinds ih => exact ⟨by simp, ih (index + 1)⟩
#print axioms selectedKindsFit_nil

theorem frameSetupFits_of_no_opaque (body : CIL.Method) (args : List Value)
    (none : body.opaqueVectorLocals = []) :
    FrameSetupFits body args ↔
      InitializersFit body.localKinds body.locals ∧ AggregateArgumentsFit body.vectorArgs args ∧
        ParameterArgumentsFit body.parameterHomes args := by
  simp only [FrameSetupFits, none, selectedKindsFit_nil, and_true]
#print axioms frameSetupFits_of_no_opaque

theorem enterFrame_succeeds (body : CIL.Method) (args : List Value) (m : Memory)
    (wellFormed : m.WellFormed) (validArgs : ValuesValid m args)
    (fits : FrameSetupFits body args) :
    ∃ frame memory, enterFrame body args m = .ok (frame, memory) := by
  obtain ⟨locals, owned, memory, prepared⟩ :=
    makeSelectedLocals_succeeds m m.nextIdentity body.opaqueVectorLocals body.localKinds
      body.locals wellFormed fits.1 fits.2.2.2
  have setup := makeSelectedLocals_setup _ _ _ _ _ _ _ _ prepared
  have valid := setup.wellFormed wellFormed
  obtain ⟨arguments, ids, result, homes⟩ :=
    makeArgumentHomes_succeeds memory m.nextIdentity body.vectorArgs args valid fits.2.1
  have resultWF := makeArgumentHomes_preserves_wellFormed _ _ _ _ _ _ _ valid homes
  have ext := setup.fresh.1.trans
    (makeArgumentHomes_fresh _ _ _ _ _ _ _ homes).1
  obtain ⟨parameters, other, final, parametersMade⟩ := makeParameterHomes_succeeds result
    m.nextIdentity body.parameterHomes args resultWF (validArgs.preserve wellFormed ext)
    fits.2.2.1
  exact ⟨⟨m.nextIdentity, locals ++ parameters.map Prod.snd, (owned ++ ids) ++ other,
    arguments⟩, final, by
    simp [enterFrame, prepared, homes, parametersMade, Bind.bind, Except.bind, Pure.pure,
      Except.pure]⟩

/-- Entering a frame whose metadata fits its arguments succeeds and starts the callee in a
    `LiveState` with an empty stack. -/
theorem enterFrame_live_succeeds (program : CIL.Program) (body : CIL.Method)
    (args : List Value) (m : Memory) (wellFormed : m.WellFormed) (valid : ValuesValid m args)
    (world : StaticWorldValid (programStaticDescriptors program) m)
    (fits : FrameSetupFits body args) :
    ∃ frame memory, enterFrame body args m = .ok (frame, memory) ∧
      LiveState program args frame [] memory := by
  obtain ⟨frame, memory, setup⟩ := enterFrame_succeeds body args m wellFormed valid fits
  exact ⟨frame, memory, setup, enterFrame_live_state _ _ _ _ _ _ wellFormed valid world setup⟩

#print axioms makeLocal_succeeds
#print axioms makeLocals_succeeds
#print axioms makeArgumentHomes_succeeds
#print axioms enterFrame_succeeds
#print axioms enterFrame_live_succeeds

end CIL.Safety
