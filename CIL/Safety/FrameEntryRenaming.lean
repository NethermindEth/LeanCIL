import CIL.Safety.FrameRenaming

/-!
# Frame entry with dead numeric locals

Ordinary declarations preserve retained initializers while allocating corresponding
homes. Entry transport derives target success from the actual successful source entry.
Opaque slots and argument or parameter homes have separate setup semantics and are
explicitly excluded by this entry theorem.
-/

namespace CIL.Safety

/-- Ordinary declarations use explicit local metadata without auxiliary argument homes. -/
structure OrdinaryFrame (body : CIL.Method) : Prop where
  noOpaque : body.opaqueVectorLocals = []
  vectorArguments : body.vectorArgs = []
  parameterHomes : body.parameterHomes = []
  layouts : ∀ kind ∈ body.localKinds, localWidth kind < nativeLimit ∧
    ∀ width writable, kind = .span width writable → (0 < width ∧ width < 2^64)

/-- Ordinary unmodeled declarations whose physical home creation is supported. -/
structure UnmodeledFrame (body : CIL.Method) : Prop where
  initializers : body.locals = body.localKinds.map (fun _ => .unmodeled)
  noOpaque : body.opaqueVectorLocals = []
  vectorArguments : body.vectorArgs = []
  parameterHomes : body.parameterHomes = []
  layouts : ∀ kind ∈ body.localKinds, localWidth kind < nativeLimit ∧
    ∀ width writable, kind = .span width writable → (0 < width ∧ width < 2^64)

/-- Entering a nested call adds its activation pair without changing existing scope witnesses. -/
def enterScopes (scopes : Nat → Nat → Prop) (source target : Nat) : Nat → Nat → Prop :=
  fun left right => scopes left right ∨ (left = source ∧ right = target)

/-- Existing activation correspondences remain valid after entering another frame. -/
theorem enterScopes_existing (scopes : Nat → Nat → Prop) (source target left right : Nat)
    (scope : scopes left right) : enterScopes scopes source target left right := Or.inl scope
#print axioms enterScopes_existing

/-- Newly entered activations are related even when their fresh allocation counters differ. -/
theorem enterScopes_new (scopes : Nat → Nat → Prop) (source target : Nat) :
    enterScopes scopes source target source target := Or.inr ⟨rfl, rfl⟩
#print axioms enterScopes_new

/-- Ordinary frame entry allocates corresponding retained homes and private deleted homes. -/
theorem Memory.Renamed.enterFrameUnmodeled {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    {sourceBody targetBody : CIL.Method} (sourceReady : UnmodeledFrame sourceBody)
    (targetReady : UnmodeledFrame targetBody) (indices : LocalIndexMap)
    (selected : indices.Selects Eq sourceBody.localKinds targetBody.localKinds)
    (sourceArgs targetArgs : List Value) :
    ∃ later sourceFrame targetFrame sourceAfter targetAfter,
      mapping.Extends later ∧
      enterFrame sourceBody sourceArgs source = .ok (sourceFrame, sourceAfter) ∧
      enterFrame targetBody targetArgs target = .ok (targetFrame, targetAfter) ∧
      Memory.Renamed later (enterScopes scopes source.nextIdentity target.nextIdentity)
        sourceAfter targetAfter ∧
      Frame.Renamed indices later (enterScopes scopes source.nextIdentity target.nextIdentity)
        sourceFrame targetFrame := by
  let enteredScopes := enterScopes scopes source.nextIdentity target.nextIdentity
  have extended : Memory.Renamed mapping enteredScopes source target :=
    related.extendScopes (fun left right scope => Or.inl scope)
  obtain ⟨later, sourceSlots, targetSlots, sourceOwned, targetOwned, sourceAfter, targetAfter,
    extension, sourceMade, targetMade, remains, slots, owned⟩ :=
    extended.makeLocalsUnmodeled sourceFormed targetFormed staticBounds source.nextIdentity
      target.nextIdentity (enterScopes_new _ _ _) selected targetReady.layouts
  let sourceFrame : Frame := ⟨source.nextIdentity, sourceSlots, sourceOwned, [], 0⟩
  let targetFrame : Frame := ⟨target.nextIdentity, targetSlots, targetOwned, [], 0⟩
  refine ⟨later, sourceFrame, targetFrame, sourceAfter, targetAfter, extension,
    ?_, ?_, remains, ?_⟩
  · simp only [enterFrame_of_no_opaque _ _ _ sourceReady.noOpaque, sourceReady.initializers,
      sourceMade, sourceReady.vectorArguments, sourceReady.parameterHomes]
    simp only [makeArgumentHomes, makeParameterHomes, Bind.bind, Except.bind,
      Pure.pure, Except.pure, List.map_nil, List.append_nil, sourceFrame]
  · simp only [enterFrame_of_no_opaque _ _ _ targetReady.noOpaque, targetReady.initializers,
      targetMade, targetReady.vectorArguments, targetReady.parameterHomes]
    simp only [makeArgumentHomes, makeParameterHomes, Bind.bind, Except.bind,
      Pure.pure, Except.pure, List.map_nil, List.append_nil, targetFrame]
  refine ⟨enterScopes_new _ _ _, slots, owned, rfl, ?_, rfl⟩
  intro home member
  cases member
#print axioms Memory.Renamed.enterFrameUnmodeled

/-- Successful frame entry preserves retained initializers and inserts only private dead homes. -/
theorem Memory.Renamed.enterFrameInitialized {mapping : AllocationRenaming}
    {scopes : Nat → Nat → Prop} {source target : Memory}
    (related : Memory.Renamed mapping scopes source target)
    (sourceFormed : source.WellFormed) (targetFormed : target.WellFormed)
    (staticBounds : ∀ binding ∈ source.staticBindings,
      binding.2.allocation < mapping.sourceLimit)
    {sourceBody targetBody : CIL.Method} (sourceReady : OrdinaryFrame sourceBody)
    (targetReady : OrdinaryFrame targetBody) (indices : LocalIndexMap)
    (selected : LocalDeclarations indices sourceBody.localKinds sourceBody.locals
      targetBody.localKinds targetBody.locals)
    (sourceArgs targetArgs : List Value) {frame : Frame} {after : Memory}
    (entered : enterFrame sourceBody sourceArgs source = .ok (frame, after)) :
    ∃ later sourceFrame targetFrame sourceAfter targetAfter,
      mapping.Extends later ∧
      enterFrame sourceBody sourceArgs source = .ok (sourceFrame, sourceAfter) ∧
      enterFrame targetBody targetArgs target = .ok (targetFrame, targetAfter) ∧
      Memory.Renamed later (enterScopes scopes source.nextIdentity target.nextIdentity)
        sourceAfter targetAfter ∧
      Frame.Renamed indices later (enterScopes scopes source.nextIdentity target.nextIdentity)
        sourceFrame targetFrame := by
  have originalEntry := entered
  simp only [enterFrame_of_no_opaque _ _ _ sourceReady.noOpaque,
    sourceReady.vectorArguments, sourceReady.parameterHomes, Bind.bind, Except.bind] at entered
  split at entered
  · cases entered
  rename_i locals made
  rcases locals with ⟨sourceSlots, sourceOwned, sourceAfter⟩
  simp only [makeArgumentHomes, makeParameterHomes,
    Pure.pure, Except.pure, List.map_nil, List.append_nil,
    Except.ok.injEq, Prod.mk.injEq] at entered
  obtain ⟨rfl, rfl⟩ := entered
  let enteredScopes := enterScopes scopes source.nextIdentity target.nextIdentity
  have extended : Memory.Renamed mapping enteredScopes source target :=
    related.extendScopes (fun left right scope => Or.inl scope)
  obtain ⟨later, targetSlots, targetOwned, targetAfter, extension, targetMade,
    remains, slots, owned⟩ :=
    extended.makeLocalsInitialized sourceFormed targetFormed staticBounds source.nextIdentity
      target.nextIdentity (enterScopes_new _ _ _) selected targetReady.layouts made
  let targetFrame : Frame := ⟨target.nextIdentity, targetSlots, targetOwned, [], 0⟩
  refine ⟨later, _, targetFrame, sourceAfter, targetAfter, extension, originalEntry,
    ?_, remains, ?_⟩
  · simp only [enterFrame_of_no_opaque _ _ _ targetReady.noOpaque,
      targetMade, targetReady.vectorArguments, targetReady.parameterHomes]
    simp only [makeArgumentHomes, makeParameterHomes, Bind.bind, Except.bind,
      Pure.pure, Except.pure, List.map_nil, List.append_nil, targetFrame]
  refine ⟨enterScopes_new _ _ _, slots, owned, rfl, ?_, rfl⟩
  intro home member
  cases member
#print axioms Memory.Renamed.enterFrameInitialized

/-- A sequential computation cannot introduce a throw when neither component can throw. -/
private theorem bind_not_thrown (first : ExecutionResult α) (next : α → ExecutionResult β)
    (exception : String) (firstSafe : first ≠ .error (.thrown exception))
    (nextSafe : ∀ value, next value ≠ .error (.thrown exception)) :
    (first >>= next) ≠ .error (.thrown exception) := by
  cases first <;> simp_all [Bind.bind, Except.bind]
#print axioms bind_not_thrown

/-- Checked memory operations report memory faults, not named CLR exceptions. -/
private theorem checkedAt_not_thrown (reference : ManagedReference) (width : Nat)
    (result : Checked α) (exception : String) :
    checkedAt reference width result ≠ .error (.thrown exception) := by
  cases result <;> simp [checkedAt, Except.mapError]
#print axioms checkedAt_not_thrown

/-- Scalar encoding reports kind mismatches without raising CLR exceptions. -/
theorem localNumber_not_thrown (kind : CIL.LocalKind) (initial : CIL.Value)
    (exception : String) : localNumber kind initial ≠ .error (.thrown exception) := by
  intro failed
  unfold localNumber at failed
  repeat' first | (solve | cases failed) | split at failed
#print axioms localNumber_not_thrown

/-- Initializing a byte home cannot raise a named CLR exception. -/
theorem storeLocal_scalar_not_thrown (memory : Memory) (kind : CIL.LocalKind)
    (reference : Reference) (initial : CIL.Value) (exception : String) :
    storeLocal memory (.bytes kind reference) (.scalar initial) ≠ .error (.thrown exception) := by
  dsimp only [storeLocal]
  split
  · intro failed; cases failed
  · cases initial with
    | snapshot shape bytes =>
      dsimp only
      split
      · intro failed; cases failed
      · apply bind_not_thrown
        · exact checkedAt_not_thrown _ _ _ _
        · intro value failed; cases failed
    | _ =>
      apply bind_not_thrown
      · exact localNumber_not_thrown _ _ _
      · intro number
        apply bind_not_thrown
        · exact checkedAt_not_thrown _ _ _ _
        · intro value failed; cases failed
#print axioms storeLocal_scalar_not_thrown

/-- Fresh home allocation reports checked memory faults rather than CLR exceptions. -/
theorem allocateHome_not_thrown (memory : Memory) (activation width alignment : Nat)
    (exception : String) :
    allocateHome memory activation width alignment ≠ .error (.thrown exception) := by
  intro failed
  unfold allocateHome checkedAt at failed
  repeat' first
    | (solve | cases failed)
    | split at failed
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.mapError] at failed
  all_goals repeat' first | contradiction | split at * | simp_all only [Except.error.injEq]
#print axioms allocateHome_not_thrown

/-- Local declaration setup reports model faults, never a named CLR exception. -/
theorem makeLocal_not_thrown (activation : Nat) (kind : CIL.LocalKind) (initial : CIL.Value)
    (memory : Memory) (exception : String) :
    makeLocal activation kind initial memory ≠ .error (.thrown exception) := by
  intro failed
  have homes := allocateHome_not_thrown memory activation (localWidth kind)
    (localAlignment kind) exception
  have stores (memory : Memory) (reference : Reference) :=
    storeLocal_scalar_not_thrown memory kind reference initial exception
  unfold makeLocal at failed
  repeat' first
    | (solve | cases failed)
    | split at failed
    | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at failed
  all_goals cases failed
  all_goals first | exact homes (by assumption) | exact stores _ _ (by assumption)
#print axioms makeLocal_not_thrown

/-- A list of local initializers cannot synthesize a named CLR exception. -/
theorem makeLocals_not_thrown (activation : Nat) (kinds : List CIL.LocalKind)
    (initials : List CIL.Value) (memory : Memory) (exception : String) :
    makeLocals activation kinds initials memory ≠ .error (.thrown exception) := by
  induction kinds generalizing initials memory with
  | nil => cases initials <;> simp [makeLocals, Pure.pure, Except.pure]
  | cons kind kinds induction =>
    cases initials with
    | nil => simp [makeLocals]
    | cons initial initials =>
      intro failed
      simp only [makeLocals, Bind.bind, Except.bind] at failed
      split at failed
      · rename_i reason localFailed
        cases failed
        exact makeLocal_not_thrown _ _ _ _ _ localFailed
      · rename_i prepared localMade
        split at failed
        · rename_i reason restFailed
          cases failed
          exact induction _ _ restFailed
        · cases failed
#print axioms makeLocals_not_thrown

/-- Ordinary frame entry cannot manufacture a named CLR exception. -/
theorem enterFrame_not_thrown (body : CIL.Method) (ready : OrdinaryFrame body)
    (arguments : List Value) (memory : Memory) (exception : String) :
    enterFrame body arguments memory ≠ .error (.thrown exception) := by
  intro failed
  simp only [enterFrame_of_no_opaque _ _ _ ready.noOpaque,
    ready.vectorArguments, ready.parameterHomes, Bind.bind, Except.bind] at failed
  split at failed
  · rename_i reason localsFailed
    cases failed
    exact makeLocals_not_thrown _ _ _ _ _ localsFailed
  · simp only [makeArgumentHomes, makeParameterHomes,
      Pure.pure, Except.pure] at failed
    cases failed
#print axioms enterFrame_not_thrown

end CIL.Safety
