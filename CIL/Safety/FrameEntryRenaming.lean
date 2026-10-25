import CIL.Safety.FrameRenaming

/-!
# Frame entry with dead numeric locals

The ordinary unmodeled declaration route used by the pinned Multiply consumer builds
both actual frames, deriving readiness from layout bounds and well-formed memory.
Opaque slots and argument or parameter homes have separate setup semantics and are
explicitly excluded by this entry theorem.
-/

namespace CIL.Safety

/-- Ordinary unmodeled declarations whose physical home creation is supported. -/
structure UnmodeledFrame (body : CIL.Method) : Prop where
  initializers : body.locals = body.localKinds.map (fun _ => .unmodeled)
  noOpaque : body.opaqueVectorLocals = []
  vectorArguments : body.vectorArgs = []
  parameterHomes : body.parameterHomes = []
  layouts : ∀ kind ∈ body.localKinds, localWidth kind < nativeLimit ∧
    ∀ width writable, kind = .span width writable → width ∈ [1, 2, 4, 8]

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

end CIL.Safety
