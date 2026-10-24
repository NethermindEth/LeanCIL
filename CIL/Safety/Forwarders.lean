import CIL.Safety.MethodContract
import CIL.Safety.ReturnArity
import CIL.Safety.ReturnReferences
import CIL.Safety.UnknownHomes
import CIL.Safety.ReturnMemory

/-!
# Forwarder contracts

A forwarder loads some of its arguments, calls another method with them and returns that
method's result: overload forwarders and instance-to-static wrappers compile to
`ldarg*; call callee; ret`. `MethodContract.Holds.forward` gives such a method the callee's
contract with the forwarder's own argument encoding, from the callee's `Holds` alone; the
argument order is data (`indices`), so no forwarder body is stepped by hand. Its frame
allocates nothing, so the callee's precondition, footprint and postcondition carry over
verbatim.

`MethodContract.Holds.forward_out` covers `ldarg*; ldloca 0; call callee; ret`, which also
passes a fresh local as an out argument and drops it. The callee then runs in the memory
after frame entry and its result is read after the local expires, so the forwarder's
contract is related to the callee's by premises over those two memories.
-/

namespace CIL.Safety

/-- What `ret narrow` returns unchanged: any values for a plain `ret`, and a single i32
    already in the narrow range for a narrowed one. -/
def ReturnsUnchanged : Option CIL.NarrowKind → List Value → Prop
  | none, _ => True
  | some kind, values => ∃ bits, values = [.scalar (.i32 bits)] ∧ kind.extend bits = bits

/-- The body that loads the arguments at `indices` in order, calls `callee` with them and
    returns its result through `ret narrow`. -/
def forwarderCode (indices : List Nat) (callee : Nat) (narrow : Option CIL.NarrowKind) :
    List CIL.Op :=
  indices.map (fun index => .arg index) ++ [.call callee indices.length, .ret narrow]

/-- `body` forwards its arguments at `indices` to `callee`, whose body is `calleeBody`,
    from a frame that allocates nothing, and declares the callee's return arity. -/
structure Forwards (body calleeBody : CIL.Method) (indices : List Nat) (callee : Nat)
    (narrow : Option CIL.NarrowKind) : Prop where
  code : body.code = forwarderCode indices callee narrow
  locals : body.locals = []
  localKinds : body.localKinds = []
  vectorArgs : body.vectorArgs = []
  parameterHomes : body.parameterHomes = []
  returnsValue : body.returnsValue = calleeBody.returnsValue

/-- `contract` with the arguments encoded by `forwarded` instead: what a forwarder to a
    method proving `contract` satisfies. -/
def MethodContract.forward {Input Output : Type} (contract : MethodContract Input Output)
    (forwarded : Input → List Value) : MethodContract Input Output :=
  { contract with args := forwarded }

/-- Values valid in `memory` pass the argument and result checks unchanged. -/
theorem checkedValues_of_valid {memory : Memory} {values : List Value}
    (valid : ValuesValid memory values) : values.mapM (checkedValue memory) = .ok values := by
  induction values with
  | nil => rfl
  | cons value rest restChecked =>
    have head := checkedValue_of_valid memory value (valid value (List.mem_cons_self ..))
    have tail := restChecked fun other member => valid other (List.mem_cons_of_mem _ member)
    simp only [List.mapM_cons, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms checkedValues_of_valid

/-- A frame that allocates nothing: entry keeps memory and the frame owns no allocation. -/
theorem Forwards.enterFrame {body calleeBody : CIL.Method} {indices : List Nat} {callee : Nat}
    {narrow : Option CIL.NarrowKind} (forwards : Forwards body calleeBody indices callee narrow)
    (args : List Value) (memory : Memory) :
    CIL.Safety.enterFrame body args memory =
      .ok (⟨memory.nextIdentity, [], [], []⟩, memory) := by
  have noLocals : makeSelectedLocals memory.nextIdentity body.opaqueVectorLocals [] []
      memory = .ok ([], [], memory) := by
    unfold makeSelectedLocals
    split
    · rfl
    · simp only [makeSelectedLocalsFrom]
  simp only [CIL.Safety.enterFrame, forwards.localKinds, forwards.locals, forwards.vectorArgs,
    forwards.parameterHomes, noLocals, makeArgumentHomes, makeParameterHomes, Bind.bind,
    Except.bind, Pure.pure, Except.pure, List.map_nil, List.append_nil]

#print axioms Forwards.enterFrame

/-- Loading the arguments at `indices` from `pc` on pushes `loaded` in order; any
    continuation from the following pc composes. -/
theorem run_load_arguments {program : CIL.Program} {method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory : Memory} {post : Memory → List Value → Prop}
    (found : program[method]? = some body) (valid : ValuesValid memory args) :
    ∀ (indices : List Nat) (pc : Nat) (stack loaded : List Value),
      (∀ position index, indices[position]? = some index →
        body.code[pc + position]? = some (.arg index)) →
      indices.map (fun index => args[index]?) = loaded.map some →
      (∃ fuel result returned,
        run program fuel method (pc + indices.length) args frame (loaded.reverse ++ stack)
          memory = .ok (result, returned) ∧ post result returned) →
      ∃ fuel result returned,
        run program fuel method pc args frame stack memory = .ok (result, returned) ∧
          post result returned := by
  intro indices
  induction indices with
  | nil =>
    intro pc stack loaded _ selected continuation
    cases loaded with
    | nil => simpa using continuation
    | cons _ _ => cases selected
  | cons index rest restLoads =>
    intro pc stack loaded fetched selected continuation
    cases loaded with
    | nil => cases selected
    | cons value values =>
      simp only [List.map_cons, List.cons.injEq] at selected
      obtain ⟨present, selected⟩ := selected
      have checked := checkedValue_of_valid memory value
        (valid value (List.mem_of_getElem? present))
      have stepped : step body (.arg index) pc args frame stack memory =
          .ok (.next (pc + 1) (value :: stack) frame memory) := by
        simp only [step_argument_eq, present, checked, Bind.bind, Except.bind, Pure.pure,
          Except.pure]
      refine run_next_exists post found (by simpa using fetched 0 index rfl) stepped ?_
      refine restLoads (pc + 1) (value :: stack) values
        (fun position other located => ?_) selected ?_
      · simpa [Nat.add_assoc, Nat.add_comm 1 position] using
          fetched (position + 1) other located
      · simpa [Nat.add_assoc, Nat.add_comm 1 rest.length] using continuation

#print axioms run_load_arguments

/-- A call whose arguments are exactly the stack, valid and fully specified, passes them to
    the callee in push order and leaves an empty stack. -/
theorem step_call_loaded {body : CIL.Method} {callee pc : Nat} {args : List Value}
    {frame : Frame} {memory : Memory} {arguments : List Value}
    (valid : ValuesValid memory arguments) (known : arguments.any Value.hasUnspecified = false) :
    step body (.call callee arguments.length) pc args frame arguments.reverse memory =
      .ok (.call callee arguments [] memory) := by
  have taken : arguments.reverse.take arguments.length = arguments.reverse :=
    List.take_of_length_le (by simp)
  have exposed : unspecifiedOperands arguments.length arguments.reverse = false := by
    rw [unspecifiedOperands, taken, List.any_reverse, known]
  simp only [step, observerCount, exposed, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    List.length_reverse, Nat.lt_irrefl, taken, List.reverse_reverse,
    checkedValues_of_valid valid, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [List.drop_of_length_le (by simp)]

#print axioms step_call_loaded

/-- `ret narrow` returns a callee's checked, fully specified result of the declared arity
    unchanged. -/
theorem step_return_unchanged {body : CIL.Method} {narrow : Option CIL.NarrowKind} {pc : Nat}
    {args : List Value} {frame : Frame} {memory : Memory} {values : List Value}
    (arity : values.length = if body.returnsValue then 1 else 0)
    (known : values.any Value.hasUnspecified = false)
    (checked : values.mapM (checkedValue memory) = .ok values)
    (unchanged : ReturnsUnchanged narrow values) :
    step body (.ret narrow) pc args frame values memory = .ok (.returned values memory) := by
  cases narrow with
  | none =>
    have hidden : unspecifiedOperands 1 values = false := by
      simp only [unspecifiedOperands, List.any_eq_false] at known ⊢
      exact fun value member => known value (List.mem_of_mem_take member)
    simp only [step_return_eq, hidden, Bool.false_eq_true, ↓reduceIte, arity, checked,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  | some kind =>
    obtain ⟨bits, rfl, same⟩ := unchanged
    have returns : body.returnsValue = true := by
      cases returning : body.returnsValue <;> simp_all
    rw [step_return_narrow_eq, returns, same]
    rfl

#print axioms step_return_unchanged

/-- From a stack holding a callee's arguments in push order, `call callee; ret narrow`
    returns what the callee's contract promises from the current memory, in the memory
    left once the frame expires. -/
theorem run_forward_call {Input Output : Type} {contract : MethodContract Input Output}
    {program : CIL.Program} {method callee pc : Nat} {body calleeBody : CIL.Method}
    {narrow : Option CIL.NarrowKind} {args : List Value} {frame : Frame} {memory : Memory}
    {input : Input} {post : Memory → List Value → Prop}
    (holds : contract.Holds program callee)
    (found : program[method]? = some body) (calleeFound : program[callee]? = some calleeBody)
    (callFetched : body.code[pc]? = some (.call callee (contract.args input).length))
    (returnFetched : body.code[pc + 1]? = some (.ret narrow))
    (returnsValue : body.returnsValue = calleeBody.returnsValue)
    (unchanged : ∀ final out, contract.post input memory final out →
      ReturnsUnchanged narrow (contract.results out))
    (permitted : contract.pre input memory)
    (known : (contract.args input).any Value.hasUnspecified = false)
    (survives : ∀ final values, ValuesValid final values →
      contract.Returns input memory final values → ValuesValid (leaveFrame frame final) values)
    (continuation : ∀ final values, Confined (contract.footprint input) memory final →
      contract.Returns input memory final values → post (leaveFrame frame final) values) :
    ∃ fuel result returned,
      run program fuel method pc args frame (contract.args input).reverse memory =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨_, _, _, invoked, _, _⟩ := holds input memory permitted
  obtain ⟨_, _, _, _, _, calleeChecked, _, _⟩ := invoke_success_setup invoked
  have calleeValid : ValuesValid memory (contract.args input) := by
    obtain ⟨same, valid⟩ := checkedValues_valid _ _ _ calleeChecked
    exact same ▸ valid
  refine run_call_of_contract holds input found callFetched
    (step_call_loaded calleeValid known) rfl permitted ?_
  intro final values ⟨_, called⟩ framed returns
  have arity : values.length = if body.returnsValue then 1 else 0 := by
    obtain ⟨_, _, _, _, _, _, _, ran⟩ := invoke_success_setup called
    rw [returnsValue]
    exact run_return_length _ _ _ _ _ _ _ _ _ _ _ calleeFound ran
  have valid := invoke_result_valid _ _ _ _ _ _ _ called
  obtain ⟨out, encoded, satisfied⟩ := id returns
  refine run_return_exists found returnFetched ?_
    (checkedValues_of_valid (survives final values valid returns))
    (continuation final values framed returns)
  rw [List.append_nil]
  exact step_return_unchanged arity (invoke_return_known called) (checkedValues_of_valid valid)
    (encoded ▸ unchanged final out satisfied)

#print axioms run_forward_call

/-- A forwarder inherits its callee's contract: it meets `pre`, `footprint` and `post`
    unchanged, with arguments encoded by `forwarded`. The callee's arguments must be the
    forwarder's at `indices`, every forwarder argument must reach the callee (the forwarder
    checks them all), the call must expose no unspecified vector bits, and a narrowed
    return must not change the callee's result. -/
theorem MethodContract.Holds.forward {Input Output : Type}
    {contract : MethodContract Input Output}
    {program : CIL.Program} {method callee : Nat} {body calleeBody : CIL.Method}
    {indices : List Nat} {narrow : Option CIL.NarrowKind} {forwarded : Input → List Value}
    (holds : contract.Holds program callee)
    (found : program[method]? = some body) (calleeFound : program[callee]? = some calleeBody)
    (forwards : Forwards body calleeBody indices callee narrow)
    (selected : ∀ input,
      indices.map (fun index => (forwarded input)[index]?) = (contract.args input).map some)
    (covered : ∀ input, ∀ value ∈ forwarded input, value ∈ contract.args input)
    (known : ∀ input initial, contract.pre input initial →
      (contract.args input).any Value.hasUnspecified = false)
    (unchanged : ∀ input initial final out, contract.post input initial final out →
      ReturnsUnchanged narrow (contract.results out)) :
    (contract.forward forwarded).Holds program method := by
  intro input initial permitted
  obtain ⟨_, _, _, invoked, _, _⟩ := holds input initial permitted
  obtain ⟨_, _, _, _, _, calleeChecked, _, _⟩ := invoke_success_setup invoked
  have forwardedValid : ValuesValid initial (forwarded input) := by
    obtain ⟨same, valid⟩ := checkedValues_valid _ _ _ calleeChecked
    subst same
    exact fun value member => valid value (covered input value member)
  have length : (contract.args input).length = indices.length := by
    simpa using (congrArg List.length (selected input)).symm
  have fetched : ∀ pc : Nat, body.code[pc]? = (forwarderCode indices callee narrow)[pc]? := by
    rw [forwards.code]; exact fun _ => rfl
  refine invoke_exists_of_run found (checkedValues_of_valid forwardedValid)
    (forwards.enterFrame _ _) ?_
  refine run_load_arguments found forwardedValid indices 0 [] (contract.args input)
    (fun position index located => ?_) (selected input) ?_
  · have bound : position < indices.length := (List.getElem?_eq_some_iff.mp located).1
    rw [Nat.zero_add, fetched, forwarderCode,
      List.getElem?_append_left (by simpa using bound), List.getElem?_map, located]
    rfl
  rw [Nat.zero_add, List.append_nil]
  -- The frame owns nothing, so leaving it keeps the callee's final memory.
  exact run_forward_call holds found calleeFound (by simp [fetched, forwarderCode, length])
    (by simp [fetched, forwarderCode]) forwards.returnsValue (unchanged input initial) permitted
    (known input initial permitted) (fun _ _ valid _ => valid)
    (fun _ _ framed returns => ⟨framed, returns⟩)

#print axioms MethodContract.Holds.forward

/-- The body that loads the arguments at `indices` in order and then the address of local 0,
    calls `callee` with them and returns its result through `ret narrow`. -/
def outForwarderCode (indices : List Nat) (callee : Nat) (narrow : Option CIL.NarrowKind) :
    List CIL.Op :=
  indices.map (fun index => .arg index) ++
    [.localAddr 0, .call callee (indices.length + 1), .ret narrow]

/-- `body` forwards its arguments at `indices` to `callee`, whose body is `calleeBody`, with
    the address of its only local, an `.unmodeled` home of `kind`, as a last out argument
    whose contents it drops; it declares the callee's return arity. -/
structure ForwardsOut (body calleeBody : CIL.Method) (indices : List Nat) (callee : Nat)
    (narrow : Option CIL.NarrowKind) (kind : CIL.LocalKind) : Prop where
  code : body.code = outForwarderCode indices callee narrow
  locals : body.locals = [.unmodeled]
  localKinds : body.localKinds = [kind]
  numeric : kind ≠ .reference
  opaqueVectorLocals : body.opaqueVectorLocals = []
  vectorArgs : body.vectorArgs = []
  parameterHomes : body.parameterHomes = []
  returnsValue : body.returnsValue = calleeBody.returnsValue

/-- A callee confined to fresh frame storage and to entries inside `footprint`, run between a
    frame entry and exit that keep memory below the caller's `nextIdentity`, is confined to
    `footprint` as the caller sees it. -/
theorem Confined.across_frame {footprint inner : List (Reference × Nat)}
    {initial entered final left : Memory}
    (entry : MemoryBelow initial.nextIdentity initial entered)
    (enterGrows : initial.nextIdentity ≤ entered.nextIdentity)
    (framed : Confined inner entered final)
    (exit : MemoryBelow initial.nextIdentity final left)
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
    fun id bound => (exit.allocations id bound).trans
      ((framed.allocations id (old bound)).trans (entry.allocations id bound)),
    fun id bound offset outside => (exit.cells id bound offset).trans
      ((framed.cells id (old bound) offset (narrow bound outside)).trans
        (entry.cells id bound offset)),
    fun id bound offset => (exit.permissions id bound offset true).trans
      ((framed.writable id (old bound) offset).trans (entry.permissions id bound offset true)),
    fun id bound offset outside => (exit.permissions id bound offset false).trans
      ((framed.readable id (old bound) offset (narrow bound outside)).trans
        (entry.permissions id bound offset false))⟩

#print axioms Confined.across_frame

/-- A forwarder that passes a fresh local as a last out argument and drops it meets `outer`
    when its callee meets `inner` at `extend input home`, `home` being that local. The
    callee's arguments must be the forwarder's at `indices` and then `home`; its
    precondition must follow from `outer.pre` in the memory after frame entry, where `home` is
    fresh and writable; its footprint may name fresh storage or lie inside `outer.footprint`;
    its postcondition must give `outer.post` once the frame has expired; and its results must
    be scalars, which survive the expiry of `home`. -/
theorem MethodContract.Holds.forward_out {Outer Inner Output : Type}
    {outer : MethodContract Outer Output} {inner : MethodContract Inner Output}
    {program : CIL.Program} {method callee : Nat} {body calleeBody : CIL.Method}
    {indices : List Nat} {narrow : Option CIL.NarrowKind} {kind : CIL.LocalKind}
    (extend : Outer → Reference → Inner)
    (holds : inner.Holds program callee)
    (found : program[method]? = some body) (calleeFound : program[callee]? = some calleeBody)
    (forwards : ForwardsOut body calleeBody indices callee narrow kind)
    (selected : ∀ input home,
      indices.map (fun index => (outer.args input)[index]?) ++
          [some (.reference (.address home))] =
        (inner.args (extend input home)).map some)
    (checked : ∀ input initial, outer.pre input initial →
      initial.WellFormed ∧ ValuesValid initial (outer.args input))
    (known : ∀ input home, (inner.args (extend input home)).any Value.hasUnspecified = false)
    (unchanged : ∀ input entered final out, inner.post input entered final out →
      ReturnsUnchanged narrow (inner.results out))
    (results : ∀ out, outer.results out = inner.results out)
    (scalars : ∀ input entered final out, inner.post input entered final out →
      ∀ value ∈ inner.results out, ∃ scalar, value = .scalar scalar)
    (entered : ∀ input initial entered home, outer.pre input initial →
      MemoryBelow initial.nextIdentity initial entered → entered.WellFormed →
      initial.nextIdentity ≤ home.allocation →
      access entered home (localWidth kind) 1 true = .ok () →
      inner.pre (extend input home) entered)
    (footprint : ∀ input initial home, outer.pre input initial →
      initial.nextIdentity ≤ home.allocation →
      ∀ entry ∈ inner.footprint (extend input home),
        initial.nextIdentity ≤ entry.1.allocation ∨
          ∃ outerEntry ∈ outer.footprint input, Within entry outerEntry)
    (returned : ∀ input initial entered final left home out, outer.pre input initial →
      MemoryBelow initial.nextIdentity initial entered →
      MemoryBelow initial.nextIdentity final left → initial.nextIdentity ≤ home.allocation →
      Confined (inner.footprint (extend input home)) entered final →
      Confined (outer.footprint input) initial left →
      inner.post (extend input home) entered final out → outer.post input initial left out) :
    outer.Holds program method := by
  intro input initial permitted
  obtain ⟨formed, outerValid⟩ := checked input initial permitted
  obtain ⟨frame, memory, setup, homes, entryBelow, memoryFormed⟩ :=
    unknown_frame_setup body (by rw [forwards.locals, forwards.localKinds]; rfl)
      (by rw [forwards.localKinds]; simpa using forwards.numeric) forwards.vectorArgs
      forwards.parameterHomes forwards.opaqueVectorLocals initial (outer.args input) formed
  obtain ⟨home, slot, fresh, writable⟩ :=
    homes.home_at 0 kind (by rw [forwards.localKinds]; rfl)
  have owned := enterFrame_fresh _ _ _ _ _ setup
  have calleePre := entered input initial memory home permitted entryBelow memoryFormed fresh
    writable
  obtain ⟨loaded, rest, split, loadedSome, restSome⟩ :=
    List.map_eq_append_iff.mp (selected input home).symm
  have restHome : rest = [.reference (.address home)] := by
    cases rest with
    | nil => cases restSome
    | cons value more =>
      cases more with
      | nil => simpa using restSome
      | cons _ _ => cases restSome
  subst restHome
  have length : (inner.args (extend input home)).length = indices.length + 1 := by
    rw [split]; simpa using (congrArg List.length loadedSome)
  have fetched : ∀ pc : Nat,
      body.code[pc]? = (outForwarderCode indices callee narrow)[pc]? := by
    rw [forwards.code]; exact fun _ => rfl
  have memoryValid := outerValid.preserve formed owned.1
  refine invoke_exists_of_run found (checkedValues_of_valid outerValid) setup ?_
  refine run_load_arguments found memoryValid indices 0 [] loaded
    (fun position index located => ?_) loadedSome.symm ?_
  · have bound : position < indices.length := (List.getElem?_eq_some_iff.mp located).1
    rw [Nat.zero_add, fetched, outForwarderCode,
      List.getElem?_append_left (by simpa using bound), List.getElem?_map, located]
    rfl
  rw [Nat.zero_add, List.append_nil]
  have addressed : step body (.localAddr 0) indices.length (outer.args input) frame
      loaded.reverse memory =
        .ok (.next (indices.length + 1) (.reference (.address home) :: loaded.reverse) frame
          memory) := by
    have formedHome := access_reference_valid _ _ _ _ _ writable
    simp only [step, observerCount, unspecifiedOperands, List.take_zero, List.any_nil,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte, slot, localAddress, formValue, checkedAt,
      formedHome, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine run_next_exists _ found (by simp [fetched, outForwarderCode]) addressed ?_
  have stack : .reference (.address home) :: loaded.reverse =
      (inner.args (extend input home)).reverse := by
    rw [split]; simp
  rw [stack]
  have exitFresh : ∀ id ∈ frame.owned, initial.nextIdentity ≤ id :=
    fun id member => (owned.2 id member).1
  refine run_forward_call holds found calleeFound
    (by rw [length]; simp [fetched, outForwarderCode])
    (by
      rw [fetched, outForwarderCode, List.getElem?_append_right (by simp; omega)]
      simp [show indices.length + 1 + 1 - indices.length = 2 by omega])
    forwards.returnsValue (unchanged (extend input home) memory) calleePre
    (known input home) (fun final values valid returns => ?_)
    (fun final values framed returns => ?_)
  · obtain ⟨out, encoded, satisfied⟩ := returns
    intro value member
    obtain ⟨scalar, same⟩ := scalars _ _ _ out satisfied value (encoded ▸ member)
    subst same
    exact valid _ member
  · have exitBelow := leaveFrame_preserves_memory_below frame final _ exitFresh
    have confined := Confined.across_frame entryBelow owned.1.next framed exitBelow
      (Nat.le_of_eq (leaveFrame_nextIdentity frame final).symm)
      (footprint input initial home permitted fresh)
    obtain ⟨out, encoded, satisfied⟩ := returns
    exact ⟨confined, out, encoded.trans (results out).symm,
      returned input initial memory final _ home out permitted entryBelow exitBelow fresh
        framed confined satisfied⟩

#print axioms MethodContract.Holds.forward_out

end CIL.Safety
