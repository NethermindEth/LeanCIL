import CIL.Safety.MethodContract
import CIL.Safety.ReturnArity
import CIL.Safety.ReturnReferences
import CIL.Safety.UnknownHomes
import CIL.Safety.ReturnMemory
import CIL.Safety.FrameProgress
import CIL.Safety.WordMemory
import CIL.Safety.NumericLocals

/-!
# Forwarder contracts

A forwarder loads some of its arguments, calls another method with them and returns that
method's result: overload forwarders and instance-to-static wrappers compile to
`ldarg*; call callee; ret`. `MethodContract.Holds.forward` gives such a method the callee's
contract with the forwarder's own argument encoding, from the callee's `Holds` and premises
that the arguments and the returned value pass through unchanged; the loads are data
(`loads`: an argument index and the narrowing the extractor attaches to small integer
parameters), so no forwarder body is stepped by hand. Its frame allocates nothing, so the
callee's precondition, footprint and postcondition carry over verbatim.

`MethodContract.Holds.forward_out` covers `ldarg*; ldloca 0; call callee; ret`, which also
passes a fresh local as an out argument and drops it. The local may be uninitialized or
zero-initialized, as the extractor emits it without or with `InitLocals`. The callee then
runs in the memory after frame entry and its result is read after the local expires, so the
forwarder's contract is related to the callee's by premises over those two memories.
-/

namespace CIL.Safety

/-- What `ret narrow` returns unchanged: any values for a plain `ret`, and a single i32
    already in the narrow range for a narrowed one. -/
def ReturnsUnchanged : Option CIL.NarrowKind → List Value → Prop
  | none, _ => True
  | some kind, values => ∃ bits, values = [.scalar (.i32 bits)] ∧ kind.extend bits = bits

/-- What `.arg index narrow` pushes unchanged: any argument for a plain load, and an i32
    already in the narrow range for a narrowed one. -/
def LoadsUnchanged : Option CIL.NarrowKind → Value → Prop
  | none, _ => True
  | some kind, value => ∃ bits, value = .scalar (.i32 bits) ∧ kind.extend bits = bits

/-- Plain loads of the arguments at `indices`, as emitted for parameters wider than 16 bits. -/
def plainLoads (indices : List Nat) : List (Nat × Option CIL.NarrowKind) :=
  indices.map fun index => (index, none)

/-- Plain loads push every argument unchanged. -/
theorem plainLoads_unchanged (indices : List Nat) (values : List Value) :
    ∀ pair ∈ (plainLoads indices).zip values, LoadsUnchanged pair.1.2 pair.2 := by
  intro ⟨⟨index, narrow⟩, value⟩ member
  have loaded := (List.of_mem_zip member).1
  simp only [plainLoads, List.mem_map, Prod.mk.injEq] at loaded
  obtain ⟨_, _, _, rfl⟩ := loaded
  trivial

#print axioms plainLoads_unchanged

/-- The body that performs `loads` in order, calls `callee` with the loaded values and
    returns its result through `ret narrow`. -/
def forwarderCode (loads : List (Nat × Option CIL.NarrowKind)) (callee : Nat)
    (narrow : Option CIL.NarrowKind) : List CIL.Op :=
  loads.map (fun load => .arg load.1 load.2) ++ [.call callee loads.length, .ret narrow]

/-- `body` forwards the arguments it loads by `loads` to `callee`, whose body is
    `calleeBody`, from a frame that allocates nothing, and declares the callee's return
    arity. -/
structure Forwards (body calleeBody : CIL.Method) (loads : List (Nat × Option CIL.NarrowKind))
    (callee : Nat) (narrow : Option CIL.NarrowKind) : Prop where
  code : body.code = forwarderCode loads callee narrow
  locals : body.locals = []
  localKinds : body.localKinds = []
  vectorArgs : body.vectorArgs = []
  parameterHomes : body.parameterHomes = []
  returnsValue : body.returnsValue = calleeBody.returnsValue

/-- `contract` with the arguments encoded by `args` instead: what a forwarder to a method
    proving `contract` satisfies. -/
def MethodContract.withArgs {Input Output : Type} (contract : MethodContract Input Output)
    (args : Input → List Value) : MethodContract Input Output :=
  { contract with args := args }

/-- A frame that allocates nothing: entry keeps memory and the frame owns no allocation. -/
theorem Forwards.enterFrame {body calleeBody : CIL.Method}
    {loads : List (Nat × Option CIL.NarrowKind)} {callee : Nat}
    {narrow : Option CIL.NarrowKind} (forwards : Forwards body calleeBody loads callee narrow)
    (args : List Value) (memory : Memory) :
    CIL.Safety.enterFrame body args memory =
      .ok (⟨memory.nextIdentity, [], [], [], 0⟩, memory) := by
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

/-- A load of a checked argument that its narrowing keeps pushes that argument. -/
theorem step_load_unchanged {body : CIL.Method} {index pc : Nat}
    {narrow : Option CIL.NarrowKind} {args stack : List Value} {frame : Frame}
    {memory : Memory} {value : Value} (present : args[index]? = some value)
    (checked : checkedValue memory value = .ok value) (unchanged : LoadsUnchanged narrow value) :
    step body (.arg index narrow) pc args frame stack memory =
      .ok (.next (pc + 1) (value :: stack) frame memory) := by
  cases narrow with
  | none =>
    simp only [step_argument_eq, present, checked, Bind.bind, Except.bind, Pure.pure,
      Except.pure]
  | some kind =>
    obtain ⟨bits, rfl, same⟩ := unchanged
    simp only [step, observerCount, unspecifiedOperands, List.take_zero, List.any_nil, present,
      Option.map_some, Option.getD_some, Value.hasUnspecified, CIL.Value.hasUnspecified,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte, same, checked, Bind.bind, Except.bind,
      Pure.pure, Except.pure]

#print axioms step_load_unchanged

/-- Performing `loads` from `pc` on pushes `loaded` in order when each load keeps its
    argument; any continuation from the following pc composes. -/
theorem run_load_arguments {program : CIL.Program} {method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory : Memory} {post : Memory → List Value → Prop}
    (found : program[method]? = some body) (valid : ValuesValid memory args) :
    ∀ (loads : List (Nat × Option CIL.NarrowKind)) (pc : Nat) (stack loaded : List Value),
      (∀ position load, loads[position]? = some load →
        body.code[pc + position]? = some (.arg load.1 load.2)) →
      loads.map (fun load => args[load.1]?) = loaded.map some →
      (∀ pair ∈ loads.zip loaded, LoadsUnchanged pair.1.2 pair.2) →
      (∃ fuel result returned,
        run program fuel method (pc + loads.length) args frame (loaded.reverse ++ stack)
          memory = .ok (result, returned) ∧ post result returned) →
      ∃ fuel result returned,
        run program fuel method pc args frame stack memory = .ok (result, returned) ∧
          post result returned := by
  intro loads
  induction loads with
  | nil =>
    intro pc stack loaded _ selected _ continuation
    cases loaded with
    | nil => simpa using continuation
    | cons _ _ => cases selected
  | cons load rest restLoads =>
    intro pc stack loaded fetched selected narrowed continuation
    cases loaded with
    | nil => cases selected
    | cons value values =>
      simp only [List.map_cons, List.cons.injEq] at selected
      obtain ⟨present, selected⟩ := selected
      have checked := checkedValue_of_valid memory value
        (valid value (List.mem_of_getElem? present))
      have stepped := step_load_unchanged (body := body) (pc := pc) (stack := stack)
        (frame := frame) present checked (narrowed (load, value) (by simp))
      refine run_next_exists post found (by simpa using fetched 0 load rfl) stepped ?_
      refine restLoads (pc + 1) (value :: stack) values
        (fun position other located => ?_) selected
        (fun pair member => narrowed pair (by simp [member])) ?_
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
    forwarder's selected by `loads`, each kept by its load's narrowing; each forwarder
    argument must reach the callee or be valid under `pre`, since the forwarder checks them
    all; the call must expose no unspecified vector bits; and a narrowed return must not
    change the callee's result. -/
theorem MethodContract.Holds.forward {Input Output : Type}
    {contract : MethodContract Input Output}
    {program : CIL.Program} {method callee : Nat} {body calleeBody : CIL.Method}
    {loads : List (Nat × Option CIL.NarrowKind)} {narrow : Option CIL.NarrowKind}
    {forwarded : Input → List Value}
    (holds : contract.Holds program callee)
    (found : program[method]? = some body) (calleeFound : program[callee]? = some calleeBody)
    (forwards : Forwards body calleeBody loads callee narrow)
    (selected : ∀ input,
      loads.map (fun load => (forwarded input)[load.1]?) = (contract.args input).map some)
    (narrowed : ∀ input initial, contract.pre input initial →
      ∀ pair ∈ loads.zip (contract.args input), LoadsUnchanged pair.1.2 pair.2)
    (covered : ∀ input initial, contract.pre input initial → ∀ value ∈ forwarded input,
      value ∈ contract.args input ∨ value.Valid initial)
    (known : ∀ input initial, contract.pre input initial →
      (contract.args input).any Value.hasUnspecified = false)
    (unchanged : ∀ input initial final out, contract.post input initial final out →
      ReturnsUnchanged narrow (contract.results out)) :
    (contract.withArgs forwarded).Holds program method := by
  intro input initial permitted
  obtain ⟨_, _, _, invoked, _, _⟩ := holds input initial permitted
  obtain ⟨_, _, _, _, _, calleeChecked, _, _⟩ := invoke_success_setup invoked
  have forwardedValid : ValuesValid initial (forwarded input) := by
    obtain ⟨same, valid⟩ := checkedValues_valid _ _ _ calleeChecked
    subst same
    exact fun value member =>
      (covered input initial permitted value member).elim (valid value) id
  have length : (contract.args input).length = loads.length := by
    simpa using (congrArg List.length (selected input)).symm
  have fetched : ∀ pc : Nat, body.code[pc]? = (forwarderCode loads callee narrow)[pc]? := by
    rw [forwards.code]; exact fun _ => rfl
  refine invoke_exists_of_run found (checkedValues_of_valid forwardedValid)
    (forwards.enterFrame _ _) ?_
  refine run_load_arguments found forwardedValid loads 0 [] (contract.args input)
    (fun position load located => ?_) (selected input) (narrowed input initial permitted) ?_
  · have bound : position < loads.length := (List.getElem?_eq_some_iff.mp located).1
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

/-- The body that performs `loads` in order, loads the address of local 0, calls `callee`
    with them and returns its result through `ret narrow`. -/
def outForwarderCode (loads : List (Nat × Option CIL.NarrowKind)) (callee : Nat)
    (narrow : Option CIL.NarrowKind) : List CIL.Op :=
  loads.map (fun load => .arg load.1 load.2) ++
    [.localAddr 0, .call callee (loads.length + 1), .ret narrow]

/-- `body` forwards the arguments it loads by `loads` to `callee`, whose body is
    `calleeBody`, with the address of its only local, a byte home of `kind` created from
    `initial`, as a last out argument whose contents it drops; it declares the callee's
    return arity. References, spans and arrays allocate no byte home, so `kind` is none of
    these. Any initializer that fits the kind is accepted; the extractor emits
    `.unmodeled` without `InitLocals` and the kind's zero with it. -/
structure ForwardsOut (body calleeBody : CIL.Method) (loads : List (Nat × Option CIL.NarrowKind))
    (callee : Nat) (narrow : Option CIL.NarrowKind) (kind : CIL.LocalKind) (initial : CIL.Value) :
    Prop where
  code : body.code = outForwarderCode loads callee narrow
  locals : body.locals = [initial]
  localKinds : body.localKinds = [kind]
  numeric : kind ≠ .reference
  notSpan : ∀ width writable, kind ≠ .span width writable
  notArray : ∀ element, kind ≠ .array element
  fits : InitializerFits kind initial
  opaqueVectorLocals : body.opaqueVectorLocals = []
  vectorArgs : body.vectorArgs = []
  parameterHomes : body.parameterHomes = []
  returnsValue : body.returnsValue = calleeBody.returnsValue

/-- What a fresh numeric home created from `initial` holds: nothing known when `initial` is
    `.unmodeled`, and otherwise the bytes of `initial`'s number at the home's width. -/
def LocalHolds (kind : CIL.LocalKind) (initial : CIL.Value) (memory : Memory)
    (home : Reference) : Prop :=
  initial = .unmodeled ∨ ∃ number, localNumber kind initial = .ok number ∧
    read memory home (localWidth kind) 1 = .ok (numberBytes number (localWidth kind))

/-- A local of a kind that is neither a reference, span nor array, with a fitting initializer,
    is one fresh writable byte home holding that initializer. -/
theorem make_fitting_local (memory : Memory) (activation : Nat) (kind : CIL.LocalKind)
    (initial : CIL.Value) (wellFormed : memory.WellFormed) (numeric : kind ≠ .reference)
    (notSpan : ∀ width writable, kind ≠ .span width writable)
    (notArray : ∀ element, kind ≠ .array element)
    (fits : InitializerFits kind initial) :
    ∃ reference result,
      makeLocal activation kind initial memory =
        .ok (.bytes kind reference, [reference.allocation], result) ∧
      access result reference (localWidth kind) 1 true = .ok () ∧
      LocalHolds kind initial result reference := by
  by_cases unknown : initial = .unmodeled
  · subst unknown
    obtain ⟨reference, result, made, writable⟩ :=
      make_unknown_local memory activation kind wellFormed numeric notSpan notArray
    exact ⟨reference, result, made, writable, Or.inl rfl⟩
  · obtain ⟨number, encoded⟩ := initializer_numeric_number fits numeric notSpan notArray unknown
    obtain ⟨reference, result, made, readback, writable, -⟩ :=
      make_numeric_local memory activation kind initial number wellFormed encoded
    exact ⟨reference, result, made, writable, Or.inr ⟨number, encoded, readback⟩⟩

#print axioms make_fitting_local

/-- Entering a `ForwardsOut` body creates its local as one fresh writable home holding its
    initializer, keeps the caller's memory below `nextIdentity` and stays well formed. -/
theorem ForwardsOut.enterFrame {body calleeBody : CIL.Method}
    {loads : List (Nat × Option CIL.NarrowKind)} {callee : Nat} {narrow : Option CIL.NarrowKind}
    {kind : CIL.LocalKind} {initial : CIL.Value}
    (forwards : ForwardsOut body calleeBody loads callee narrow kind initial)
    (args : List Value) (memory : Memory) (wellFormed : memory.WellFormed) :
    ∃ home result,
      CIL.Safety.enterFrame body args memory =
        .ok (⟨memory.nextIdentity, [.bytes kind home], [home.allocation], [], 0⟩, result) ∧
      memory.nextIdentity ≤ home.allocation ∧
      access result home (localWidth kind) 1 true = .ok () ∧
      LocalHolds kind initial result home ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed := by
  obtain ⟨home, result, made, writable, holds⟩ :=
    make_fitting_local memory memory.nextIdentity kind initial wellFormed forwards.numeric
      forwards.notSpan forwards.notArray forwards.fits
  have fresh := (makeLocal_fresh _ _ _ _ _ _ _ made).2 home.allocation (by simp)
  refine ⟨home, result, ?_, fresh.1, writable, holds,
    makeLocal_preserves_caller_memory _ _ _ _ _ _ _ made,
    makeLocal_preserves_wellFormed _ _ _ _ _ _ _ wellFormed made⟩
  simp only [CIL.Safety.enterFrame, forwards.opaqueVectorLocals, makeSelectedLocals,
    List.isEmpty_nil, ite_true, forwards.localKinds, forwards.locals, makeLocals, made,
    forwards.vectorArgs, makeArgumentHomes, forwards.parameterHomes, makeParameterHomes,
    List.map_nil, Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil]

#print axioms ForwardsOut.enterFrame

/-- A forwarder that passes a fresh local as a last out argument and drops it meets `outer`
    when its callee meets `inner` at `extend input home`, `home` being that local. Each
    argument must be valid under `outer.pre` (`checked`), since the forwarder checks them
    all. The callee's arguments must be the forwarder's selected by `loads`, each kept by its
    load's narrowing, and then `home`; its precondition must follow from `outer.pre` in the
    memory after frame entry, where `home` is fresh, writable over the local's width and
    holds its initializer; its footprint may name fresh storage or lie inside
    `outer.footprint`; its postcondition must give `outer.post` once the frame has expired;
    and its results must be scalars, which survive the expiry of `home`. The home's
    alignment is not surfaced. -/
theorem MethodContract.Holds.forward_out {Outer Inner Output : Type}
    {outer : MethodContract Outer Output} {inner : MethodContract Inner Output}
    {program : CIL.Program} {method callee : Nat} {body calleeBody : CIL.Method}
    {loads : List (Nat × Option CIL.NarrowKind)} {narrow : Option CIL.NarrowKind}
    {kind : CIL.LocalKind} {initial : CIL.Value}
    (extend : Outer → Reference → Inner)
    (holds : inner.Holds program callee)
    (found : program[method]? = some body) (calleeFound : program[callee]? = some calleeBody)
    (forwards : ForwardsOut body calleeBody loads callee narrow kind initial)
    (selected : ∀ input home,
      loads.map (fun load => (outer.args input)[load.1]?) ++
          [some (.reference (.address home))] =
        (inner.args (extend input home)).map some)
    (checked : ∀ input memory, outer.pre input memory →
      memory.WellFormed ∧ ValuesValid memory (outer.args input))
    (narrowed : ∀ input memory home, outer.pre input memory →
      ∀ pair ∈ loads.zip (inner.args (extend input home)), LoadsUnchanged pair.1.2 pair.2)
    (known : ∀ input memory home, outer.pre input memory →
      (inner.args (extend input home)).any Value.hasUnspecified = false)
    (unchanged : ∀ input memory home entered final out, outer.pre input memory →
      inner.post (extend input home) entered final out →
      ReturnsUnchanged narrow (inner.results out))
    (results : ∀ out, outer.results out = inner.results out)
    (scalars : ∀ input memory home entered final out, outer.pre input memory →
      inner.post (extend input home) entered final out →
      ∀ value ∈ inner.results out, ∃ scalar, value = .scalar scalar)
    (prepared : ∀ input memory entered home, outer.pre input memory →
      MemoryBelow memory.nextIdentity memory entered → entered.WellFormed →
      memory.nextIdentity ≤ home.allocation →
      access entered home (localWidth kind) 1 true = .ok () →
      LocalHolds kind initial entered home →
      inner.pre (extend input home) entered)
    (footprint : ∀ input memory home, outer.pre input memory →
      memory.nextIdentity ≤ home.allocation →
      ∀ entry ∈ inner.footprint (extend input home),
        memory.nextIdentity ≤ entry.1.allocation ∨
          ∃ outerEntry ∈ outer.footprint input, Within entry outerEntry)
    (returned : ∀ input memory entered final left home out, outer.pre input memory →
      MemoryBelow memory.nextIdentity memory entered →
      MemoryBelow memory.nextIdentity final left → memory.nextIdentity ≤ home.allocation →
      Confined (inner.footprint (extend input home)) entered final →
      Confined (outer.footprint input) memory left →
      inner.post (extend input home) entered final out → outer.post input memory left out) :
    outer.Holds program method := by
  intro input memory permitted
  obtain ⟨formed, outerValid⟩ := checked input memory permitted
  obtain ⟨home, entered, setup, fresh, writable, initialized, entryBelow, enteredFormed⟩ :=
    forwards.enterFrame (outer.args input) memory formed
  have owned := enterFrame_fresh _ _ _ _ _ setup
  have calleePre := prepared input memory entered home permitted entryBelow enteredFormed fresh
    writable initialized
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
  have length : (inner.args (extend input home)).length = loads.length + 1 := by
    rw [split]; simpa using (congrArg List.length loadedSome)
  have fetched : ∀ pc : Nat,
      body.code[pc]? = (outForwarderCode loads callee narrow)[pc]? := by
    rw [forwards.code]; exact fun _ => rfl
  have loadedNarrowed : ∀ pair ∈ loads.zip loaded, LoadsUnchanged pair.1.2 pair.2 := by
    intro pair member
    refine narrowed input memory home permitted pair ?_
    have same : loads.length = loaded.length := by
      have lengths := congrArg List.length loadedSome
      simp only [List.length_map] at lengths
      omega
    rw [split, ← List.append_nil loads, List.zip_append same]
    exact List.mem_append_left _ member
  have enteredValid := outerValid.preserve formed owned.1
  refine invoke_exists_of_run found (checkedValues_of_valid outerValid) setup ?_
  refine run_load_arguments found enteredValid loads 0 [] loaded
    (fun position load located => ?_) loadedSome.symm loadedNarrowed ?_
  · have bound : position < loads.length := (List.getElem?_eq_some_iff.mp located).1
    rw [Nat.zero_add, fetched, outForwarderCode,
      List.getElem?_append_left (by simpa using bound), List.getElem?_map, located]
    rfl
  rw [Nat.zero_add, List.append_nil]
  let frame : Frame := ⟨memory.nextIdentity, [.bytes kind home], [home.allocation], [], 0⟩
  have addressed : step body (.localAddr 0) loads.length (outer.args input) frame
      loaded.reverse entered =
        .ok (.next (loads.length + 1) (.reference (.address home) :: loaded.reverse) frame
          entered) := by
    have formedHome := access_reference_valid _ _ _ _ _ writable
    simp only [step, observerCount, unspecifiedOperands, List.take_zero, List.any_nil,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte, frame, List.getElem?_cons_zero,
      localAddress, formValue, checkedAt, formedHome, Except.mapError, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  refine run_next_exists _ found (by simp [fetched, outForwarderCode]) addressed ?_
  have stack : .reference (.address home) :: loaded.reverse =
      (inner.args (extend input home)).reverse := by
    rw [split]; simp
  rw [stack]
  have exitFresh : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id :=
    fun id member => (owned.2 id member).1
  refine run_forward_call holds found calleeFound
    (by rw [length]; simp [fetched, outForwarderCode])
    (by
      rw [fetched, outForwarderCode, List.getElem?_append_right (by simp; omega)]
      simp [show loads.length + 1 + 1 - loads.length = 2 by omega])
    forwards.returnsValue
    (fun final out satisfied =>
      unchanged input memory home entered final out permitted satisfied)
    calleePre (known input memory home permitted) (fun final values valid returns => ?_)
    (fun final values framed returns => ?_)
  · obtain ⟨out, encoded, satisfied⟩ := returns
    intro value member
    obtain ⟨scalar, same⟩ :=
      scalars input memory home entered final out permitted satisfied value (encoded ▸ member)
    subst same
    exact valid _ member
  · have exitBelow := leaveFrame_preserves_memory_below frame final _ exitFresh
    have confined := Confined.across_frame entryBelow owned.1.next framed exitBelow
      (Nat.le_of_eq (leaveFrame_nextIdentity frame final).symm)
      (footprint input memory home permitted fresh)
    obtain ⟨out, encoded, satisfied⟩ := returns
    exact ⟨confined, out, encoded.trans (results out).symm,
      returned input memory entered final _ home out permitted entryBelow exitBelow fresh
        framed confined satisfied⟩

#print axioms MethodContract.Holds.forward_out

end CIL.Safety
