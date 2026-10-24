import CIL.Safety.MethodContract

/-!
# Certified method contracts

`MethodContract.Certified` strengthens `MethodContract.Holds` with the
`InvocationCertificate` of the returning invocation, so a consumer keeps the visited-state
and returned-state invariants alongside the contract. `Holds.certified` derives it from a
proved contract whose precondition implies well-formed memory and a valid static world.
`Certified.holds` recovers the ordinary `Holds`, and `Certified.weaken` derives a certified
exported contract from a certified internal contract that refines it. At a call site,
`run_call_of_certified` and `run_call_of_contract_certified` hand the continuation the
callee's certificate, which `run_call_of_contract` drops; `cil_certified_call` and
`cil_contract_certified_call` apply them at a fetched call.
-/

namespace CIL.Safety

/-- Every invocation meeting `pre` returns normally within the footprint, satisfies `post`,
    and is certified by an `InvocationCertificate` for the same fuel and result. -/
def MethodContract.Certified {Input Output : Type} (c : MethodContract Input Output)
    (program : CIL.Program) (method : Nat) : Prop :=
  ∀ input initial, c.pre input initial →
    ∃ fuel final values,
      InvocationCertificate program method (c.args input) initial fuel final values ∧
      Confined (c.footprint input) initial final ∧ c.Returns input initial final values

/-- A certified contract holds; the certificate's first clause is the invocation. -/
theorem MethodContract.Certified.holds {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method : Nat} (certified : c.Certified program method) :
    c.Holds program method := by
  intro input initial permitted
  obtain ⟨fuel, final, values, certificate, framed, returns⟩ :=
    certified input initial permitted
  exact ⟨fuel, final, values, certificate.1, framed, returns⟩

/-- A proved contract is certified when its precondition implies well-formed memory and a
    valid static world, the premises checked frame entry needs. -/
theorem MethodContract.Holds.certified {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method : Nat} (holds : c.Holds program method)
    (entry : ∀ input initial, c.pre input initial →
      initial.WellFormed ∧ StaticWorldValid (programStaticDescriptors program) initial) :
    c.Certified program method := by
  intro input initial permitted
  obtain ⟨fuel, final, values, invoked, framed, returns⟩ := holds input initial permitted
  obtain ⟨formed, world⟩ := entry input initial permitted
  exact ⟨fuel, final, values, .of_invoke formed world invoked, framed, returns⟩

/-- Derive a certified exported contract from a certified internal contract that refines it,
    keeping the certificate; the method is neither unfolded nor executed. -/
theorem MethodContract.Certified.weaken {Input Output : Type}
    {internal exported : MethodContract Input Output}
    {program : CIL.Program} {method : Nat} (certified : internal.Certified program method)
    (refines : internal.Refines exported) : exported.Certified program method := by
  intro input initial permitted
  obtain ⟨fuel, final, values, certificate, framed, out, encoded, satisfied⟩ :=
    certified input initial (refines.pre _ _ permitted)
  refine ⟨fuel, final, values, ?_, framed.widen_within (refines.footprint _ _ permitted),
    out, ?_, refines.post _ _ _ _ permitted framed satisfied⟩
  · rw [refines.args]; exact certificate
  · rw [refines.results]; exact encoded

/-- Compose a fetched call through a certified contract: the continuation receives the
    callee's `InvocationCertificate`, with its entered frame, live entry and visited states
    and returned state, besides the footprint and the typed output. -/
theorem run_call_of_certified {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (certified : c.Certified program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (continuation : ∀ calleeFuel final values,
      InvocationCertificate program callee arguments updated calleeFuel final values →
      Confined (c.footprint input) updated final → c.Returns input updated final values →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame (values ++ rest) final =
          .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧
        post result returned := by
  subst encoded
  obtain ⟨calleeFuel, final, values, certificate, framed, satisfied⟩ :=
    certified input updated permitted
  obtain ⟨parentFuel, result, returned, resumed, finished⟩ :=
    continuation calleeFuel final values certificate framed satisfied
  obtain ⟨fuel, composed⟩ := run_call_exists methodFound instructionFound stepped
    ⟨calleeFuel, certificate.1⟩ ⟨parentFuel, resumed⟩
  exact ⟨fuel, result, returned, composed, finished⟩

/-- Compose a fetched call through a proved contract from a well-formed caller memory in a
    valid static world, whatever the callee's precondition: the continuation receives the
    callee's `InvocationCertificate`, so beyond `run_call_of_contract_formed` it learns the
    callee's entered frame and that its entry and every visited state are live. -/
theorem run_call_of_contract_certified {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (formed : memory.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) memory)
    (continuation : ∀ calleeFuel final values,
      InvocationCertificate program callee arguments updated calleeFuel final values →
      Confined (c.footprint input) updated final → c.Returns input updated final values →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame (values ++ rest) final =
          .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧
        post result returned :=
  have called : ProgramStep program method pc args frame stack memory
      (.call callee arguments rest updated) :=
    ⟨body, op, methodFound, instructionFound, stepped⟩
  have entered : updated.WellFormed :=
    programStep_preserves_wellFormed _ _ _ _ _ _ _ _ formed called
  have enteredWorld : StaticWorldValid (programStaticDescriptors program) updated :=
    programStep_preserves_static_world called formed world
  run_call_of_contract holds input methodFound instructionFound stepped encoded permitted
    fun final values ⟨calleeFuel, invoked⟩ =>
      continuation calleeFuel final values (.of_invoke entered enteredWorld invoked)

#print axioms MethodContract.Certified.holds
#print axioms MethodContract.Holds.certified
#print axioms MethodContract.Certified.weaken
#print axioms run_call_of_certified
#print axioms run_call_of_contract_certified

/-- `cil_contract_call` through `run_call_of_certified`: leaves the precondition, then the
    continuation over the callee's certificate, footprint and output. -/
syntax "cil_certified_call" term:max term:max (" at " ident)? "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_certified_call $certified $input [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.run_call_of_certified $certified $input
      (by cil_lookup [$[$facts:term],*])
      (by cil_lookup [$[$facts:term],*])
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_))
  | `(tactic| cil_certified_call $certified $input at $site:ident [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.run_call_of_certified $certified $input
      (by cil_lookup [$[$facts:term],*]) $(Lean.mkIdent (site.getId ++ `call))
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_))

/-- `cil_contract_call` through `run_call_of_contract_certified`: leaves the precondition,
    the caller memory's `WellFormed` and static world, then the continuation over the
    callee's certificate, footprint and output. -/
syntax "cil_contract_certified_call" term:max term:max (" at " ident)? "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_contract_certified_call $holds $input [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.run_call_of_contract_certified $holds $input
      (by cil_lookup [$[$facts:term],*])
      (by cil_lookup [$[$facts:term],*])
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_ ?_ ?_))
  | `(tactic| cil_contract_certified_call $holds $input at $site:ident [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.run_call_of_contract_certified $holds $input
      (by cil_lookup [$[$facts:term],*]) $(Lean.mkIdent (site.getId ++ `call))
      (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_ ?_ ?_))

end CIL.Safety
