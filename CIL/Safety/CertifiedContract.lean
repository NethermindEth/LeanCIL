import CIL.Safety.MethodContract

/-!
# Certified method contracts

`MethodContract.Certified` strengthens `MethodContract.Holds` with the
`InvocationCertificate` of the returning invocation, so a consumer keeps the visited-state
and returned-state invariants alongside the contract. `Holds.certified` derives it from a
proved contract whose precondition implies well-formed memory and a valid static world.
`Certified.holds` recovers the ordinary `Holds`, and `Certified.weaken` derives a certified
contract from a certified one it refines. At a call site, `run_call_of_certified` and
`run_call_of_contract_certified` hand the continuation the callee's certificate, which
`run_call_of_contract` drops.
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

/-- Derive a certified contract from a certified one it refines, keeping the certificate;
    the method is neither unfolded nor executed. -/
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
    callee's `InvocationCertificate` with the footprint and the typed output. -/
theorem run_call_of_certified {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (certified : c.Certified program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (continuation : ∀ fuel final values,
      InvocationCertificate program callee arguments updated fuel final values →
      Confined (c.footprint input) updated final → c.Returns input updated final values →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame (values ++ rest) final =
          .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧
        post result returned := by
  subst encoded
  obtain ⟨childFuel, final, values, certificate, framed, satisfied⟩ :=
    certified input updated permitted
  obtain ⟨parentFuel, result, returned, resumed, finished⟩ :=
    continuation childFuel final values certificate framed satisfied
  obtain ⟨fuel, composed⟩ := run_call_exists methodFound instructionFound stepped
    ⟨childFuel, certificate.1⟩ ⟨parentFuel, resumed⟩
  exact ⟨fuel, result, returned, composed, finished⟩

/-- Compose a fetched call through a proved contract from a well-formed caller memory in a
    valid static world: the continuation receives the callee's `InvocationCertificate`,
    whose returned state carries the final memory's well-formedness and static world. -/
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
    (continuation : ∀ fuel final values,
      InvocationCertificate program callee arguments updated fuel final values →
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
    fun final values ⟨fuel, invoked⟩ =>
      continuation fuel final values (.of_invoke entered enteredWorld invoked)

#print axioms MethodContract.Certified.holds
#print axioms MethodContract.Holds.certified
#print axioms MethodContract.Certified.weaken
#print axioms run_call_of_certified
#print axioms run_call_of_contract_certified

end CIL.Safety
