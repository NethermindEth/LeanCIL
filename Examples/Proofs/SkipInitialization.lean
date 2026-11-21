import Extracted
import CIL.Safety.SymbolicExecution
import CIL.Safety.StepComposition

/-! Skipping initialization consumes a checked reference without initializing its storage. -/

namespace ExampleProof

/-- Caller memory with one readable and writable 8-byte allocation, identity 0. -/
def callerMemory : CIL.Safety.Memory where
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 8, true, true⟩]
  nextIdentity := 1

/-- A reference to the start of `callerMemory`'s allocation. -/
def callerReference : CIL.Safety.Value := .reference (.address ⟨0, 0⟩)

open CIL.Safety

def uninitialized : Memory := { callerMemory with
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨32, 1, []⟩, true, [32]⟩ else none
  cells := fun _ _ => ⟨37, false⟩
  views := [⟨0, 0, 32, true, true⟩] }

-- The compiled call consumes its reference without changing any caller byte,
-- including initialization flags. It does not initialize an out parameter.
theorem correctness :
    invoke Extracted.program 4 0 [callerReference] uninitialized = .ok (uninitialized, []) := by
  rfl

/-- A `SkipInit` call the runtime table models preserves every byte and initialization flag of
    caller memory. -/
theorem step_preserves (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame)
    (memory : Memory) {method : CIL.Extraction.MethodRef} {prefixes : CIL.CallPrefixes}
    (link : body.linkAt pc = none)
    (found : CIL.Extraction.runtimeModel body.environment .call method = some .skipInit)
    (direct : prefixes.tail = false) (reference : ManagedReference) (stack : List Value)
    (valid : ∃ value, formValue memory reference = .ok value) :
    step body (.call method prefixes) pc args frame (.reference reference :: stack) memory =
      .ok (.next (pc + 1) stack frame memory) := by
  obtain ⟨value, valid⟩ := valid
  rw [step_call_skipInit_reference (link := link) (found := found) (direct := direct), valid]
  rfl

#print axioms correctness
#print axioms step_preserves

/-- Both environments assign the call to the SkipInit family before checking its layout. -/
theorem skip_family :
    let raw := Extracted.method0Closed.code[1]'(by decide)
    CIL.Extraction.siteClaim Extracted.environment none raw =
      .model ∧
    CIL.Extraction.siteClaim {} none raw =
      .model := by
  decide +kernel

#print axioms skip_family

open CIL in
cil_decoded_method skipWithLayout := Method.ofRaw? Extracted.profile Extracted.environment
  Extracted.method0Links Extracted.method0Reachable Extracted.method0Original
  Extracted.method0TypeArgumentsRaw

/-- The same decoding environment with no aggregate layouts. -/
private def emptyLayouts : CIL.LayoutEnvironment := {}

/-- The decoder retains the call with the method reference from the raw operand. -/
theorem resolved_skip :
    let raw := Extracted.method0Closed.code[1]'(by decide)
    match raw.operand with
    | .call site => skipWithLayout.code[1]? = some (.call site.method {})
    | _ => False := by rfl

#print axioms resolved_skip

/-- The extracted instruction pops the caller's reference and preserves its uninitialized bytes. -/
theorem compiled_step (args : List Value) (frame : Frame) (stack : List Value) :
    step Extracted.method0 (Extracted.method0.code[1]'(by decide)) 1 args frame
      (callerReference :: stack) uninitialized = .ok (.next 2 stack frame uninitialized) :=
  step_preserves Extracted.method0 1 args frame uninitialized (prefixes := {})
    rfl Extracted.method0_model1 rfl (.address ⟨0, 0⟩) stack ⟨_, rfl⟩

#print axioms compiled_step

/-- Without the value type's layout the call has no model, so the decoder refuses the method. -/
theorem unresolved_skip :
    (CIL.Method.ofRaw? Extracted.profile emptyLayouts Extracted.method0Links
      Extracted.method0Reachable Extracted.method0Original
      Extracted.method0TypeArgumentsRaw).isNone = true := by
  decide +kernel

#print axioms unresolved_skip

end ExampleProof
