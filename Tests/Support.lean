import CIL.Safety.Execution

/-!
Caller memory and argument fixtures shared by the repository's tests. They are test inputs, not
part of the framework, and are not shipped with the tool.
-/

namespace Tests
open CIL.Safety

/-- Caller memory with one readable and writable 8-byte allocation, identity 0. -/
def caller : Memory where
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨8, 1, []⟩, true, [8]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 8, true, true⟩]
  nextIdentity := 1

/-- A reference to the start of `caller`'s allocation. -/
def reference : Value := .reference (.address ⟨0, 0⟩)

/-- The parameterless Boolean getter on a named ISA class in the pinned intrinsics assembly. -/
def supportedGetter (isa : String) : CIL.Extraction.MethodRef where
  owner := .atom CIL.Extraction.intrinsicsScope ("System.Runtime.Intrinsics." ++ isa) .classType
  name := name!"get_IsSupported"
  hasThis := false
  genericArity := 0
  returnType := .primitive .boolean
  parameters := []

/-- The checked getter table selects AVX2 in every layout environment. -/
theorem supportedGetter_avx2_model (environment : CIL.LayoutEnvironment) :
    CIL.Extraction.runtimeModel environment .call (supportedGetter "X86.Avx2") =
      some (.feature .avx2) := rfl

/-- A static method of `count` parameters, for a body that calls through its link table and
    needs only the call's arity; the owner, name and types are placeholders no check reads. -/
def callee (count : Nat) : CIL.Extraction.MethodRef where
  owner := .void
  name := ⟨1⟩
  hasThis := false
  genericArity := 0
  returnType := .void
  parameters := List.replicate count .void

/-- A placeholder method takes exactly its parameter count of arguments. -/
@[simp] theorem callee_argumentCount (count : Nat) : (callee count).argumentCount = count := by
  simp [callee, CIL.Extraction.MethodRef.argumentCount]

#print axioms callee_argumentCount

end Tests
