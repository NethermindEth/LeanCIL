import CIL.Extraction.ModelTable

/-!
# The `System.Object` constructor

An admitted class derives directly from `System.Object`, so its constructor calls
`System.Object::.ctor()` on its receiver. That constructor has no effect on an instance, and its
runtime model consumes the receiver. The model entry stands for exactly that method reference
under `call`, so a constructor of another owner, scope or signature has no model. The call keeps
its call, and `callEmitsNoPop`, which `CIL/Extraction/UnsafeCalls.lean` requires, refuses `pop`
at every call site.
-/

namespace CIL.Extraction

/-- `instance void [System.Runtime]System.Object::.ctor()`. -/
def objectConstructorMethod : MethodRef :=
  { owner := .atom runtimeScope "System.Object", name := name!".ctor", hasThis := true,
    genericArity := 0, returnType := .void, parameters := [] }

/-- A `call` of the `System.Object` constructor only consumes its receiver. -/
def objectConstructorEntry : ModelEntry :=
  .exact .call objectConstructorMethod .objectConstructor

/-- The raw opcodes of `call`, `calli`, `callvirt` and `newobj`. -/
def callFamilyOpcodes : List Nat := [40, 41, 111, 115]

/-- No call site emits `pop`: the `System.Object` constructor call keeps its call and runs its
    model, and `pop` in place of any other call would drop that call's effects. -/
def callEmitsNoPop (instruction : RawInstruction) (emitted : Instruction) : Bool :=
  !(emitted matches .pop) || !callFamilyOpcodes.contains instruction.opcode

end CIL.Extraction
