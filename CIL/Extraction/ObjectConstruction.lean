import CIL.Extraction.Generics

/-!
# The `System.Object` constructor call

An admitted class derives directly from `System.Object`, so its constructor calls
`System.Object::.ctor()` on its receiver. That constructor has no effect on an instance, and the
extractor translates the call to `pop`. `objectConstructorCall` recognizes the exact call from raw
metadata alone: `CIL/Extraction/Scalars.lean` types its receiver as an object reference, and
`CIL/Extraction/UnsafeCalls.lean` requires it, and only it among calls, to emit `pop`.
-/

namespace CIL.Extraction

/-- Exactly `call instance void [System.Runtime]System.Object::.ctor()`. -/
def objectConstructorCall (instruction : RawInstruction) : Bool :=
  match instruction.opcode, instruction.operand with
  | 40, .call site =>
    site.name == ".ctor" && site.hasThis && !site.returnsValue && site.returnType == .void &&
      site.parameterCount == 0 && site.parameterTypes.isEmpty && site.typeArguments.isEmpty &&
      site.declaringType == .atom runtimeScope "System.Object" &&
      site.target == .external (runtimeScope ++ "::System.Void System.Object::.ctor()")
  | _, _ => false

/-- The `System.Object` constructor call emits `pop`, and no other `call` does. -/
def objectConstructorMatches (instruction : RawInstruction) (emitted : Op) : Bool :=
  match emitted with
  | .pop => instruction.opcode != 40 || objectConstructorCall instruction
  | _ => !objectConstructorCall instruction

end CIL.Extraction
