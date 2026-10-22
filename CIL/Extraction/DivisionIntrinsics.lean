import CIL.Extraction.Features

namespace CIL.Extraction

private def intrinsicScope := "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"

private def divisionSignatures : List (String × String × String × Intrinsic × Nat) := [
  ("System.Runtime.Intrinsics.X86.Avx2", "And", "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::And(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)", .avx2 .band, 2),
  ("System.Runtime.Intrinsics.X86.Avx2", "Or", "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::Or(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)", .avx2 .bor, 2),
  ("System.Runtime.Intrinsics.X86.Avx2", "Xor", "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::Xor(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)", .avx2 .bxor, 2),
  ("System.Runtime.Intrinsics.X86.Avx2", "AndNot", "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::AndNot(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)", .avx2 .andNot, 2),
  ("System.Runtime.Intrinsics.X86.Avx2", "ShiftLeftLogical", "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::ShiftLeftLogical(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector128`1<System.UInt64>)", .avx2 .shl64Count, 2),
  ("System.Runtime.Intrinsics.X86.Avx2", "ShiftRightLogical", "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::ShiftRightLogical(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector128`1<System.UInt64>)", .avx2 .shr64Count, 2),
  ("System.Runtime.Intrinsics.X86.Avx512F", "CompareLessThan", "System.Runtime.Intrinsics.Vector512`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx512F::CompareLessThan(System.Runtime.Intrinsics.Vector512`1<System.UInt64>,System.Runtime.Intrinsics.Vector512`1<System.UInt64>)", .avx512 .ltu512, 2),
  ("System.Runtime.Intrinsics.X86.Avx512F", "CompareGreaterThan", "System.Runtime.Intrinsics.Vector512`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx512F::CompareGreaterThan(System.Runtime.Intrinsics.Vector512`1<System.UInt64>,System.Runtime.Intrinsics.Vector512`1<System.UInt64>)", .avx512 .gtu512, 2),
  ("System.Runtime.Intrinsics.X86.Avx512DQ", "MoveMask", "System.Int32 System.Runtime.Intrinsics.X86.Avx512DQ::MoveMask(System.Runtime.Intrinsics.Vector512`1<System.UInt64>)", .avx512DQ .moveMask512, 1),
  ("System.Runtime.Intrinsics.Vector512", "Create", "System.Runtime.Intrinsics.Vector512`1<System.UInt64> System.Runtime.Intrinsics.Vector512::Create(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)", .vector .combine256, 2),
  ("System.Runtime.Intrinsics.Vector128", "CreateScalarUnsafe", "System.Runtime.Intrinsics.Vector128`1<System.UInt64> System.Runtime.Intrinsics.Vector128::CreateScalarUnsafe(System.UInt64)", .vector .createScalarUnsafe64, 1),
  ("System.Runtime.Intrinsics.X86.Avx2", "ShiftLeftLogical", "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::ShiftLeftLogical(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)", .avx2 .shl64, 2),
  ("System.Runtime.Intrinsics.X86.Avx2", "ShiftRightLogical", "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::ShiftRightLogical(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)", .avx2 .shr64, 2),
  ("System.Runtime.Intrinsics.X86.Avx512DQ", "MoveMask", "System.Int32 System.Runtime.Intrinsics.X86.Avx512DQ::MoveMask(System.Runtime.Intrinsics.Vector256`1<System.UInt64>)", .avx512DQ .moveMask64, 1)]

def divisionIntrinsic (instruction : RawInstruction) : Option (Intrinsic × Nat) := do
  if instruction.opcode != 40 then none else
  let .call site := instruction.operand | none
  if site.hasThis || !site.returnsValue || !site.typeArguments.isEmpty then none else
  let (owner, name, signature, intrinsic, arity) ← divisionSignatures.find? fun (owner, name, signature, _, arity) =>
    site.declaringType == .atom intrinsicScope owner && site.name == name &&
    site.parameterCount == arity && site.target == .external (intrinsicScope ++ "::" ++ signature)
  let _ := owner
  let _ := name
  let _ := signature
  return (intrinsic, arity)

private def divisionCallFamily (instruction : RawInstruction) : Bool :=
  match instruction.operand with
  | .call site => divisionSignatures.any fun (owner, name, signature, _, _) =>
      site.target == .external (intrinsicScope ++ "::" ++ signature) ||
      site.name == name && match site.declaringType with
        | .atom _ declared => declared == owner
        | _ => false
  | _ => false

def emittedDivisionIntrinsic : Op → Option (Intrinsic × Nat)
  | .intrinsic intrinsic arity => match intrinsic with
    | .avx2 .band | .avx2 .bor | .avx2 .bxor | .avx2 .andNot
    | .avx2 .shl64Count | .avx2 .shr64Count | .avx2 .shl64 | .avx2 .shr64
    | .avx512 .ltu512 | .avx512 .gtu512
    | .avx512DQ .moveMask512 | .avx512DQ .moveMask64 | .vector .combine256 | .vector .createScalarUnsafe64 => some (intrinsic, arity)
    | _ => none
  | _ => none

def DivisionIntrinsicsValid (closed : RawMethod) (reachable : List Bool) (method : Method) : Prop :=
  method.profile.Valid ∧ closed.code.length = reachable.length ∧ closed.code.length = method.code.length ∧
  all3 (fun raw live emitted => !live ||
    (if divisionCallFamily raw || (emittedDivisionIntrinsic emitted).isSome then
      (divisionIntrinsic raw).isSome && decide (divisionIntrinsic raw = emittedDivisionIntrinsic emitted)
     else true) &&
    match emittedDivisionIntrinsic emitted with
    | some (intrinsic, _) => Intrinsic.available method.profile intrinsic
    | none => true) closed.code reachable method.code = true

instance (closed : RawMethod) (reachable : List Bool) (method : Method) :
    Decidable (DivisionIntrinsicsValid closed reachable method) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

private def opaqueEligible (closed : RawMethod) (index : Nat) : Bool :=
  (match closed.locals[index]? with
  | some (.apply (.constructor scope "System.Runtime.Intrinsics.Vector128`1") (.atom scalarScope "System.UInt64")) =>
    scope == intrinsicScope && scalarScope == "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
  | _ => false) && !(closed.code.any fun instruction =>
    (instruction.opcode == 18 || instruction.opcode == 65037) && localIndex instruction == some index)

def opaqueLocalIndices (closed : RawMethod) : List Nat :=
  (List.range closed.locals.length).filter (opaqueEligible closed)

def OpaqueLocalsValid (closed : RawMethod) (method : Method) : Prop :=
  method.opaqueVectorLocals = opaqueLocalIndices closed ∧
  method.opaqueVectorLocals.all (fun index => method.localKinds[index]? == some .vector128) = true ∧
  method.code.all (fun operation => match operation with
    | .localAddr index => !(index ∈ method.opaqueVectorLocals)
    | _ => true) = true

instance (closed : RawMethod) (method : Method) : Decidable (OpaqueLocalsValid closed method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end CIL.Extraction
