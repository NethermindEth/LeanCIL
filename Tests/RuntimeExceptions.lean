import CIL.ExceptionType
import CIL.Extraction.Folds
import CIL.Safety.RuntimeExceptions

namespace Tests.RuntimeExceptions

open CIL.Safety

inductive Case where
  | add | sub | mul | convert | divide | remainder | signedDivide | signedRemainder
  deriving DecidableEq

def operation : Case → CIL.Instruction
  | .add => .add_ovf
  | .sub => .sub_ovf
  | .mul => .mul_ovf
  | .convert => .conv_ovf .u1
  | .divide => .div_un
  | .remainder => .rem_un
  | .signedDivide => .div
  | .signedRemainder => .rem

def arguments : Case → List CIL.Safety.Value
  | .add => [.scalar (.i32 2147483647), .scalar (.i32 1)]
  | .sub => [.scalar (.i32 2147483648), .scalar (.i32 1)]
  | .mul => [.scalar (.i32 2147483647), .scalar (.i32 2)]
  | .convert => [.scalar (.i32 256)]
  | .divide | .remainder => [.scalar (.i32 7), .scalar (.i32 0)]
  | .signedDivide | .signedRemainder => [.scalar (.i32 2147483648), .scalar (.i32 4294967295)]

def method (which : Case) : CIL.Method := {
  code := (match which with | .convert => [.ldarg 0] | _ => [.ldarg 0, .ldarg 1]) ++
    [operation which, .ret]
  locals := [], returnsValue := true }

def instruction : Case → Nat
  | .convert => 1
  | _ => 2

def arithmeticFault : Case → CIL.ArithmeticFault
  | .divide | .remainder => .divideByZero
  | _ => .overflow

def exceptionName : Case → CIL.ExceptionType
  | .divide | .remainder => .divideByZero
  | _ => .overflow

def wrongName : Case → CIL.ExceptionType
  | .divide | .remainder => .overflow
  | _ => .divideByZero

def contract (which : Case) (exception : CIL.ExceptionType) : OutcomeContract Unit where
  args _ := arguments which
  pre _ _ := True
  footprint _ := []
  post _ _ _ _ := False
  raises _ _ := some exception

def empty : Memory := {
  allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }

theorem invoked (which : Case) (memory : Memory) :
    invoke [method which] 4 0 (arguments which) memory =
      .error ⟨0, instruction which, .arithmetic (arithmeticFault which)⟩ := by
  cases which <;> rfl

theorem named_outcomes (which : Case) : (contract which (exceptionName which)).HoldsCLR [method which] 0 := by
  intro _ memory _
  exact ⟨4, ⟨0, instruction which, .arithmetic (arithmeticFault which)⟩,
    invoked which memory, by cases which <;> rfl⟩

theorem wrong_outcomes (which : Case) : ¬ (contract which (wrongName which)).HoldsCLR [method which] 0 := by
  intro holds
  have raised := holds.raising (input := ()) (initial := empty) trivial rfl
  exact RaisesCLR.not_of_invoke (by simp [Settled]) (invoked which empty)
    (by cases which <;> decide) raised

def zeroDivisorMethod (remainder : Bool) : CIL.Method := {
  code := [.ldarg 0, .ldarg 1, if remainder then .rem_un else .div_un, .ret], locals := [],
  returnsValue := true }

def zeroDivisorContract : OutcomeContract CIL.W32 where
  args value := [.scalar (.i32 value), .scalar (.i32 0)]
  pre _ _ := True
  footprint _ := []
  post _ _ _ _ := False
  raises _ _ := some .divideByZero

theorem divide_and_mod_zero (remainder : Bool) : zeroDivisorContract.HoldsCLR [zeroDivisorMethod remainder] 0 := by
  intro value memory _
  cases remainder <;> exact ⟨4, ⟨0, 2, .arithmetic .divideByZero⟩, rfl, rfl⟩

theorem unnamed_faults (exception : CIL.ExceptionType) :
    ExecutionFault.clrException (.arithmetic .invalidOperands) ≠ some exception ∧
    ExecutionFault.clrException (.arithmetic .invalidBounds) ≠ some exception ∧
    ExecutionFault.clrException .invalidState ≠ some exception ∧
    ExecutionFault.clrException (.unsupported "operation") ≠ some exception ∧
    ExecutionFault.clrException .fuelExhausted ≠ some exception := by
  simp [ExecutionFault.clrException]

theorem memory_faults_never_named (rule : Fault) (reference : ManagedReference) (width : Nat)
    (exception : CIL.ExceptionType) :
    ExecutionFault.clrException (.memory rule reference width) ≠ some exception := by
  simp [ExecutionFault.clrException]

theorem unsupported_never_named (exception : CIL.ExceptionType) :
    ¬ RaisesCLR [{ code := [.unadmitted 0], locals := [], returnsValue := false }] 0 [] empty
      exception := by
  apply RaisesCLR.not_of_invoke (fuel := 1)
    (fault := ⟨0, 0, .unsupported "Opcode not admitted"⟩)
  · simp [Settled]
  · rfl
  · simp [ExecutionFault.clrException]

theorem invalid_state_never_named (exception : CIL.ExceptionType) :
    ¬ RaisesCLR [] 0 [] empty exception := by
  apply RaisesCLR.not_of_invoke (fuel := 1) (fault := ⟨0, 0, .invalidState⟩)
  · simp [Settled]
  · rfl
  · simp [ExecutionFault.clrException]

theorem thrown_still_named (exception : CIL.ExceptionType) :
    RaisesCLR [{ code := [.throw exception], locals := [], returnsValue := false }] 0 [] empty exception :=
  RaisesCLR.of_raises ⟨1, ⟨0, 0, .thrown exception⟩, rfl, rfl⟩

#print axioms named_outcomes
#print axioms wrong_outcomes
#print axioms divide_and_mod_zero
#print axioms unsupported_never_named
#print axioms invalid_state_never_named

-- A throw raises its member, and a checked overflow surfaces as the overflow member.
example : Raises [{ code := [.throw .overflow], locals := [], returnsValue := false }] 0 []
    empty .overflow :=
  ⟨1, ⟨0, 0, .thrown .overflow⟩, rfl, rfl⟩

example : (ExecutionFault.arithmetic .overflow).clrException = some .overflow := rfl

-- Goals show the fault with its member by name.
/--
trace: ⊢ ExecutionFault.thrown CIL.ExceptionType.overflow ≠
  ExecutionFault.thrown CIL.ExceptionType.format
-/
#guard_msgs (whitespace := lax) in
example : ExecutionFault.thrown .overflow ≠ ExecutionFault.thrown .format := by
  trace_state
  decide

/--
info: 'CIL.Extraction.exceptionOwner?_eq_some' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms CIL.Extraction.exceptionOwner?_eq_some

-- The runtime assembly displays as the scope text extraction compares.
#guard CIL.Extraction.runtimeAssembly.display == CIL.Extraction.runtimeScope

-- Each member's owner name is its namespace and name as a reader writes them.
#guard CIL.ExceptionType.all.all fun raised =>
  raised.ownerName ==
    raised.typeIdentity.typeNamespace.display ++ "." ++ raised.typeIdentity.name.display

example : CIL.ExceptionType.all.Nodup := by decide

/-- info: 'CIL.ExceptionType.typeIdentity_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms CIL.ExceptionType.typeIdentity_injective

/-- info: 'CIL.ExceptionType.ofTypeIdentity?_typeIdentity' does not depend on any axioms -/
#guard_msgs in
#print axioms CIL.ExceptionType.ofTypeIdentity?_typeIdentity

/-- info: 'CIL.ExceptionType.ownerName_spells' does not depend on any axioms -/
#guard_msgs in
#print axioms CIL.ExceptionType.ownerName_spells

/--
info: 'CIL.Extraction.runtimeScope_spells_runtimeAssembly' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms CIL.Extraction.runtimeScope_spells_runtimeAssembly

end Tests.RuntimeExceptions
