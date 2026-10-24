import CIL.Safety.RuntimeExceptions

namespace Tests.RuntimeExceptions

open CIL.Safety

inductive Case where
  | add | sub | mul | convert | divide | remainder | signedDivide | signedRemainder
  deriving DecidableEq

def operation : Case → CIL.Op
  | .add => .checkedArithmetic .add true
  | .sub => .checkedArithmetic .sub true
  | .mul => .checkedArithmetic .mul true
  | .convert => .checkedConvert 8 false false
  | .divide => .divide false false
  | .remainder => .divide false true
  | .signedDivide => .divide true false
  | .signedRemainder => .divide true true

def arguments : Case → List CIL.Safety.Value
  | .add => [.scalar (.i32 2147483647), .scalar (.i32 1)]
  | .sub => [.scalar (.i32 2147483648), .scalar (.i32 1)]
  | .mul => [.scalar (.i32 2147483647), .scalar (.i32 2)]
  | .convert => [.scalar (.i32 256)]
  | .divide | .remainder => [.scalar (.i32 7), .scalar (.i32 0)]
  | .signedDivide | .signedRemainder => [.scalar (.i32 2147483648), .scalar (.i32 4294967295)]

def method (which : Case) : CIL.Method := {
  code := (match which with | .convert => [.arg 0] | _ => [.arg 0, .arg 1]) ++ [operation which, .ret]
  locals := [], returnsValue := true }

def instruction : Case → Nat
  | .convert => 1
  | _ => 2

def arithmeticFault : Case → CIL.ArithmeticFault
  | .divide | .remainder => .divideByZero
  | _ => .overflow

def exceptionName : Case → String
  | .divide | .remainder => "System.DivideByZeroException"
  | _ => "System.OverflowException"

def wrongName : Case → String
  | .divide | .remainder => "System.OverflowException"
  | _ => "System.DivideByZeroException"

def contract (which : Case) (exception : String) : OutcomeContract Unit where
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
  code := [.arg 0, .arg 1, .divide false remainder, .ret], locals := [], returnsValue := true }

def zeroDivisorContract : OutcomeContract CIL.W32 where
  args value := [.scalar (.i32 value), .scalar (.i32 0)]
  pre _ _ := True
  footprint _ := []
  post _ _ _ _ := False
  raises _ _ := some "System.DivideByZeroException"

theorem divide_and_mod_zero (remainder : Bool) : zeroDivisorContract.HoldsCLR [zeroDivisorMethod remainder] 0 := by
  intro value memory _
  exact ⟨4, ⟨0, 2, .arithmetic .divideByZero⟩, rfl, rfl⟩

theorem unnamed_faults (exception : String) :
    ExecutionFault.clrException (.arithmetic .invalidOperands) ≠ some exception ∧
    ExecutionFault.clrException (.arithmetic .invalidBounds) ≠ some exception ∧
    ExecutionFault.clrException .invalidState ≠ some exception ∧
    ExecutionFault.clrException (.unsupported "operation") ≠ some exception ∧
    ExecutionFault.clrException .fuelExhausted ≠ some exception := by
  simp [ExecutionFault.clrException]

theorem memory_faults_never_named (rule : Fault) (reference : ManagedReference) (width : Nat)
    (exception : String) : ExecutionFault.clrException (.memory rule reference width) ≠ some exception := by
  simp [ExecutionFault.clrException]

theorem unsupported_never_named (exception : String) :
    ¬ RaisesCLR [{ code := [.unsupported "operation"], locals := [], returnsValue := false }] 0 [] empty exception := by
  apply RaisesCLR.not_of_invoke (fuel := 1)
    (fault := ⟨0, 0, .unsupported "Not a memory instruction"⟩)
  · simp [Settled]
  · rfl
  · simp [ExecutionFault.clrException]

theorem invalid_state_never_named (exception : String) : ¬ RaisesCLR [] 0 [] empty exception := by
  apply RaisesCLR.not_of_invoke (fuel := 1) (fault := ⟨0, 0, .invalidState⟩)
  · simp [Settled]
  · rfl
  · simp [ExecutionFault.clrException]

theorem thrown_still_named (exception : String) :
    RaisesCLR [{ code := [.throw exception], locals := [], returnsValue := false }] 0 [] empty exception :=
  RaisesCLR.of_raises ⟨1, ⟨0, 0, .thrown exception⟩, rfl, rfl⟩

#print axioms named_outcomes
#print axioms wrong_outcomes
#print axioms divide_and_mod_zero
#print axioms unsupported_never_named
#print axioms invalid_state_never_named

end Tests.RuntimeExceptions
