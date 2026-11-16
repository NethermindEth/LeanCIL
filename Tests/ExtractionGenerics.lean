import CIL.Extraction.Generics
import CIL.Extraction.Scalars
import CIL.Safety.SymbolicExecution
import Tests.Support

namespace Tests.ExtractionGenerics
open CIL CIL.Extraction

def word : TypeExpr := .atom
  "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
  "System.UInt64"
def raw : RawMethod := {
  token := 1, owner := "Test::Owner", hasThis := false, explicitThis := false,
  callingConvention := 16, attributes := 0, implementation := 0,
  returnType := .parameter 0, parameters := [.byref (.parameter 0)],
  locals := [.parameter 0], initLocals := true, maxStack := 2,
  genericParameters := [{ flags := 24, types := [] }],
  code := [⟨0, 2, .none⟩, ⟨1, 65045, .type (.parameter 0)⟩, ⟨7, 43, .target 3⟩, ⟨9, 42, .none⟩] }
def closed : RawMethod := { raw with
  callingConvention := 0, returnType := word, parameters := [.byref word],
  locals := [word], genericParameters := [],
  code := [⟨0, 2, .none⟩, ⟨1, 65045, .type word⟩, ⟨7, 43, .target 3⟩, ⟨9, 42, .none⟩] }
example : instantiateMethod [] raw [word] = some closed := by decide
example : instantiateMethod [] raw [] = none := by decide
example : instantiateMethod [] raw [.byref word] = none := by decide
example : instantiateMethod [] { raw with genericParameters := [{ flags := 4, types := [] }] } [word] = none := by decide
/-- `T : I<T>` closes at each argument and needs that argument's layout to list `I<argument>`. -/
def selfConstrained : RawMethod := { raw with
  genericParameters := [{
    flags := 24, types := [], interfaces := [.apply (.constructor "Test" "I`1") (.parameter 0)] }] }
def selfLayout : RawLayout := {
  identity := "Test::A", explicit := false, packing := 0, declaredSize := 0, fields := [],
  interfaces := ["Test::I`1<Test::A>"] }
example : (instantiateMethod [selfLayout] selfConstrained [.aggregate "Test::A" 0]).isSome := by
  decide +kernel
example : instantiateMethod [{ selfLayout with interfaces := ["Test::I`1<Test::B>"] }]
    selfConstrained [.aggregate "Test::A" 0] = none := by decide +kernel
example : instantiateMethod [] selfConstrained [word] = none := by decide +kernel
example : instantiateMethod [] raw [word] ≠ some { closed with locals := [] } := by decide
example : instantiateMethod [] raw [word] ≠ some { closed with returnType := .void } := by decide
example : instantiateMethod [] raw [word] ≠ some { closed with code := [⟨0, 42, .none⟩] } := by decide
example : instantiateMethod [] raw [word] ≠ some { closed with
    code := [⟨0, 2, .none⟩, ⟨1, 65045, .type word⟩, ⟨7, 43, .target 1⟩, ⟨9, 42, .none⟩] } := by decide
example : typeStorage [] (.atom "attacker" "System.UInt64") = none := by decide
example : typeStorage [{
    identity := "A", explicit := false, packing := 0, declaredSize := 0, fields := []
  }] (.aggregate "B" 0) = none := by decide
example : substituteType [word] (.apply (.constructor "scope" "Box`1") (.parameter 0)) =
    some (.apply (.constructor "scope" "Box`1") word) := by decide

/-- A call site whose scoped signature and generic arguments match the selected closed method. -/
def callSite (parameter : TypeExpr) : CallSite := {
  method := {
    owner := .atom "Test" "Owner", name := name!"Call", hasThis := false, genericArity := 1,
    returnType := word, parameters := [.byref parameter], methodArguments := [word] },
  name := "Call", target := .managed 1, typeArguments := [word], parameterCount := 1,
  returnsValue := true }

/-- A method whose one instruction calls `callSite parameter`. -/
def caller (parameter : TypeExpr) : RawMethod :=
  { closed with code := [⟨0, 40, .call (callSite parameter)⟩] }

/-- The emitted target and argument count are independently checked against the call site. -/
def callCode : Method := {
  locals := [], returnsValue := true, code := [.call (callSite word).method],
  links := [(0, .direct 0)] }

/-- Structural proof construction retains the complete managed-call predicate. -/
theorem structural_call :
    ManagedCallsValid [⟨[word], closed⟩] [] (fun _ => false) (caller word) [true] callCode := by
  cil_strict (cil_managed_calls [caller, callSite, closed, raw, word, callCode])
#print axioms structural_call

/-- Equal storage width does not permit substituting a signed parameter. -/
theorem signed_parameter_rejected :
    ¬ ManagedCallsValid [⟨[word], closed⟩] [] (fun _ => false)
      (caller (.atom runtimeScope "System.Int64")) [true] callCode := by
  fail_if_success (cil_strict (
    have invalid : ManagedCallsValid [⟨[word], closed⟩] [] (fun _ => false)
        (caller (.atom runtimeScope "System.Int64")) [true] callCode := by
      cil_managed_calls [caller, callSite, closed, raw, word, callCode]))
  decide +kernel
#print axioms signed_parameter_rejected

/-- A matching type name from another assembly remains a different parameter type. -/
theorem parameter_scope_rejected :
    ¬ ManagedCallsValid [⟨[word], closed⟩] [] (fun _ => false)
      (caller (.atom "attacker" "System.UInt64")) [true] callCode := by
  fail_if_success (cil_strict (
    have invalid : ManagedCallsValid [⟨[word], closed⟩] [] (fun _ => false)
        (caller (.atom "attacker" "System.UInt64")) [true] callCode := by
      cil_managed_calls [caller, callSite, closed, raw, word, callCode]))
  decide +kernel
#print axioms parameter_scope_rejected

/-- A closed signature cannot stand in for different method type arguments. -/
theorem generic_argument_rejected :
    ¬ ManagedCallsValid [⟨[.atom runtimeScope "System.Int64"], closed⟩] [] (fun _ => false)
      (caller word) [true] callCode := by
  fail_if_success (cil_strict (
    have invalid : ManagedCallsValid [⟨[.atom runtimeScope "System.Int64"], closed⟩] []
        (fun _ => false) (caller word) [true] callCode := by
      cil_managed_calls [caller, callSite, closed, raw, word, callCode]))
  decide +kernel
#print axioms generic_argument_rejected

/-- A call operand naming the method with a second parameter, so another argument count. -/
def twoArguments : Method :=
  { callCode with
    code := [.call { (callSite word).method with parameters := [.byref word, word] }] }

/-- Structural proof construction rejects a call with an altered operand and argument count. -/
theorem argument_count_rejected :
    ¬ ManagedCallsValid [⟨[word], closed⟩] [] (fun _ => false) (caller word) [true]
      twoArguments := by
  fail_if_success (cil_strict (
    have invalid : ManagedCallsValid [⟨[word], closed⟩] [] (fun _ => false) (caller word) [true]
        twoArguments := by
      cil_managed_calls [caller, callSite, closed, raw, word, callCode, twoArguments]))
  decide +kernel
#print axioms argument_count_rejected

/-- A class deriving from `Test.Counter` whose instances have two fields, its base's included,
    and its constructor, taking one `word`. -/
def tally : TypeExpr := .object "Test" "Tally"
def counter : TypeExpr := .object "Test" "Counter"
def tallyConstructor : RawMethod := { closed with
  token := 2, owner := "Test::Tally", hasThis := true, returnType := .void, parameters := [word],
  objectReceiver := true, objectFieldCount := 2, objectBases := [counter] }
/-- A struct `Test::Pair` and its constructor, taking one `word` after its storage's address. -/
def pair : TypeExpr := .aggregate "Test::Pair" 16
def pairConstructor : RawMethod := { tallyConstructor with
  token := 3, owner := "Test::Pair", objectReceiver := false, objectFieldCount := 0,
  objectBases := [] }
/-- The program's methods: the class constructor at index 0, the struct constructor at 1. -/
def constructors (index : Nat) : Option SpecializedMethod :=
  [(⟨[], tallyConstructor⟩ : SpecializedMethod), ⟨[], pairConstructor⟩][index]?
/-- The managed site of each constructor. -/
def construction : CallSite := {
  method := {
    owner := tally, name := name!".ctor", hasThis := true, genericArity := 0, returnType := .void,
    parameters := [word] },
  name := ".ctor", target := .managed 2, typeArguments := [], parameterCount := 1,
  returnsValue := false }
def pairConstruction : CallSite := { construction with method.owner := pair, target := .managed 3 }
/-- The raw `newobj` of each site. -/
def newTally : RawInstruction := ⟨0, 115, .call construction⟩
def newPair : RawInstruction := ⟨0, 115, .call pairConstruction⟩

-- A class construction is linked `.object` to the method its site names, with that class's
-- bases and one slot per field; a struct construction is linked `.aggregate` to its method. A
-- dead site passes unlinked.
theorem constructions_linked :
    validateConstructionWith constructors newTally true (some (.object 0 [counter] 16))
      construction.method ∧
    validateConstructionWith constructors newPair true (some (.aggregate 1 16))
      pairConstruction.method ∧
    validateConstructionWith constructors newTally false none construction.method := by
  decide +kernel
#print axioms constructions_linked

-- Forged links: another size, other bases, a constructor of the other kind, another method, no
-- link, a constructor the site does not name, or a call opcode.
theorem forged_constructions_rejected :
    ¬ validateConstructionWith constructors newTally true (some (.object 0 [counter] 8))
      construction.method ∧
    ¬ validateConstructionWith constructors newTally true (some (.object 0 [counter] 24))
      construction.method ∧
    ¬ validateConstructionWith constructors newTally true (some (.object 0 [] 16))
      construction.method ∧
    ¬ validateConstructionWith constructors newTally true
      (some (.object 0 [counter, tally] 16)) construction.method ∧
    ¬ validateConstructionWith constructors newTally true (some (.aggregate 0 16))
      construction.method ∧
    ¬ validateConstructionWith constructors newPair true (some (.object 1 [] 0))
      pairConstruction.method ∧
    ¬ validateConstructionWith constructors newTally true (some (.object 1 [counter] 16))
      construction.method ∧
    ¬ validateConstructionWith constructors newTally true none construction.method ∧
    ¬ validateConstructionWith constructors newTally true (some (.object 0 [counter] 16))
      pairConstruction.method ∧
    ¬ validateConstructionWith constructors ⟨0, 40, .call construction⟩ true
      (some (.object 0 [counter] 16)) construction.method := by
  decide +kernel
#print axioms forged_constructions_rejected

/-- A non-virtual instance method of `Tally` taking one word, and a call site of it. -/
def deposit : RawMethod := { closed with
  owner := "Test::Tally", hasThis := true, objectReceiver := true, parameters := [word] }
def depositSite : CallSite := {
  method := {
    owner := tally, name := name!"Deposit", hasThis := true, genericArity := 0, returnType := word,
    parameters := [word] },
  name := "Deposit", target := .managed closed.token, typeArguments := [], parameterCount := 1,
  returnsValue := true }

/-- The link of a call site whose callee is method 0. -/
def linkedZero : Option Link := some (.direct 0)

-- Only `callvirt` emits a receiver-checked call, counting the receiver, and only into a method
-- whose receiver is an object; a `callvirt` that skips the null check as a plain call is rejected.
theorem receiver_checked_calls :
    validateManagedCall [⟨[], deposit⟩] [] ⟨0, 111, .call depositSite⟩ true linkedZero
      (.callInstance 0 2) ∧
    ¬ validateManagedCall [⟨[], deposit⟩] [] ⟨0, 111, .call depositSite⟩ true linkedZero
      (.call depositSite.method) ∧
    ¬ validateManagedCall [⟨[], deposit⟩] [] ⟨0, 40, .call depositSite⟩ true linkedZero
      (.callInstance 0 2) ∧
    ¬ validateManagedCall [⟨[], deposit⟩] [] ⟨0, 111, .call depositSite⟩ true linkedZero
      (.callInstance 0 1) ∧
    ¬ validateManagedCall [⟨[], { deposit with objectReceiver := false }⟩] []
      ⟨0, 111, .call depositSite⟩ true linkedZero (.callInstance 0 2) := by decide +kernel
#print axioms receiver_checked_calls

/-- `deposit` marked virtual, as an override or a `virtual` member is. -/
def virtualDeposit : RawMethod := { deposit with attributes := virtualMethodAttribute }

-- A virtual body is admitted as the target of a plain `call`, which runs exactly that body, but a
-- `callvirt` of it can never become a fixed-target receiver-checked call.
theorem virtual_bodies_called_directly :
    validateManagedCall [⟨[], virtualDeposit⟩] [] ⟨0, 40, .call depositSite⟩ true
      linkedZero (.call depositSite.method) ∧
    ¬ validateManagedCall [⟨[], virtualDeposit⟩] [] ⟨0, 111, .call depositSite⟩ true
      linkedZero (.callInstance 0 2) := by decide +kernel
#print axioms virtual_bodies_called_directly

/-- A method with a class instance local and parameter beside a scalar of each. -/
def holder : RawMethod := { closed with
  parameters := [tally, word], locals := [tally, word], code := [] }

-- No byref to a class instance's slot exists, so none can stand in for an object receiver.
theorem class_instance_slots_unaddressed :
    scalarTransfer holder ⟨0, 18, .local 0⟩ [] = none ∧
    scalarTransfer holder ⟨0, 18, .local 1⟩ [] ≠ none ∧
    scalarTransfer holder ⟨0, 15, .argument 0⟩ [] = none ∧
    scalarTransfer holder ⟨0, 15, .argument 1⟩ [] ≠ none := by decide +kernel
#print axioms class_instance_slots_unaddressed

end Tests.ExtractionGenerics
