import CIL.Extraction.Generics
import CIL.Extraction.MetadataResolution
import CIL.Extraction.Scalars
import CIL.Safety.SymbolicExecution
import Tests.Support
import Tests.Support.FixtureAssembly

/-! Raw method specialization, call-site binding and construction checks. -/

namespace Tests.ExtractionGenerics
open CIL CIL.Extraction

def word : TypeExpr := .primitive .uint64
/-- The assembly every fixture method belongs to. -/
def testPin : AssemblyPin := ⟨Tests.fixtureAssembly⟩
/-- The scope text of `testPin` in the fixture's type names. -/
def testScope : String := Tests.fixtureScope
def raw : RawMethod := {
  token := 1, owner := (testScope ++ "::Owner"), hasThis := false, explicitThis := false,
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
    flags := 24, types := [],
    interfaces := [.apply (.objectConstructor "Test" "I`1") (.parameter 0)] }] }
def selfLayout : RawLayout := {
  identity := "Test::A", explicit := false, packing := 0, declaredSize := 0, fields := [],
  interfaces := ["Test::I`1<Test::A>"] }
/-- Flag 0x08, `System.ValueType` and `unmanaged` each refuse class arguments and require an
    admitted value type; byref-like structs require the `allows ref struct` flag 0x20. -/
theorem value_type_constraints_reject_classes :
    let classArg : TypeExpr := .object testScope "C"
    let byRefLayout : RawLayout := { selfLayout with byRefLike := true }
    let valueConstrained : RawMethod := { raw with
      genericParameters := [{ flags := 0, types := [valueTypeConstraint] }] }
    let unmanagedConstrained : RawMethod := { raw with
      genericParameters := [{ flags := 0, types := [unmanagedTypeConstraint] }] }
    let refStructAllowed : RawMethod := { raw with
      genericParameters := [{ flags := 0x28, types := [valueTypeConstraint] }] }
    instantiateMethod [] raw [classArg] = none ∧
    instantiateMethod [] valueConstrained [classArg] = none ∧
    instantiateMethod [] unmanagedConstrained [classArg] = none ∧
    (instantiateMethod [] valueConstrained [word]).isSome ∧
    (instantiateMethod [] unmanagedConstrained [word]).isSome ∧
    instantiateMethod [byRefLayout] raw [.aggregate "Test::A" 0] = none ∧
    (instantiateMethod [byRefLayout] refStructAllowed [.aggregate "Test::A" 0]).isSome := by
  decide +kernel
#print axioms value_type_constraints_reject_classes
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
example : typeStorage [] (.atom "attacker" "System.UInt64" .valueType) = none := by decide
example : typeStorage [{
    identity := "A", explicit := false, packing := 0, declaredSize := 0, fields := []
  }] (.aggregate "B" 0) = none := by decide
example : substituteType [word] (.apply (.constructor "scope" "Box`1") (.parameter 0)) =
    some (.apply (.constructor "scope" "Box`1") word) := by decide

/-- A call site whose scoped signature and generic arguments match the selected closed method. -/
def callSite (parameter : TypeExpr) : CallSite := {
  declared := { convention := 0x10, returnType := word, parameters := [.byref (.parameter 0)] },
  method := {
    owner := .atom testScope "Owner" .classType, name := name!"Call", hasThis := false,
    genericArity := 1,
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

/-- A generic call site whose operand, link and closed signature agree passes the check. -/
theorem structural_call :
    ManagedCallsValid [⟨[word], closed, testPin⟩] [] (fun _ => false) (caller word) [true]
      callCode := by
  decide +kernel
#print axioms structural_call

/-- Equal storage width does not permit substituting a signed parameter. -/
theorem signed_parameter_rejected :
    ¬ ManagedCallsValid [⟨[word], closed, testPin⟩] [] (fun _ => false)
      (caller (.primitive .int64)) [true] callCode := by
  decide +kernel
#print axioms signed_parameter_rejected

/-- A matching type name from another assembly remains a different parameter type. -/
theorem parameter_scope_rejected :
    ¬ ManagedCallsValid [⟨[word], closed, testPin⟩] [] (fun _ => false)
      (caller (.atom "attacker" "System.UInt64" .valueType)) [true] callCode := by
  decide +kernel
#print axioms parameter_scope_rejected

/-- A closed signature cannot stand in for different method type arguments. -/
theorem generic_argument_rejected :
    ¬ ManagedCallsValid [⟨[.primitive .int64], closed, testPin⟩] [] (fun _ => false)
      (caller word) [true] callCode := by
  decide +kernel
#print axioms generic_argument_rejected

/-- A call operand naming the method with a second parameter, so another argument count. -/
def twoArguments : Method :=
  { callCode with
    code := [.call { (callSite word).method with parameters := [.byref word, word] }] }

/-- A call operand with an altered argument count fails the check. -/
theorem argument_count_rejected :
    ¬ ManagedCallsValid [⟨[word], closed, testPin⟩] [] (fun _ => false) (caller word) [true]
      twoArguments := by
  decide +kernel
#print axioms argument_count_rejected

/-- A class deriving from `Test.Counter` whose instances have two fields, its base's included,
    and its constructor, taking one `word`. -/
def tally : TypeExpr := .object testScope "Tally"
def counter : TypeExpr := .object testScope "Counter"
def tallyConstructor : RawMethod := { closed with
  token := 2, owner := (testScope ++ "::Tally"), hasThis := true, returnType := .void,
  parameters := [word],
  receiverClass := some tally, objectFieldCount := 2, objectBases := [counter] }
/-- A struct `Test::Pair` and its constructor, taking one `word` after its storage's address. -/
def pair : TypeExpr := .aggregate (testScope ++ "::Pair") 16
def pairConstructor : RawMethod := { tallyConstructor with
  token := 3, owner := (testScope ++ "::Pair"), receiverClass := none, objectFieldCount := 0,
  objectBases := [] }
/-- The program's methods: the class constructor at index 0, the struct constructor at 1. -/
def constructors (index : Nat) : Option SpecializedMethod :=
  [(⟨[], tallyConstructor, testPin⟩ : SpecializedMethod), ⟨[], pairConstructor, testPin⟩][index]?
/-- The managed site of each constructor. -/
def construction : CallSite := {
  declared := { convention := 0x20, parameters := [word] },
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

/-- Class `Tally` as its TypeDef row resolves it. -/
def tallyRow : NamedType :=
  { scope := bytesOf testScope, name := bytesOf "Tally", parts := [[], bytesOf "Tally"],
    kind := .classType, pinned := true, assembly := some Tests.fixtureAssembly }
/-- Struct `Pair` as its TypeDef row resolves it. -/
def pairRow : NamedType :=
  { tallyRow with name := bytesOf "Pair", parts := [[], bytesOf "Pair"], kind := .valueType }
/-- A signature frame anchored in the fixture assembly. -/
def fixtureFrame : CIL.Extraction.Frame :=
  { corlib := some runtimeScopeBytes, anchor := bytesOf testScope, arity := 0, ownerArity := 0 }

/-- An atom is admitted only at the head kind its definition states. -/
theorem atom_heads_follow_their_rows :
    fixtureFrame.admits (.named tallyRow) (.atom testScope "Tally" .classType) = true ∧
    fixtureFrame.admits (.named tallyRow) (.atom testScope "Tally" .valueType) = false ∧
    fixtureFrame.admits (.named tallyRow) (.atom testScope "Tally" .interfaceType) = false ∧
    fixtureFrame.admits (.named pairRow) (.atom testScope "Pair" .valueType) = true ∧
    fixtureFrame.admits (.named pairRow) (.atom testScope "Pair" .classType) = false := by
  decide +kernel
#print axioms atom_heads_follow_their_rows

/-- `Tally`'s constructor with the receiver facts of a struct constructor. -/
def structShapedTally : RawMethod :=
  { tallyConstructor with receiverClass := none, objectFieldCount := 0, objectBases := [] }
/-- The program whose only method is `structShapedTally`. -/
def structShapedMethods (index : Nat) : Option SpecializedMethod :=
  [(⟨[], structShapedTally, testPin⟩ : SpecializedMethod)][index]?
/-- The construction of `Tally` through an atom owner claiming `kind`. -/
def atomConstruction (kind : HeadKind) : CallSite :=
  { construction with method.owner := .atom testScope "Tally" kind }

/-- A class's constructor cannot be linked as a struct construction: the value-headed atom of
    `Tally` is refused against its row, and its class-headed atom links no aggregate. A
    value-headed atom of `Pair` still links its aggregate and a class-headed one does not. -/
theorem forged_value_head_rejected :
    fixtureFrame.admits (.named tallyRow) (atomConstruction .valueType).method.owner = false ∧
    ¬ validateConstructionWith structShapedMethods ⟨0, 115, .call (atomConstruction .classType)⟩
      true (some (.aggregate 0 16)) (atomConstruction .classType).method ∧
    validateConstructionWith constructors ⟨0, 115, .call
      { pairConstruction with method.owner := .atom testScope "Pair" .valueType }⟩
      true (some (.aggregate 1 16)) { pairConstruction.method with
        owner := .atom testScope "Pair" .valueType } ∧
    ¬ validateConstructionWith constructors ⟨0, 115, .call
      { pairConstruction with method.owner := .atom testScope "Pair" .classType }⟩
      true (some (.aggregate 1 16)) { pairConstruction.method with
        owner := .atom testScope "Pair" .classType } := by
  decide +kernel
#print axioms forged_value_head_rejected

/-- A non-virtual instance method of `Tally` taking one word, and a call site of it. -/
def deposit : RawMethod := { closed with
  owner := (testScope ++ "::Tally"), hasThis := true, receiverClass := some tally,
  parameters := [word] }
def depositSite : CallSite := {
  declared := { convention := 0x20, returnType := word, parameters := [word] },
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
    validateManagedCall [⟨[], deposit, testPin⟩] [] ⟨0, 111, .call depositSite⟩ true linkedZero
      (.callvirt depositSite.method) ∧
    ¬ validateManagedCall [⟨[], deposit, testPin⟩] [] ⟨0, 111, .call depositSite⟩ true linkedZero
      (.call depositSite.method) ∧
    ¬ validateManagedCall [⟨[], deposit, testPin⟩] [] ⟨0, 40, .call depositSite⟩ true linkedZero
      (.callvirt depositSite.method) ∧
    ¬ validateManagedCall [⟨[], deposit, testPin⟩] [] ⟨0, 111, .call depositSite⟩ true linkedZero
      (.callvirt { depositSite.method with parameters := [] }) ∧
    ¬ validateManagedCall [⟨[], { deposit with receiverClass := none }, testPin⟩] []
      ⟨0, 111, .call depositSite⟩ true linkedZero (.callvirt depositSite.method) := by
  decide +kernel
#print axioms receiver_checked_calls

/-- `deposit` marked virtual, as an override or a `virtual` member is. -/
def virtualDeposit : RawMethod := { deposit with attributes := virtualMethodAttribute }

-- A virtual body is admitted as the target of a plain `call`, which runs exactly that body, but a
-- `callvirt` of it can never become a fixed-target receiver-checked call.
theorem virtual_bodies_called_directly :
    validateManagedCall [⟨[], virtualDeposit, testPin⟩] [] ⟨0, 40, .call depositSite⟩ true
      linkedZero (.call depositSite.method) ∧
    ¬ validateManagedCall [⟨[], virtualDeposit, testPin⟩] [] ⟨0, 111, .call depositSite⟩ true
      linkedZero (.callvirt depositSite.method) := by decide +kernel
#print axioms virtual_bodies_called_directly

/-- Both receiver link kinds authenticate the slot. A virtual table requires virtual bodies. -/
theorem receiver_links_bind_slot :
    let site : RawInstruction := ⟨0, 111, .call depositSite⟩
    let other := Instruction.callvirt { depositSite.method with name := name!"Withdraw" }
    let table := some (Link.virtual [(tally, 0)])
    validateManagedCall [⟨[], virtualDeposit, testPin⟩] [] site true table
      (.callvirt depositSite.method) ∧
    ¬ validateManagedCall [⟨[], deposit, testPin⟩] [] site true table
      (.callvirt depositSite.method) ∧
    ¬ validateManagedCall [⟨[], deposit, testPin⟩] [] site true linkedZero other ∧
    ¬ validateManagedCall [⟨[], virtualDeposit, testPin⟩] [] site true table other := by
  decide +kernel
#print axioms receiver_links_bind_slot

/-- Managed addresses and catalog entries authenticate the token of the indexed body. -/
theorem managed_pointer_bindings :
    let first := { closed with parameters := [], returnType := .void }
    let second := { first with token := 2 }
    let methods : List SpecializedMethod := [⟨[], first, testPin⟩, ⟨[], second, testPin⟩]
    let signature : ManagedSignature := ⟨.void, []⟩
    let identity : ManagedIdentity := ⟨first.owner, first.token, []⟩
    let site := { callSite word with
      method.parameters := [], method.returnType := .void,
      method.methodArguments := [], method.genericArity := 0, typeArguments := [],
      parameterCount := 0, returnsValue := false }
    let address := Instruction.ldftn identity signature
    let load := RawInstruction.mk 0 65030 (.call site)
    let indirect := RawInstruction.mk 0 41 (.indirectCall .void [] false false 0)
    let transfer := Instruction.calli signature false
    let target : ManagedTarget := ⟨identity, 0⟩
    let forged : ManagedTarget := ⟨{ identity with token := second.token }, 0⟩
    validateManagedCall methods [] load true (some (.address 0)) address ∧
      ¬ validateManagedCall methods [] load true (some (.address 1)) address ∧
      validateManagedCall methods [] indirect true (some (.indirect [target])) transfer ∧
      ¬ validateManagedCall methods [] indirect true (some (.indirect [target, forged]))
        transfer := by decide +kernel
#print axioms managed_pointer_bindings

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
