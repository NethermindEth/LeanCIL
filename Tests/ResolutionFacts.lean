import CIL.Resolution
import CIL.Safety.ValueSteps
import CIL.Safety.StepTransport
import CIL.Extraction.Translation

/-!
# Declared narrowing

Pins the narrowing a declared type implies, which `ret` applies to a method's return value:
each primitive below 32 bits narrows to its own width and signedness and wider primitives do
not; an enum narrows as its underlying primitive only where `typeStorage` admits that primitive;
struct, object, pointer, array and span types never narrow; a misspelled name or a primitive
name from another assembly is not a primitive; and a method that returns nothing never narrows,
whatever its declared return type says. The method facts are proved by lemma application, as a
generated fact is, so no proof below evaluates a type name except the misspelling cases.

Pins how a method reads each argument: an argument without a home narrowed as its declared type
requires, `this` as it arrives, and a homed argument from the slot after the declared locals,
which is the slot the argument check expects. `cil_resolution_facts` states the same for static
and instance methods and across suffix blocks, refuses homes out of argument order, and the
simplifier reads a literal body without facts and leaves a symbolic one alone.

Pins the shape of array elements: a primitive, an enum, a class and a function pointer by lemma,
a struct of the size its checked layout gives, and no shape for a by-ref-like struct or one the
layouts do not hold. `cil_resolution_facts` declares one fact per distinct element type a raw
method names, reads struct layouts across suffix blocks shared by an environment's methods, and
the simplifier reads a literal body without facts.
-/

namespace Tests.ResolutionFacts

open CIL CIL.Extraction

-- A primitive below 32 bits narrows to its own width and signedness; the extractor's own table
-- agrees head by head (Tests/InstructionIndexes.cs).
example : declaredNarrow [] (.atom runtimeScope "System.SByte") = some .signed8 :=
  declaredNarrow_primitive [] .sbyte
example : declaredNarrow [] (.atom runtimeScope "System.Byte") = some .unsigned8 :=
  declaredNarrow_primitive [] .byte
example : declaredNarrow [] (.atom runtimeScope "System.Boolean") = some .unsigned8 :=
  declaredNarrow_primitive [] .boolean
example : declaredNarrow [] (.atom runtimeScope "System.Int16") = some .signed16 :=
  declaredNarrow_primitive [] .int16
example : declaredNarrow [] (.atom runtimeScope "System.UInt16") = some .unsigned16 :=
  declaredNarrow_primitive [] .uint16
example : declaredNarrow [] (.atom runtimeScope "System.Char") = some .unsigned16 :=
  declaredNarrow_primitive [] .char

-- A primitive of 32 bits or more, or a floating-point one, is returned as it is.
example : declaredNarrow [] (.atom runtimeScope "System.Int32") = none :=
  declaredNarrow_primitive [] .int32
example : declaredNarrow [] (.atom runtimeScope "System.UInt32") = none :=
  declaredNarrow_primitive [] .uint32
example : declaredNarrow [] (.atom runtimeScope "System.Int64") = none :=
  declaredNarrow_primitive [] .int64
example : declaredNarrow [] (.atom runtimeScope "System.UInt64") = none :=
  declaredNarrow_primitive [] .uint64
example : declaredNarrow [] (.atom runtimeScope "System.IntPtr") = none :=
  declaredNarrow_primitive [] .intPtr
example : declaredNarrow [] (.atom runtimeScope "System.UIntPtr") = none :=
  declaredNarrow_primitive [] .uintPtr
example : declaredNarrow [] (.atom runtimeScope "System.Single") = none :=
  declaredNarrow_primitive [] .single
example : declaredNarrow [] (.atom runtimeScope "System.Double") = none :=
  declaredNarrow_primitive [] .double

-- An enum narrows as its underlying integer type.
example : declaredNarrow [] (.enum "Examples.Small" (.atom runtimeScope "System.Int16")) =
    some .signed16 :=
  (declaredNarrow_enum [] "Examples.Small" .int16).trans rfl
example : declaredNarrow [] (.enum "Examples.Flags" (.atom runtimeScope "System.Byte")) =
    some .unsigned8 :=
  (declaredNarrow_enum [] "Examples.Flags" .byte).trans rfl
example : declaredNarrow [] (.enum "Examples.Signed" (.atom runtimeScope "System.SByte")) =
    some .signed8 :=
  (declaredNarrow_enum [] "Examples.Signed" .sbyte).trans rfl
example : declaredNarrow [] (.enum "Examples.Wide" (.atom runtimeScope "System.UInt16")) =
    some .unsigned16 :=
  (declaredNarrow_enum [] "Examples.Wide" .uint16).trans rfl
example : declaredNarrow [] (.enum "Examples.Plain" (.atom runtimeScope "System.Int32")) = none :=
  (declaredNarrow_enum [] "Examples.Plain" .int32).trans rfl

-- An enum over a type `typeStorage` does not admit as an enum's underlying type has no storage.
example : declaredNarrow [] (.enum "Examples.Truth" (.atom runtimeScope "System.Boolean")) =
    none :=
  (declaredNarrow_enum [] "Examples.Truth" .boolean).trans rfl

/-- A struct layout for the aggregate return below. -/
def pointLayout : RawLayout :=
  { identity := "Examples.Point", explicit := false, packing := 0, declaredSize := 0,
    fields := [{ type := .signed8 }, { type := .signed8 }] }

-- A struct, even one of byte fields, and every other non-primitive head do not narrow.
example : declaredNarrow [pointLayout] (.aggregate "Examples.Point" 0) = none :=
  declaredNarrow_of_not_candidate _ _ rfl
example : declaredNarrow [] (.object "Examples" "Examples.Box") = none :=
  declaredNarrow_of_not_candidate _ _ rfl
example : declaredNarrow [] (.pointer (.atom runtimeScope "System.Byte")) = none :=
  declaredNarrow_of_not_candidate _ _ rfl
example : declaredNarrow [] (.array (.atom runtimeScope "System.Byte")) = none :=
  declaredNarrow_of_not_candidate _ _ rfl
example : declaredNarrow []
    (.apply (.constructor runtimeScope "System.Span`1") (.atom runtimeScope "System.Byte")) =
    none :=
  declaredNarrow_of_not_candidate _ _ rfl

-- A name that only resembles a primitive's, or a primitive's name in another assembly, is not
-- that primitive and does not narrow.
example : declaredNarrow [] (.atom runtimeScope "SByte") = none := by rfl
/-- The assembly scope of the example application. -/
def examplesScope : String := "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

example : declaredNarrow [] (.atom examplesScope "System.Byte") = none := by rfl

/-- A method that returns a byte. -/
def byteReturn : Method :=
  { code := [.ldc_i4 7, .ret], locals := [], returnsValue := true,
    declared := { returnType := .atom runtimeScope "System.Byte" } }

/-- A method whose return value narrows to a byte. -/
theorem byteReturn_returnNarrow : byteReturn.returnNarrow = some .unsigned8 :=
  Method.returnNarrow_of_declared rfl rfl (declaredNarrow_primitive _ .byte)

/-- info: 'Tests.ResolutionFacts.byteReturn_returnNarrow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms byteReturn_returnNarrow

-- A narrowed method returns a value.
example : byteReturn.returnsValue = true :=
  Method.returnsValue_of_returnNarrow byteReturn_returnNarrow

/-- A method returning an enum over `System.Int16`. -/
def enumReturn : Method :=
  { code := [.ldc_i4 7, .ret], locals := [], returnsValue := true,
    declared := { returnType := .enum "Examples.Small" (.atom runtimeScope "System.Int16") } }

/-- A method whose return value narrows as its enum's underlying type. -/
theorem enumReturn_returnNarrow : enumReturn.returnNarrow = some .signed16 :=
  Method.returnNarrow_of_declared rfl rfl ((declaredNarrow_enum _ _ .int16).trans rfl)

/-- info: 'Tests.ResolutionFacts.enumReturn_returnNarrow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms enumReturn_returnNarrow

/-- A method returning a struct. -/
def pointReturn : Method :=
  { code := [.ret], locals := [], returnsValue := true,
    declared := { returnType := .aggregate "Examples.Point" 0 },
    environment := { rawLayouts := [pointLayout] } }

/-- A method returning a struct does not narrow its return value. -/
theorem pointReturn_returnNarrow : pointReturn.returnNarrow = none :=
  Method.returnNarrow_of_declared rfl rfl (declaredNarrow_of_not_candidate _ _ rfl)

/-- info: 'Tests.ResolutionFacts.pointReturn_returnNarrow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pointReturn_returnNarrow

/-- A method that returns nothing, with a declared return type that would narrow. -/
def voidReturn : Method :=
  { code := [.ret], locals := [], returnsValue := false,
    declared := { returnType := .atom runtimeScope "System.Byte" } }

/-- A method that returns nothing does not narrow, whatever its declared return type. -/
theorem voidReturn_returnNarrow : voidReturn.returnNarrow = none :=
  Method.returnNarrow_of_void rfl

/-- info: 'Tests.ResolutionFacts.voidReturn_returnNarrow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms voidReturn_returnNarrow

-- The lemmas generated facts apply stay within the kernel's standard axioms.
/-- info: 'CIL.Extraction.declaredNarrow_primitive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms declaredNarrow_primitive

/-- info: 'CIL.Extraction.declaredNarrow_enum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms declaredNarrow_enum

/-- info: 'CIL.Extraction.declaredNarrow_of_not_candidate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms declaredNarrow_of_not_candidate

namespace Generated

open Lean Elab Command in
/-- A named signature fixture with both generated and simplifier proofs. -/
elab "resolution_fixture " name:ident " : " type:term " returns " returns:term
    " narrows " expected:term : command => do
  let returnsName := mkIdent (name.getId.appendAfter "_returnsValue")
  let declaredName := mkIdent (name.getId.appendAfter "_declared")
  let narrowedName := mkIdent (name.getId.appendAfter "_returnNarrow")
  let simplifiedName := mkIdent (name.getId.appendAfter "_simplified")
  elabCommand (← `(def $name : Method :=
    { code := [], locals := [], returnsValue := $returns, declared := { returnType := $type },
      environment := { rawLayouts := [pointLayout] } }))
  elabCommand (← `(theorem $returnsName : ($name).returnsValue = $returns := rfl))
  elabCommand (← `(theorem $declaredName : ($name).declared = { returnType := $type } := rfl))
  elabCommand (← `(cil_resolution_facts $name))
  elabCommand (← `(example : ($name).returnNarrow = $expected := $narrowedName))
  elabCommand (← `(theorem $simplifiedName : ($name).returnNarrow = $expected := by
    simp only [cil_step]))
  elabCommand (← `(#print axioms $returnsName))
  elabCommand (← `(#print axioms $declaredName))
  elabCommand (← `(#print axioms $narrowedName))
  elabCommand (← `(#print axioms $simplifiedName))

resolution_fixture primitive : (.atom runtimeScope "System.Byte")
  returns true narrows (some .unsigned8)
resolution_fixture enumeration : (.enum "Small" (.atom runtimeScope "System.Int16"))
  returns true narrows (some .signed16)
resolution_fixture invalidEnumeration : (.enum "Truth" (.atom runtimeScope "System.Boolean"))
  returns true narrows none
resolution_fixture nestedEnumeration :
  (.enum "Outer" (.enum "Inner" (.atom runtimeScope "System.Byte")))
  returns true narrows (some .unsigned8)
resolution_fixture noValue : (.atom runtimeScope "System.Byte") returns false narrows none
resolution_fixture aggregate : (.aggregate "Examples.Point" 0) returns true narrows none
resolution_fixture foreign : (.atom "Other" "System.Byte") returns true narrows none
resolution_fixture misspelled : (.atom runtimeScope "System.Bytex") returns true narrows none

/-- Enum storage over an aggregate stays unresolved as storage, but its narrowing is known. -/
def aggregateEnum (layouts : List RawLayout) : Method :=
  { code := [], locals := [], returnsValue := true, environment := { rawLayouts := layouts },
    declared := { returnType := .enum "Bad" (.aggregate "Point" 0) } }

/-- The aggregate enum fixture returns a value. -/
theorem aggregateEnum_returnsValue (layouts : List RawLayout) :
    (aggregateEnum layouts).returnsValue = true := rfl
#print axioms aggregateEnum_returnsValue

/-- The aggregate enum fixture retains its exact declared type. -/
theorem aggregateEnum_declared (layouts : List RawLayout) :
    (aggregateEnum layouts).declared =
      { returnType := .enum "Bad" (.aggregate "Point" 0) } := rfl
#print axioms aggregateEnum_declared

cil_resolution_facts aggregateEnum
#print axioms aggregateEnum_returnNarrow

/-- Enum narrowing over an aggregate does not inspect a symbolic layout table. -/
theorem aggregateEnum_simplified (layouts : List RawLayout) :
    (aggregateEnum layouts).returnNarrow = none := by simp only [cil_step]
#print axioms aggregateEnum_simplified

/-- Nested enum metadata over an aggregate array retains an arbitrary layout table. -/
def arrayEnum (layouts : List RawLayout) : Method :=
  { code := [], locals := [], returnsValue := true, environment := { rawLayouts := layouts },
    declared := { returnType := .enum "Outer" (.enum "Bad" (.array (.aggregate "Point" 0))) } }

/-- The aggregate array enum fixture returns a value. -/
theorem arrayEnum_returnsValue (layouts : List RawLayout) :
    (arrayEnum layouts).returnsValue = true := rfl
#print axioms arrayEnum_returnsValue

/-- The aggregate array enum fixture retains its exact declared type. -/
theorem arrayEnum_declared (layouts : List RawLayout) :
    (arrayEnum layouts).declared =
      { returnType := .enum "Outer" (.enum "Bad" (.array (.aggregate "Point" 0))) } := rfl
#print axioms arrayEnum_declared

cil_resolution_facts arrayEnum
#print axioms arrayEnum_returnNarrow

/-- Nested enum narrowing over an aggregate array does not inspect a symbolic layout table. -/
theorem arrayEnum_simplified (layouts : List RawLayout) :
    (arrayEnum layouts).returnNarrow = none := by simp only [cil_step]
#print axioms arrayEnum_simplified

/-- info: 'Tests.ResolutionFacts.Generated.primitive_returnNarrow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms primitive_returnNarrow

/-- A symbolic signature retains its unknown return narrowing. -/
def unknown (type : TypeExpr) : Method :=
  { code := [], locals := [], returnsValue := true, declared := { returnType := type } }

/-- The symbolic method always returns a value. -/
theorem unknown_returnsValue (type : TypeExpr) : (unknown type).returnsValue = true := rfl
#print axioms unknown_returnsValue

/-- The symbolic method preserves its declared type. -/
theorem unknown_declared (type : TypeExpr) :
    (unknown type).declared = { returnType := type } := rfl
#print axioms unknown_declared

/--
error: cil_resolution_facts: return narrowing of
Tests.ResolutionFacts.Generated.unknown is unresolved
-/
#guard_msgs (whitespace := lax) in
cil_resolution_facts unknown

example (type : TypeExpr) (expected : Option NarrowKind)
    (known : (unknown type).returnNarrow = expected) :
    (unknown type).returnNarrow = expected := by
  fail_if_success simp only [cil_step]
  exact known

/-- Differing return narrowing prevents metadata transport even when both methods return values. -/
theorem differing_narrowing_rejected : ¬ CIL.Safety.StepMetadata primitive enumeration := by
  intro metadata
  have mismatch := metadata.returnNarrow
  rw [primitive_returnNarrow, enumeration_returnNarrow] at mismatch
  cases mismatch
#print axioms differing_narrowing_rejected

/-- Signature and environment evidence suffice without an instruction-shaped hypothesis. -/
theorem shape_narrowing {rawLayouts : List RawLayout} {layouts : Array ComputedLayout}
    {closed : RawMethod} {method : Method}
    (shape : MethodShapeValid closed method)
    (environment : MethodEnvironmentValid rawLayouts layouts method) :
    method.returnNarrow = declaredNarrow rawLayouts closed.returnType :=
  returnNarrow_of_shape shape environment
#print axioms shape_narrowing

end Generated


/-! ## Argument access -/

/-- A byte parameter and an int parameter, returning an int. -/
def twoParameterSignature : DeclaredSignature :=
  { parameters := [.atom runtimeScope "System.Byte", .atom runtimeScope "System.Int32"],
    returnType := .atom runtimeScope "System.Int32" }

/-- A static method with a byte parameter read as it arrives and an int parameter that the body
    stores to, so it has a home after the method's one local. -/
def twoParameters : Method :=
  { code := [.ldc_i4 0, .stloc 1, .ldarg 0, .ret], locals := [.i32 0],
    localKinds := [.word32], parameterHomes := [(1, .word32)], returnsValue := true,
    declared := twoParameterSignature }

-- The byte argument is read narrowed to its declared width.
example : twoParameters.argumentAccess 0 = .value (some .unsigned8) :=
  Method.argumentAccess_value rfl rfl (declaredNarrow_primitive _ .byte)

-- The stored argument is read from its home, the slot after the one declared local.
example : twoParameters.argumentAccess 1 = .home 1 := Method.argumentAccess_home rfl rfl

-- An index past the declared parameters has no type and is read as it arrives.
example : twoParameters.argumentAccess 2 = .value none := Method.argumentAccess_undeclared rfl rfl

/-- The return fact the facts command also reads. -/
theorem twoParameters_returnsValue : twoParameters.returnsValue = true := rfl
#print axioms twoParameters_returnsValue

/-- The declared signature the facts command also reads. -/
theorem twoParameters_declared : twoParameters.declared = twoParameterSignature := rfl
#print axioms twoParameters_declared

cil_resolution_facts twoParameters

example : twoParameters.argumentAccess 0 = .value (some .unsigned8) :=
  twoParameters_argumentAccess0
example : twoParameters.argumentAccess 1 = .home 1 := twoParameters_argumentAccess1
example : twoParameters.argumentAccess 1 = .home 1 := by simp only [cil_code]

/--
info: 'Tests.ResolutionFacts.twoParameters_argumentAccess0' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms twoParameters_argumentAccess0

/--
info: 'Tests.ResolutionFacts.twoParameters_argumentAccess1' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms twoParameters_argumentAccess1

/-- A value-type instance method's signature: a short and a byte-backed enum. -/
def instanceSignature : DeclaredSignature :=
  { receiver := some .reference,
    parameters := [.atom runtimeScope "System.Int16",
      .enum "Examples.Flags" (.atom runtimeScope "System.Byte")] }

/-- An instance method: `this` is stored to, so it has the home; its parameters follow. -/
def instanceMethod : Method :=
  { code := [.ret], locals := [], parameterHomes := [(0, .reference)], returnsValue := false,
    declared := instanceSignature }

/-- The return fact the facts command also reads. -/
theorem instanceMethod_returnsValue : instanceMethod.returnsValue = false := rfl
#print axioms instanceMethod_returnsValue

/-- The declared signature the facts command also reads. -/
theorem instanceMethod_declared : instanceMethod.declared = instanceSignature := rfl
#print axioms instanceMethod_declared

cil_resolution_facts instanceMethod

-- Parameter i of an instance method is argument i + 1.
example : instanceMethod.argumentAccess 0 = .home 0 := instanceMethod_argumentAccess0
example : instanceMethod.argumentAccess 1 = .value (some .signed16) :=
  instanceMethod_argumentAccess1
example : instanceMethod.argumentAccess 2 = .value (some .unsigned8) :=
  instanceMethod_argumentAccess2

/-- An unhomed `this` is read as it arrives. -/
def unhomedThis : Method :=
  { code := [.ret], locals := [], returnsValue := false,
    declared := { receiver := some .object, parameters := [.atom runtimeScope "System.Char"] } }

/-- The return fact the facts command also reads. -/
theorem unhomedThis_returnsValue : unhomedThis.returnsValue = false := rfl
#print axioms unhomedThis_returnsValue

/-- The declared signature the facts command also reads. -/
theorem unhomedThis_declared : unhomedThis.declared =
    { receiver := some .object, parameters := [.atom runtimeScope "System.Char"] } := rfl
#print axioms unhomedThis_declared

cil_resolution_facts unhomedThis

example : unhomedThis.argumentAccess 0 = .value none := unhomedThis_argumentAccess0
example : unhomedThis.argumentAccess 1 = .value (some .unsigned16) := unhomedThis_argumentAccess1

/-- Forty parameters, so the facts read three blocks of parameter types, with homes before the
    first block boundary, on both sides of it, at the last index of a block and at the end. -/
def wide : Method :=
  { code := [.ret], locals := [.i32 0, .i32 0],
    localKinds := [.word32, .word32], returnsValue := false,
    parameterHomes := [(3, .word32), (15, .word32), (16, .word32), (17, .word32), (31, .word32),
      (39, .narrow .unsigned16)],
    declared := { parameters := (List.replicate 39 (.atom runtimeScope "System.Int32")) ++
      [.atom runtimeScope "System.Char"] } }

/-- The return fact the facts command also reads. -/
theorem wide_returnsValue : wide.returnsValue = false := rfl
#print axioms wide_returnsValue

/-- The declared signature the facts command also reads. -/
theorem wide_declared : wide.declared = { parameters :=
    (List.replicate 39 (.atom runtimeScope "System.Int32")) ++
      [.atom runtimeScope "System.Char"] } := rfl
#print axioms wide_declared

cil_resolution_facts wide

-- Each fact agrees with the definition, decided by evaluation.
example : wide.argumentAccess 0 = .value none := wide_argumentAccess0
example : wide.argumentAccess 3 = .home 2 := wide_argumentAccess3
example : wide.argumentAccess 4 = .value none := wide_argumentAccess4
example : wide.argumentAccess 15 = .home 3 := wide_argumentAccess15
example : wide.argumentAccess 16 = .home 4 := wide_argumentAccess16
example : wide.argumentAccess 17 = .home 5 := wide_argumentAccess17
example : wide.argumentAccess 18 = .value none := wide_argumentAccess18
example : wide.argumentAccess 32 = .value none := wide_argumentAccess32
example : wide.argumentAccess 39 = .home 7 := wide_argumentAccess39
example : ∀ index, index < 40 → wide.argumentAccess index =
    if index ∈ [3, 15, 16, 17, 31, 39] then .home (2 + [3, 15, 16, 17, 31, 39].idxOf index)
    else .value none := by decide

/-- A method whose homes do not ascend; a fact would otherwise depend on their order. -/
def unordered : Method :=
  { code := [.ret], locals := [], parameterHomes := [(1, .word32), (0, .word32)],
    returnsValue := false, declared := { parameters := [.atom runtimeScope "System.Int32",
      .atom runtimeScope "System.Int32"] } }

/-- The return fact the facts command also reads. -/
theorem unordered_returnsValue : unordered.returnsValue = false := rfl
#print axioms unordered_returnsValue

/-- The declared signature the facts command also reads. -/
theorem unordered_declared : unordered.declared = { parameters :=
    [.atom runtimeScope "System.Int32", .atom runtimeScope "System.Int32"] } := rfl
#print axioms unordered_declared

/--
error: cil_resolution_facts: the parameter homes of Tests.ResolutionFacts.unordered
do not ascend
-/
#guard_msgs (whitespace := lax) in
cil_resolution_facts unordered

-- The simplifier reads a literal body's argument access without generated facts.
example : twoParameters.argumentAccess 0 = .value (some .unsigned8) := by simp only [cil_step]
example : wide.argumentAccess 39 = .home 7 := by simp only [cil_step]

/-- A method whose homes are not known. -/
def symbolicHomes (homes : List (Nat × LocalKind)) : Method :=
  { code := [], locals := [], parameterHomes := homes, returnsValue := false,
    declared := twoParameterSignature }

example : (symbolicHomes []).argumentAccess 1 = .value none := by simp only [cil_step]

-- A symbolic home list leaves the access for a caller's fact.
example (homes : List (Nat × LocalKind)) (access : ArgumentAccess)
    (known : (symbolicHomes homes).argumentAccess 0 = access) :
    (symbolicHomes homes).argumentAccess 0 = access := by
  fail_if_success simp only [cil_step]
  exact known

/-- Two methods that differ only in their locals' initial values read arguments alike. -/
example : ({ twoParameters with locals := [.i32 7] } : Method).argumentAccess =
    twoParameters.argumentAccess := Method.argumentAccess_congr rfl rfl rfl rfl

/-- The raw view of `twoParameters`: a byte and an int argument, one int local, and a body that
    stores to the int argument and loads the byte. -/
def twoParametersRaw : RawArguments :=
  { arguments := [.field .unsigned8, .field .signed32], locals := [.field .signed32],
    code := [.other, .store 1, .load 0, .other] }

/-- The argument check accepts `twoParameters` against its raw view. -/
theorem twoParameters_homesValid :
    ParameterHomesValid #[] twoParametersRaw [true, true, true, true] twoParameters := by decide
#print axioms twoParameters_homesValid

-- The home slot the check expects is the slot `argumentAccess` reads.
example : twoParameters.argumentAccess 1 = .home (1 + 0) :=
  argumentAccess_of_homed twoParameters_homesValid (by decide)

/-- A static method without parameters. A fact for argument 0 would state a read the method
    never makes, so the facts command declares none. -/
def noParameters : Method :=
  { code := [.ret], locals := [], returnsValue := false, declared := {} }

/-- The return fact the facts command also reads. -/
theorem noParameters_returnsValue : noParameters.returnsValue = false := rfl
#print axioms noParameters_returnsValue

/-- The declared signature the facts command also reads. -/
theorem noParameters_declared : noParameters.declared = {} := rfl
#print axioms noParameters_declared

cil_resolution_facts noParameters

/-- error: Unknown identifier `noParameters_argumentAccess0` -/
#guard_msgs in #check noParameters_argumentAccess0
/-- error: Unknown identifier `noParameters_parameterSuffix0` -/
#guard_msgs in #check noParameters_parameterSuffix0

-- One fact per declared argument and no more: argument 1 is the last of `twoParameters`.
/-- error: Unknown identifier `twoParameters_argumentAccess2` -/
#guard_msgs in #check twoParameters_argumentAccess2

/-- A home keyed past the one declared parameter, which the argument check would refuse. The
    facts cover the declared argument alone, so a stray home cannot add a fact for an argument
    the signature does not have. -/
def strayHome : Method :=
  { code := [.ret], locals := [], parameterHomes := [(3, .word32)], returnsValue := false,
    declared := { parameters := [.atom runtimeScope "System.Int16"] } }

/-- The return fact the facts command also reads. -/
theorem strayHome_returnsValue : strayHome.returnsValue = false := rfl
#print axioms strayHome_returnsValue

/-- The declared signature the facts command also reads. -/
theorem strayHome_declared : strayHome.declared =
    { parameters := [.atom runtimeScope "System.Int16"] } := rfl
#print axioms strayHome_declared

cil_resolution_facts strayHome

example : strayHome.argumentAccess 0 = .value (some .signed16) := strayHome_argumentAccess0
/-- error: Unknown identifier `strayHome_argumentAccess3` -/
#guard_msgs in #check strayHome_argumentAccess3

/-- Two homes for one argument. A fact would pick one of the two slots by search order, so the
    facts command refuses the method as it refuses descending homes. -/
def duplicateHomes : Method :=
  { code := [.ret], locals := [], parameterHomes := [(0, .word32), (0, .word32)],
    returnsValue := false, declared := { parameters := [.atom runtimeScope "System.Int32"] } }

/-- The return fact the facts command also reads. -/
theorem duplicateHomes_returnsValue : duplicateHomes.returnsValue = false := rfl
#print axioms duplicateHomes_returnsValue

/-- The declared signature the facts command also reads. -/
theorem duplicateHomes_declared : duplicateHomes.declared =
    { parameters := [.atom runtimeScope "System.Int32"] } := rfl
#print axioms duplicateHomes_declared

/--
error: cil_resolution_facts: the parameter homes of Tests.ResolutionFacts.duplicateHomes
do not ascend
-/
#guard_msgs (whitespace := lax) in
cil_resolution_facts duplicateHomes

/-- An array and a pointer parameter. Neither type is a narrowing candidate, so their facts
    read each argument as it arrives without consulting the layouts. -/
def referenceParameters : Method :=
  { code := [.ret], locals := [], returnsValue := false,
    declared := { parameters := [.array (.atom runtimeScope "System.Byte"),
      .pointer (.atom runtimeScope "System.Int16")] } }

/-- The return fact the facts command also reads. -/
theorem referenceParameters_returnsValue : referenceParameters.returnsValue = false := rfl
#print axioms referenceParameters_returnsValue

/-- The declared signature the facts command also reads. -/
theorem referenceParameters_declared : referenceParameters.declared =
    { parameters := [.array (.atom runtimeScope "System.Byte"),
      .pointer (.atom runtimeScope "System.Int16")] } := rfl
#print axioms referenceParameters_declared

cil_resolution_facts referenceParameters

example : referenceParameters.argumentAccess 0 = .value none :=
  referenceParameters_argumentAccess0
example : referenceParameters.argumentAccess 1 = .value none :=
  referenceParameters_argumentAccess1

/-- A symbolic argument index leaves the access for a caller's fact: the simproc decides only
    literal indices, so it cannot rewrite one argument's access into another's. -/
example (index : Nat) (access : ArgumentAccess)
    (known : twoParameters.argumentAccess index = access) :
    twoParameters.argumentAccess index = access := by
  fail_if_success simp only [cil_step]
  exact known

/-- Twenty parameters and seventeen homes, so the home suffix crosses a 16-entry block. The
    facts past the boundary must read the second home block, not the first. -/
def manyHomes : Method :=
  { code := [.ret], locals := [.i32 0], localKinds := [.word32], returnsValue := false,
    parameterHomes := (List.range 17).map (·, .word32),
    declared := { parameters := List.replicate 20 (.atom runtimeScope "System.Int32") } }

/-- The return fact the facts command also reads. -/
theorem manyHomes_returnsValue : manyHomes.returnsValue = false := rfl
#print axioms manyHomes_returnsValue

/-- The declared signature the facts command also reads. -/
theorem manyHomes_declared : manyHomes.declared =
    { parameters := List.replicate 20 (.atom runtimeScope "System.Int32") } := rfl
#print axioms manyHomes_declared

cil_resolution_facts manyHomes

example : manyHomes.argumentAccess 15 = .home 16 := manyHomes_argumentAccess15
example : manyHomes.argumentAccess 16 = .home 17 := manyHomes_argumentAccess16
example : manyHomes.argumentAccess 17 = .value none := manyHomes_argumentAccess17
example : manyHomes.argumentAccess 19 = .value none := manyHomes_argumentAccess19
example : manyHomes_homeSuffix16 = [(16, .word32)] := rfl

/-! ## Array element shapes -/

/-- The `int32` type as the extractor writes it. -/
def int32Type : TypeExpr := .atom runtimeScope "System.Int32"

/-- A function pointer type of the managed convention taking and returning an `int32`. -/
def unaryPointer : TypeExpr :=
  .functionPointer int32Type (.signatureParameter int32Type .void) 0 false false

-- A primitive array holds the primitive's storage and a floating-point array has no shape,
-- whatever the method's layouts, without evaluating the type name.
example (body : Method) : body.elementShape int32Type = .value .signed32 :=
  Method.elementShape_primitive body .int32
example (body : Method) : body.elementShape (.atom runtimeScope "System.Double") =
    .unsupported ElementShape.unsupportedType :=
  Method.elementShape_primitive body .double

-- An enum array holds the enum's storage over its underlying integer type, and an enum over a
-- type no enum may have as its underlying type has no shape.
example (body : Method) :
    body.elementShape (.enum "Examples.Small" (.atom runtimeScope "System.Int16")) =
      .value (.enumeration "Examples.Small" .signed16) :=
  Method.elementShape_enum body _ .int16
example (body : Method) :
    body.elementShape (.enum "Examples.Truth" (.atom runtimeScope "System.Boolean")) =
      .unsupported ElementShape.unsupportedType :=
  Method.elementShape_enum body _ .boolean

-- A class array holds references.
example (body : Method) :
    body.elementShape (.object "Examples" "Examples.Box") =
      .reference (.object "Examples" "Examples.Box") :=
  Method.elementShape_object body _ _

-- A function-pointer array holds method-table entries of the pointer's managed signature.
example (body : Method) : body.elementShape unaryPointer = .method ⟨int32Type, [int32Type]⟩ :=
  rfl

/-- A by-ref-like struct, which no heap array holds. -/
def spanLikeLayout : RawLayout :=
  { identity := "Examples.SpanLike", explicit := false, packing := 0, declaredSize := 0,
    byRefLike := true, fields := [{ type := .signed64 }] }

/-- The checked layout of `pointLayout`: two bytes. -/
def pointComputed : ComputedLayout :=
  { layout := { size := 2, fields := [{ offset := 0, width := 1 }, { offset := 1, width := 1 }] },
    alignment := 1 }

/-- The checked layout of `spanLikeLayout`: eight bytes. -/
def spanLikeComputed : ComputedLayout :=
  { layout := { size := 8, fields := [{ offset := 0, width := 8 }] }, alignment := 8 }

/-- The layouts every array method below shares. -/
def arraysEnvironment : LayoutEnvironment :=
  { rawLayouts := [pointLayout, spanLikeLayout], layouts := #[pointComputed, spanLikeComputed] }

/-- A method whose arrays hold the element types `arraysClosed` names. -/
def arrays : Method :=
  { code := [.ret], locals := [], returnsValue := false, environment := arraysEnvironment }

-- A struct array holds values of the size the checked layout gives, which the same struct in
-- a table of another size changes.
example : arrays.elementShape (.aggregate "Examples.Point" 0) =
    .value (.aggregate "Examples.Point" 2) :=
  Method.elementShape_aggregate (metadata := pointLayout) (layout := pointComputed) rfl rfl rfl rfl
example : ({ arrays with environment := { arraysEnvironment with
      layouts := #[{ pointComputed with layout := { pointComputed.layout with size := 6 } }] } }
      : Method).elementShape (.aggregate "Examples.Point" 0) =
    .value (.aggregate "Examples.Point" 6) :=
  Method.elementShape_aggregate (metadata := pointLayout)
    (layout := { pointComputed with layout := { pointComputed.layout with size := 6 } })
    rfl rfl rfl rfl

-- A by-ref-like struct array has no shape, even with a checked layout.
example : arrays.elementShape (.aggregate "Examples.SpanLike" 1) =
    .unsupported ElementShape.byRefLikeElement :=
  Method.elementShape_byRefLike (metadata := spanLikeLayout) rfl rfl rfl

/-- The raw view of `arrays`: one instruction per element opcode, a repeated element type and a
    type operand of an opcode that names no element type. -/
def arraysClosed : RawMethod :=
  { token := 1, owner := "Examples", hasThis := false, explicitThis := false,
    callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
    parameters := [], locals := [], initLocals := true, maxStack := 3, genericParameters := [],
    code := [⟨0, 141, .type int32Type⟩, ⟨5, 163, .type int32Type⟩,
      ⟨10, 163, .type (.enum "Examples.Small" (.atom runtimeScope "System.Int16"))⟩,
      ⟨15, 164, .type (.aggregate "Examples.Point" 0)⟩,
      ⟨20, 143, .type (.aggregate "Examples.SpanLike" 1)⟩,
      ⟨25, 141, .type (.object "Examples" "Examples.Box")⟩,
      ⟨30, 140, .type (.atom runtimeScope "System.Int64")⟩,
      ⟨35, 163, .type unaryPointer⟩, ⟨40, 42, .none⟩] }

/-- The return fact the facts command also reads. -/
theorem arrays_returnsValue : arrays.returnsValue = false := rfl
#print axioms arrays_returnsValue

/-- The declared signature the facts command also reads. -/
theorem arrays_declared : arrays.declared = {} := rfl
#print axioms arrays_declared

cil_resolution_facts arrays

example : arrays.elementShape int32Type = .value .signed32 := arrays_elementShape0
example : arrays.elementShape (.enum "Examples.Small" (.atom runtimeScope "System.Int16")) =
    .value (.enumeration "Examples.Small" .signed16) := arrays_elementShape1
example : arrays.elementShape (.aggregate "Examples.Point" 0) =
    .value (.aggregate "Examples.Point" 2) := arrays_elementShape2
example : arrays.elementShape (.aggregate "Examples.SpanLike" 1) =
    .unsupported ElementShape.byRefLikeElement := arrays_elementShape3
example : arrays.elementShape (.object "Examples" "Examples.Box") =
    .reference (.object "Examples" "Examples.Box") := arrays_elementShape4
example : arrays.elementShape unaryPointer = .method ⟨int32Type, [int32Type]⟩ :=
  arrays_elementShape5
example : arrays.elementShape (.aggregate "Examples.Point" 0) =
    .value (.aggregate "Examples.Point" 2) := by simp only [cil_code]

/-- info: 'Tests.ResolutionFacts.arrays_elementShape0' depends on axioms: [propext] -/
#guard_msgs in #print axioms arrays_elementShape0
/-- info: 'Tests.ResolutionFacts.arrays_elementShape1' depends on axioms: [propext] -/
#guard_msgs in #print axioms arrays_elementShape1
/-- info: 'Tests.ResolutionFacts.arrays_elementShape2' depends on axioms: [propext] -/
#guard_msgs in #print axioms arrays_elementShape2
/-- info: 'Tests.ResolutionFacts.arrays_elementShape3' depends on axioms: [propext] -/
#guard_msgs in #print axioms arrays_elementShape3
/-- info: 'Tests.ResolutionFacts.arrays_elementShape4' depends on axioms: [propext] -/
#guard_msgs in #print axioms arrays_elementShape4
/-- info: 'Tests.ResolutionFacts.arrays_elementShape5' depends on axioms: [propext] -/
#guard_msgs in #print axioms arrays_elementShape5

-- One fact per distinct element type, not per instruction: `int32` is named twice, and the
-- `int64` operand of an opcode that names no element type has no fact.
/-- error: Unknown identifier `arrays_elementShape6` -/
#guard_msgs in #check arrays_elementShape6

-- The layout suffixes belong to the shared environment constant, so a second method of the same
-- environment reads them instead of declaring its own.
example : arraysEnvironment_rawLayoutSuffix0 = [pointLayout, spanLikeLayout] := rfl

/-- A second method of the shared layouts, named as the extractor names them. -/
def moreArrays : Method :=
  { code := [.nop, .ret], locals := [], returnsValue := false, environment := arraysEnvironment }

/-- The raw view of `moreArrays`: one struct element. -/
def moreArraysClosed : RawMethod :=
  { arraysClosed with code := [⟨0, 164, .type (.aggregate "Examples.Point" 0)⟩] }

/-- The return fact the facts command also reads. -/
theorem moreArrays_returnsValue : moreArrays.returnsValue = false := rfl
#print axioms moreArrays_returnsValue

/-- The declared signature the facts command also reads. -/
theorem moreArrays_declared : moreArrays.declared = {} := rfl
#print axioms moreArrays_declared

cil_resolution_facts moreArrays

example : moreArrays.elementShape (.aggregate "Examples.Point" 0) =
    .value (.aggregate "Examples.Point" 2) := moreArrays_elementShape0
/-- error: Unknown identifier `moreArrays_rawLayoutSuffix0` -/
#guard_msgs in #check moreArrays_rawLayoutSuffix0

/-- Eighteen one-field structs, so the layout suffixes cross a 16-entry block. -/
def manyLayoutsEnvironment : LayoutEnvironment :=
  { rawLayouts := (List.range 18).map fun index =>
      { identity := s!"Examples.Cell{index}", explicit := false, packing := 0,
        declaredSize := 0, fields := [{ type := .signed32 }] }
    layouts := ((List.range 18).map fun index =>
      { layout := { size := 4 * (index + 1), fields := [] }, alignment := 4 }).toArray }

/-- A method whose arrays hold the structs on both sides of the block boundary. -/
def manyLayouts : Method :=
  { code := [.ret], locals := [], returnsValue := false, environment := manyLayoutsEnvironment }

/-- The raw view of `manyLayouts`. -/
def manyLayoutsClosed : RawMethod :=
  { arraysClosed with code := [⟨0, 141, .type (.aggregate "Examples.Cell15" 15)⟩,
      ⟨5, 141, .type (.aggregate "Examples.Cell17" 17)⟩] }

/-- The return fact the facts command also reads. -/
theorem manyLayouts_returnsValue : manyLayouts.returnsValue = false := rfl
#print axioms manyLayouts_returnsValue

/-- The declared signature the facts command also reads. -/
theorem manyLayouts_declared : manyLayouts.declared = {} := rfl
#print axioms manyLayouts_declared

cil_resolution_facts manyLayouts

example : manyLayouts.elementShape (.aggregate "Examples.Cell15" 15) =
    .value (.aggregate "Examples.Cell15" 64) := manyLayouts_elementShape0
example : manyLayouts.elementShape (.aggregate "Examples.Cell17" 17) =
    .value (.aggregate "Examples.Cell17" 72) := manyLayouts_elementShape1

/-- A method of the shared layouts without a raw view, so it has no generated shape facts. -/
def literalArrays : Method := { arrays with code := [] }

-- The simplifier reads a literal body's element shapes without generated facts.
example : literalArrays.elementShape (.aggregate "Examples.Point" 0) =
    .value (.aggregate "Examples.Point" 2) := by simp only [cil_step]
example : literalArrays.elementShape (.aggregate "Examples.SpanLike" 1) =
    .unsupported ElementShape.byRefLikeElement := by simp only [cil_step]
example : literalArrays.elementShape int32Type = .value .signed32 := by simp only [cil_step]
example : literalArrays.elementShape unaryPointer =
    .method ⟨.atom runtimeScope "System.Int32", [.atom runtimeScope "System.Int32"]⟩ := by
  simp only [cil_step]
example : literalArrays.elementShape
    (.apply (.constructor intrinsicsScope "System.Runtime.Intrinsics.Vector128`1") int32Type) =
      .value (.vector "System.Runtime.Intrinsics.Vector128`1<System.Int32>" 16) := by
  simp only [cil_step]

-- A struct index the layouts do not hold, or an identity other than the one held there, has
-- no shape.
example : literalArrays.elementShape (.aggregate "Examples.Point" 5) =
    .unsupported ElementShape.outsideLayouts := by simp only [cil_step]
example : literalArrays.elementShape (.aggregate "Examples.Other" 0) =
    .unsupported ElementShape.outsideLayouts := by simp only [cil_step]

/-- A method whose raw layouts hold `pointLayout` without a checked layout for it. -/
def uncomputedArrays : Method :=
  { code := [.ret], locals := [], returnsValue := false,
    environment := { rawLayouts := [pointLayout], layouts := #[] } }

-- A struct the raw layouts hold under its identity, but that has no checked layout, has no shape.
example : uncomputedArrays.elementShape (.aggregate "Examples.Point" 0) =
    .unsupported ElementShape.outsideLayouts := by simp only [cil_step]

/-- A managed function pointer taking a struct at a layout index that no raw layout holds. -/
def unboundPointer : TypeExpr :=
  .functionPointer .void (.signatureParameter (.aggregate "Examples.Missing" 7) .void) 0 false false

-- A function pointer whose struct parameter no layout binds has no shape, as it has no storage.
example : literalArrays.elementShape unboundPointer =
    .unsupported ElementShape.outsideLayouts := by simp only [cil_step]

/-- A method over layouts that are not known. -/
def symbolicLayouts (environment : LayoutEnvironment) : Method :=
  { code := [], locals := [], returnsValue := false, environment }

-- A symbolic element type or layout table leaves the shape for a caller's fact.
example (type : TypeExpr) (shape : ElementShape)
    (known : literalArrays.elementShape type = shape) :
    literalArrays.elementShape type = shape := by
  fail_if_success simp only [cil_step]
  exact known
example (environment : LayoutEnvironment) (shape : ElementShape)
    (known : (symbolicLayouts environment).elementShape (.aggregate "Examples.Point" 0) = shape) :
    (symbolicLayouts environment).elementShape (.aggregate "Examples.Point" 0) = shape := by
  fail_if_success simp only [cil_step]
  exact known

end Tests.ResolutionFacts
