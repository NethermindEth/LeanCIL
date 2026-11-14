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
-/

namespace Tests.ResolutionFacts

open CIL CIL.Extraction

-- A primitive below 32 bits narrows to its own width and signedness.
example : declaredNarrow [] (.atom runtimeScope "System.SByte") = some .signed8 :=
  declaredNarrow_primitive [] .sbyte
example : declaredNarrow [] (.atom runtimeScope "System.Byte") = some .unsigned8 :=
  declaredNarrow_primitive [] .byte
example : declaredNarrow [] (.atom runtimeScope "System.Boolean") = some .unsigned8 :=
  declaredNarrow_primitive [] .boolean
example : declaredNarrow [] (.atom runtimeScope "System.Int16") = some .signed16 :=
  declaredNarrow_primitive [] .int16
example : declaredNarrow [] (.atom runtimeScope "System.Char") = some .unsigned16 :=
  declaredNarrow_primitive [] .char

-- A primitive of 32 bits or more, or a floating-point one, is returned as it is.
example : declaredNarrow [] (.atom runtimeScope "System.Int32") = none :=
  declaredNarrow_primitive [] .int32
example : declaredNarrow [] (.atom runtimeScope "System.UIntPtr") = none :=
  declaredNarrow_primitive [] .uintPtr
example : declaredNarrow [] (.atom runtimeScope "System.Double") = none :=
  declaredNarrow_primitive [] .double

-- An enum narrows as its underlying integer type.
example : declaredNarrow [] (.enum "Examples.Small" (.atom runtimeScope "System.Int16")) =
    some .signed16 :=
  (declaredNarrow_enum [] "Examples.Small" .int16).trans rfl
example : declaredNarrow [] (.enum "Examples.Flags" (.atom runtimeScope "System.Byte")) =
    some .unsigned8 :=
  (declaredNarrow_enum [] "Examples.Flags" .byte).trans rfl

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

end Tests.ResolutionFacts
