import CIL.Resolution

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
  { code := [.ldc_i4 7, .ret (some .unsigned8)], locals := [], returnsValue := true,
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
  { code := [.ldc_i4 7, .ret (some .signed16)], locals := [], returnsValue := true,
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

/--
info: 'Tests.ResolutionFacts.pointReturn_returnNarrow' depends on axioms: [propext, Quot.sound]
-/
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

/--
info: 'CIL.Extraction.declaredNarrow_of_not_candidate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms declaredNarrow_of_not_candidate

end Tests.ResolutionFacts
