import CIL.Extraction.Dispatch

/-! Standalone dispatch scaling comparison, including catalog construction. -/

namespace DispatchScaling
open CIL CIL.Extraction
set_option maxRecDepth 65536
set_option maxHeartbeats 0
/-- One interface shared by every concrete type. -/
def iface : TypeExpr := .atom "Fixture" "IValue"
/-- Distinct aggregate identities within one assembly. -/
def receiver (index : Nat) : TypeExpr := .aggregate ("Fixture::T" ++ toString index) index
/-- Abstract interface method with a simple void signature. -/
def slot : DispatchMethod := {
  token := 5, name := "Read", hasThis := true, isPublic := true, isAbstract := true,
  isVirtual := true, hasBody := false, genericArity := 0, explicitThis := false,
  callingConvention := 0, attributes := 0, implementation := 0,
  returnType := .void, parameters := [], overrides := [] }
/-- A value type with one implicit implementation. -/
def concrete (index : Nat) : DispatchType := {
  identity := receiver index, valueType := true, interfaceType := false,
  interfaces := [iface], methods := [{slot with
    token := index + 21, isAbstract := false, hasBody := true}] }
/-- The complete dispatch catalog, including the interface declaration. -/
def types (count : Nat) : List DispatchType :=
  (List.range count).map concrete ++ [{
    identity := iface, valueType := false, interfaceType := true,
    interfaces := [], methods := [slot]}]
/-- Call site selecting the shared interface slot. -/
def site : CallSite := {
  declaringType := iface, name := "Read", target := .managed 5,
  typeArguments := [], parameterCount := 0, hasThis := true, returnsValue := false,
  returnType := .void, parameterTypes := [] }
/-- Resolve one call per concrete type using the list specification. -/
def baseline (count : Nat) : Bool :=
  let catalog := types count
  (List.range count).all fun index =>
    (resolveConstrained catalog (receiver index) site).map (·.token) == some (index + 21)
/-- Resolve the same calls, including building the shared index. -/
def indexed (count : Nat) : Bool :=
  let catalog := DispatchIndex.ofTypes (types count)
  (List.range count).all fun index =>
    (catalog.resolve (receiver index) site).map (·.token) == some (index + 21)
/-- Every list resolution selects the expected implementation token. -/
theorem baseline32 : baseline 32 = true := by decide +kernel
#print axioms baseline32
/-- Every indexed resolution selects the expected implementation token. -/
theorem indexed32 : indexed 32 = true := by decide +kernel
#print axioms indexed32

/-- Every list resolution selects the expected implementation token. -/
theorem baseline16 : baseline 16 = true := by decide +kernel
#print axioms baseline16
/-- Every indexed resolution selects the expected implementation token. -/
theorem indexed16 : indexed 16 = true := by decide +kernel
#print axioms indexed16

/-- Every list resolution selects the expected implementation token. -/
theorem baseline64 : baseline 64 = true := by decide +kernel
#print axioms baseline64
/-- Every indexed resolution selects the expected implementation token. -/
theorem indexed64 : indexed 64 = true := by decide +kernel
#print axioms indexed64

end DispatchScaling
