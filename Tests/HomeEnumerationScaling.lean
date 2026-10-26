import CIL.Extraction.Parameters

/-!
Standalone kernel-work comparison of range membership against ordered home-set enumeration.
Both dense and sparse cases include constructing the collected set.
-/
namespace HomeEnumerationScaling
open CIL CIL.Extraction
set_option maxRecDepth 65536
set_option maxHeartbeats 0
/-- A live instruction that requires an argument home. -/
def home : ArgumentOp × Bool → Option Nat
  | (.store index, true) | (.address index, true) => some index
  | _ => none
/-- Prior range-scanning reference implementation. -/
def baseline (raw : RawArguments) (reachable : List Bool) : List Nat :=
  let homes := Std.TreeSet.ofList ((raw.code.zip reachable).filterMap home)
  (List.range raw.arguments.length).filter homes.contains
/-- Eight live stores amid many declared arguments. -/
def sparse (count : Nat) : RawArguments :=
  ⟨List.replicate count (.field .unsigned64), [], (List.range 8).map ArgumentOp.store⟩
/-- Every declared argument receives a home. -/
def dense (count : Nat) : RawArguments :=
  ⟨List.replicate count (.field .unsigned64), [], (List.range count).map ArgumentOp.store⟩
/-- Fixed kernel decision workload including collection and enumeration. -/
theorem oldDense128 : baseline (dense 128) (List.replicate 128 true) = List.range 128 := by decide +kernel
#print axioms oldDense128
/-- Fixed kernel decision workload including collection and enumeration. -/
theorem newDense128 : requiredHomeIndices (dense 128) (List.replicate 128 true) = List.range 128 := by decide +kernel
#print axioms newDense128
/-- Fixed kernel decision workload including collection and enumeration. -/
theorem oldDense512 : baseline (dense 512) (List.replicate 512 true) = List.range 512 := by decide +kernel
#print axioms oldDense512
/-- Fixed kernel decision workload including collection and enumeration. -/
theorem newDense512 : requiredHomeIndices (dense 512) (List.replicate 512 true) = List.range 512 := by decide +kernel
#print axioms newDense512
/-- Fixed kernel decision workload including collection and enumeration. -/
theorem oldSparse512 : baseline (sparse 512) (List.replicate 8 true) = List.range 8 := by decide +kernel
#print axioms oldSparse512
/-- Fixed kernel decision workload including collection and enumeration. -/
theorem newSparse512 : requiredHomeIndices (sparse 512) (List.replicate 8 true) = List.range 8 := by decide +kernel
#print axioms newSparse512
/-- Fixed kernel decision workload including collection and enumeration. -/
theorem oldSparse2048 : baseline (sparse 2048) (List.replicate 8 true) = List.range 8 := by decide +kernel
#print axioms oldSparse2048
/-- Fixed kernel decision workload including collection and enumeration. -/
theorem newSparse2048 : requiredHomeIndices (sparse 2048) (List.replicate 8 true) = List.range 8 := by decide +kernel
#print axioms newSparse2048
end HomeEnumerationScaling

