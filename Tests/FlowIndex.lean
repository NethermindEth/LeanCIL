import CIL.Extraction.FlowIndex
import CIL.Extraction.KernelEquation

/-!
# Consuming certificate index regressions

The index must retain holes, odd-sized partitions and bounds, and leave an unconsumed suffix
untouched when constructed for only a prefix.
-/

namespace Tests.FlowIndex
open CIL.Extraction

/-- Empty and singleton indexes retain exact optional lookup, including out-of-bounds cases. -/
theorem endpoints :
    (FlowIndex.ofList ([] : List Nat)).get? 0 = none ∧
    (FlowIndex.ofList [7]).get? 0 = some 7 ∧
    (FlowIndex.ofList [7]).get? 1 = none := by decide +kernel
#print axioms endpoints

/-- An odd certificate retains missing states without shifting later states. -/
theorem holes :
    (List.range 6).map (FlowIndex.ofList [some 3, none, some 5, none, some 7]).get? =
      [some (some 3), some none, some (some 5), some none, some (some 7), none] := by
  decide +kernel
#print axioms holes

/-- Prefix construction returns the exact suffix and excludes it from the built index. -/
theorem prefix_consumed :
    (FlowIndex.build 3 3 [10, 11, 12, 13, 14]).2 = [13, 14] ∧
    (List.range 4).map (FlowIndex.build 3 3 [10, 11, 12, 13, 14]).1.get? =
      [some 10, some 11, some 12, none] := by decide +kernel
#print axioms prefix_consumed

/-- Both sides of balanced even partitions preserve position and reject the endpoint. -/
theorem partitions :
    (List.range 9).map (FlowIndex.ofList [10, 11, 12, 13, 14, 15, 16, 17]).get? =
      [some 10, some 11, some 12, some 13, some 14, some 15, some 16, some 17, none] := by
  decide +kernel
#print axioms partitions

/-- A named cell, which `program_index%` writes into its leaf as written. -/
def cell : Nat := 7

open Lean Elab Term Command in
run_cmd liftTermElabM do
  let tree ← elabTerm (← `(program_index% [cell])) none
  let_expr FlowIndex.leaf _ value := tree | throwError "Expected a singleton leaf"
  unless value.isConstOf ``cell do throwError "Expected the named cell, found {value}"

/-- The kernel rejects index agreement with a duplicated or missing leaf, and a false length. -/
example : True := by
  fail_if_success
    have : (program_index% [10, 20, 20]) = FlowIndex.ofList [10, 20, 30] := by cil_kernel_rfl
  fail_if_success
    have : (program_index% [10, 20]) = FlowIndex.ofList [10, 20, 30] := by cil_kernel_rfl
  fail_if_success have : 2 = [10, 20, 30].length := by cil_kernel_rfl
  trivial

/-- `program_index%` writes the index `ofList` builds, split at the same middles, for lists with
    none, one, an odd and an even number of cells. -/
theorem literal_indices :
    (program_index% ([] : List Nat)) = FlowIndex.ofList [] ∧
    (program_index% [cell]) = FlowIndex.ofList [cell] ∧
    (program_index% [10, 20, 30]) = .branch 1 (.leaf 10) (.branch 1 (.leaf 20) (.leaf 30)) ∧
    (program_index% [10, 20, 30]) = FlowIndex.ofList [10, 20, 30] ∧
    (program_index% [10, 11, 12, 13, 14, 15, 16, 17]) =
      FlowIndex.ofList [10, 11, 12, 13, 14, 15, 16, 17] := by
  decide +kernel
#print axioms literal_indices
end Tests.FlowIndex
