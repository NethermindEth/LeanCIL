import CIL.Extraction.FlowIndex

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

end Tests.FlowIndex
