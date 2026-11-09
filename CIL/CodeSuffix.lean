import CIL.Instructions

/-!
# Code suffixes

The extractor states `method{n}.code[pc]? = some op` for every pc of an extracted method.
Checking such an equation by `rfl` walks `pc` cells of the code list, so the equations of one
method would cost time quadratic in its length. The extractor instead names the suffix of the
code at each block boundary, proves each named suffix from the one before it with `advance`,
and proves each instruction from the suffix that starts its block with `lookup`. No proof
then walks more than one block, and the equations cost time linear in the method's length.
-/

namespace CIL.CodeSuffix

variable {code suffix next : List Op} {start : Nat}

/-- Dropping `count` more instructions from the suffix at `start` leaves the suffix at
    `start + count`. -/
theorem advance (count : Nat) (placed : code.drop start = suffix)
    (rest : suffix.drop count = next) : code.drop (start + count) = next := by
  rw [← rest, ← placed, List.drop_drop]

/-- info: 'CIL.CodeSuffix.advance' depends on axioms: [propext] -/
#guard_msgs in #print axioms advance

/-- The instruction at `index` of the suffix at `start` is the code's instruction at
    `start + index`. -/
theorem lookup {op : Op} (index : Nat) (placed : code.drop start = suffix)
    (found : suffix[index]? = some op) : code[start + index]? = some op := by
  rw [← placed, List.getElem?_drop] at found
  exact found

/-- info: 'CIL.CodeSuffix.lookup' depends on axioms: [propext] -/
#guard_msgs in #print axioms lookup

end CIL.CodeSuffix
