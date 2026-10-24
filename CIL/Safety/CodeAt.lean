import CIL.Instructions

/-!
# Code placement

`CodeAt body start segment` states that `segment` occupies `body.code` from position `start`,
so the instruction at `start + index` is `segment[index]`. It replaces the positional
hypotheses `body.code = leading ++ segment ++ tail` and `leading.length = start` that segment
theorems would otherwise thread: it is decidable, so a concrete placement closes by
`decide +kernel`, and `CodeAt.lookup` turns it into the `body.code[pc]? = some op` facts that
the stepping tactics consume. Placements split and compose along `++`, `drop` and `take`.
-/

namespace CIL.Safety

/-- `segment` occupies `body.code` from position `start`: the instructions at `start`,
    `start + 1`, ... are exactly those of `segment`, in order. -/
def CodeAt (body : CIL.Method) (start : Nat) (segment : List CIL.Op) : Prop :=
  (body.code.drop start).take segment.length = segment

/-- A concrete placement is decided by `decide +kernel`; the kernel unfolds the instruction
    equality that elaboration keeps irreducible. -/
instance (body : CIL.Method) (start : Nat) (segment : List CIL.Op) :
    Decidable (CodeAt body start segment) :=
  inferInstanceAs (Decidable (_ = _))

namespace CodeAt

variable {body : CIL.Method} {start : Nat} {segment : List CIL.Op}

/-- A placement is exactly agreement of `body.code` with `segment` at each position of the
    segment, shifted by `start`. -/
theorem iff_lookup : CodeAt body start segment ↔
    ∀ index, index < segment.length → body.code[start + index]? = segment[index]? := by
  unfold CodeAt
  constructor
  · intro placed index bound
    rw [← placed, List.getElem?_take, ite_eq_left (by simpa [placed] using bound),
      List.getElem?_drop]
  · intro agrees
    apply List.ext_getElem?
    intro index
    rw [List.getElem?_take, List.getElem?_drop]
    split
    · exact agrees index ‹_›
    · exact (List.getElem?_eq_none (by omega)).symm

#print axioms iff_lookup

/-- The instruction at each position of a placed segment is the segment's instruction there. -/
theorem lookup {index : Nat} {op : CIL.Op} (placed : CodeAt body start segment)
    (found : segment[index]? = some op) : body.code[start + index]? = some op := by
  rw [iff_lookup.mp placed index (List.getElem?_eq_some_iff.mp found).1, found]

#print axioms lookup

/-- The positional form a placement replaces: `segment` follows `start` instructions. -/
theorem of_eq_append {leading tail : List CIL.Op}
    (placed : body.code = leading ++ segment ++ tail) (offset : leading.length = start) :
    CodeAt body start segment := by
  unfold CodeAt
  rw [placed, ← offset, List.append_assoc, List.drop_left, List.take_left]

#print axioms of_eq_append

/-- A placement inside the code recovers the positional form, for theorems still stated over it.
    The bound matters only for the empty segment, which `nil` places anywhere. -/
theorem exists_eq_append (placed : CodeAt body start segment)
    (inBounds : start ≤ body.code.length) :
    ∃ leading tail, body.code = leading ++ segment ++ tail ∧ leading.length = start := by
  refine ⟨body.code.take start, body.code.drop (start + segment.length), ?_, ?_⟩
  · unfold CodeAt at placed
    conv => lhs; rw [← List.take_append_drop start body.code,
      ← List.take_append_drop segment.length (body.code.drop start)]
    rw [placed, List.drop_drop, List.append_assoc]
  · simp only [List.length_take]
    omega

#print axioms exists_eq_append

/-- The empty segment is placed anywhere. -/
theorem nil : CodeAt body start [] := by
  simp [CodeAt]

#print axioms nil

/-- A segment is placed at `start` exactly when its two parts are placed one after the other. -/
theorem append_iff {left right : List CIL.Op} :
    CodeAt body start (left ++ right) ↔
      CodeAt body start left ∧ CodeAt body (start + left.length) right := by
  simp only [iff_lookup, List.length_append]
  constructor
  · intro agrees
    refine ⟨fun index bound => ?_, fun index bound => ?_⟩
    · rw [agrees index (by omega), List.getElem?_append_left bound]
    · rw [Nat.add_assoc, agrees (left.length + index) (by omega),
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  · intro ⟨first, second⟩ index bound
    by_cases inLeft : index < left.length
    · rw [first index inLeft, List.getElem?_append_left inLeft]
    · have shifted := second (index - left.length) (by omega)
      rw [Nat.add_assoc, Nat.add_sub_cancel' (by omega)] at shifted
      rw [shifted, List.getElem?_append_right (by omega)]

#print axioms append_iff

/-- The first part of a placed segment is placed at the same start. -/
theorem append_left {left right : List CIL.Op} (placed : CodeAt body start (left ++ right)) :
    CodeAt body start left :=
  (append_iff.mp placed).1

#print axioms append_left

/-- The second part of a placed segment is placed after the first part. -/
theorem append_right {left right : List CIL.Op} (placed : CodeAt body start (left ++ right)) :
    CodeAt body (start + left.length) right :=
  (append_iff.mp placed).2

#print axioms append_right

/-- Adjacent placed segments compose into one placed segment. -/
theorem append {left right : List CIL.Op} (first : CodeAt body start left)
    (second : CodeAt body (start + left.length) right) : CodeAt body start (left ++ right) :=
  append_iff.mpr ⟨first, second⟩

#print axioms append

/-- A placed segment's first instruction is at `start` and the rest follows it. -/
theorem cons_iff {op : CIL.Op} {rest : List CIL.Op} :
    CodeAt body start (op :: rest) ↔
      body.code[start]? = some op ∧ CodeAt body (start + 1) rest := by
  rw [← List.singleton_append, append_iff, iff_lookup (segment := [op])]
  simp

#print axioms cons_iff

/-- The part of a placed segment after its first `count` instructions is placed `count` later. -/
theorem drop (placed : CodeAt body start segment) (count : Nat) :
    CodeAt body (start + count) (segment.drop count) := by
  by_cases short : count ≤ segment.length
  · have split := List.take_append_drop count segment
    rw [← split] at placed
    simpa [List.length_take, Nat.min_eq_left short] using append_right placed
  · rw [List.drop_eq_nil_of_le (by omega)]
    exact nil

#print axioms drop

/-- The first `count` instructions of a placed segment are placed at the same start. -/
theorem take (placed : CodeAt body start segment) (count : Nat) :
    CodeAt body start (segment.take count) := by
  rw [← List.take_append_drop count segment] at placed
  exact append_left placed

#print axioms take

/-- A segment inside a placed segment is placed after the instructions that precede it. -/
theorem middle {before middle after : List CIL.Op}
    (placed : CodeAt body start (before ++ middle ++ after)) :
    CodeAt body (start + before.length) middle :=
  append_left (append_right (List.append_assoc _ _ _ ▸ placed))

#print axioms middle

end CodeAt

end CIL.Safety
