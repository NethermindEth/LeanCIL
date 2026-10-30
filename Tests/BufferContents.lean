import CIL.Safety.BufferContents
import CIL.Safety.SpanContents
import CIL.Safety.ExecutionLifetime

/-! Contiguous-buffer contents over the checked memory model, checked without an extraction. -/
namespace Tests.BufferContents

open CIL.Safety

/-- A fill of any length from write authority alone yields the replicated sequence, confined to the buffer. -/
theorem fill_replicates {m : Memory} {base : Reference} {n : Nat} (v : BitVec (8 * 8))
    (writable : Writable m base 8 0 n) :
    ∃ after, writeElements m base 8 0 (List.replicate n v) = .ok after ∧
      Contents after base 8 (List.replicate n v) ∧ Confined [(base, 8 * n)] m after := by
  obtain ⟨after, written, filled, framed⟩ :=
    Filled.fill (done := []) (xs := List.replicate n v) (room := 0) (Filled.start (by simpa using writable))
  exact ⟨after, written, by simpa using filled.complete, by simpa using framed⟩

/-- An in-place transform of any length over 32-bit elements maps every element and loads back as values. -/
theorem transform_increments {m : Memory} {base : Reference} {xs : List (BitVec (8 * 4))}
    (contents : Contents m base 4 xs) (writable : Writable m base 4 0 xs.length) :
    ∃ after, transformElements m base 4 (· + 1) 0 xs.length = .ok after ∧
      Contents after base 4 (xs.map (· + 1)) ∧ Confined [(base, 4 * xs.length)] m after := by
  obtain ⟨after, ran, mapped, _, framed⟩ := contents.transform (· + 1) writable
  exact ⟨after, ran, mapped, framed⟩

/-- Each filled 64-bit element loads back as the filled word. -/
theorem fill_loads {m : Memory} {base : Reference} {n i : Nat} (v : BitVec (8 * 8))
    (writable : Writable m base 8 0 n) (bound : i < n) :
    ∃ after, writeElements m base 8 0 (List.replicate n v) = .ok after ∧
      loadValue after (.address (base.element 8 i)) 8 = .ok (.i64 v) := by
  obtain ⟨after, written, contents, _⟩ := fill_replicates v writable
  exact ⟨after, written, contents.load_word (by simp [bound])⟩

/-- The bytes just past the filled buffer and just before it are unchanged. -/
theorem fill_keeps_neighbours {m : Memory} {base : Reference} {n before width : Nat} (v : BitVec (8 * 8))
    {low high : List (BitVec 8)} (formed : m.WellFormed) (writable : Writable m base 8 0 n)
    (room : before ≤ base.offset)
    (lower : read m ⟨base.allocation, base.offset - before⟩ before 1 = .ok low)
    (upper : read m ⟨base.allocation, base.offset + 8 * n⟩ width 1 = .ok high) :
    ∃ after, writeElements m base 8 0 (List.replicate n v) = .ok after ∧
      read after ⟨base.allocation, base.offset - before⟩ before 1 = .ok low ∧
      read after ⟨base.allocation, base.offset + 8 * n⟩ width 1 = .ok high := by
  obtain ⟨after, written, _, framed⟩ := fill_replicates v writable
  refine ⟨after, written, framed.read_apart formed lower ?_, framed.read_apart formed upper ?_⟩ <;>
    simp only [List.mem_singleton, forall_eq, Apart] <;> omega

/-- Updating an element of one slice keeps a disjoint slice of the same allocation. -/
theorem update_keeps_sibling_slice {m after : Memory} {left : Reference} {start : Nat}
    {xs ys : List (BitVec (8 * 8))} {i : Nat} {x : BitVec (8 * 8)}
    (first : Contents m left 8 xs) (second : Contents m ⟨left.allocation, start⟩ 8 ys)
    (ordered : left.offset + 8 * xs.length ≤ start) (bound : i < xs.length)
    (written : write m (left.element 8 i) (numberBytes x.toNat 8) 1 = .ok after) :
    Contents after left 8 (xs.set i x) ∧ Contents after ⟨left.allocation, start⟩ 8 ys := by
  refine ⟨first.write_element written, second.after_write_apart written ?_⟩
  have := element_le (width := 8) bound
  simp only [Apart, Reference.element_allocation, Reference.element_offset, numberBytes_length]
  omega

/-- A run written at element `index` replaces exactly that run. -/
theorem run_update {m after : Memory} {base : Reference} {a b c d p q : BitVec (8 * 8)}
    (formed : m.WellFormed) (contents : Contents m base 8 [a, b, c, d])
    (written : write m (base.element 8 1) (elementBytes 8 [p, q]) 1 = .ok after) :
    Contents after base 8 [a, p, q, d] := by
  simpa using contents.write_run formed (by decide) written (index := 1) (by simp)

/-- A producer extends its prefix by one element while its room stays only writable. -/
theorem producer_extends {m after : Memory} {base : Reference} {xs : List (BitVec (8 * 8))} {room : Nat}
    {x : BitVec (8 * 8)} (filled : Filled m base 8 xs (room + 1))
    (written : write m (base.element 8 xs.length) (numberBytes x.toNat 8) 1 = .ok after) :
    Filled after base 8 (xs ++ [x]) room :=
  filled.push written

/-- An uninitialized byte inside any element refutes contents, whatever value is claimed. -/
theorem uninitialized_rejected {m : Memory} {base : Reference} {xs : List (BitVec (8 * 8))} {i j : Nat}
    (bound : i < xs.length) (byte : j < 8)
    (fresh : (m.cells base.allocation (base.offset + 8 * i + j)).initialized = false) :
    ¬ Contents m base 8 xs := by
  intro contents
  have loaded := contents i xs[i] (List.getElem?_eq_getElem bound)
  have ready := read_requires_initialization _ _ _ _ _ loaded j (List.mem_range.mpr byte)
  simp [fresh] at ready

/-- A producer cannot read its unwritten room: an uninitialized room byte refutes contents there. -/
theorem room_not_readable {m : Memory} {base : Reference} {xs : List (BitVec (8 * 8))} {room j : Nat}
    (_filled : Filled m base 8 xs (room + 1)) (byte : j < 8)
    (fresh : (m.cells base.allocation (base.offset + 8 * xs.length + j)).initialized = false)
    (y : BitVec (8 * 8)) : ¬ Contents m (base.element 8 xs.length) 8 [y] :=
  uninitialized_rejected (i := 0) (by simp) byte (by simpa using fresh)

/-- Contents past the allocation's end are refuted. -/
theorem past_end_rejected {m : Memory} {base : Reference} {xs : List (BitVec (8 * 8))} {allocation : Allocation}
    (present : m.allocations base.allocation = some allocation) (nonempty : xs ≠ [])
    (overrun : allocation.layout.size < base.offset + 8 * xs.length) : ¬ Contents m base 8 xs := by
  intro contents
  obtain ⟨found, same, _, bounds⟩ := contents.extent nonempty
  rw [present] at same
  cases same
  omega

/-- A write overlapping one byte of the buffer is not apart from it, so preservation does not apply. -/
theorem overlap_not_apart (base : Reference) :
    ¬ Apart base (8 * 2) (⟨base.allocation, base.offset + 15⟩, 8) := by
  simp [Apart]
  omega

/-- After writing a different value to an element, the old contents are refuted. -/
theorem update_refutes_old {m after : Memory} {base : Reference} {xs : List (BitVec (8 * 8))} {i : Nat}
    {x : BitVec (8 * 8)} (contents : Contents m base 8 xs) (bound : i < xs.length) (differ : xs[i] ≠ x)
    (written : write m (base.element 8 i) (numberBytes x.toNat 8) 1 = .ok after) :
    ¬ Contents after base 8 xs := by
  intro stale
  have now := (contents.write_element written) i x (by simp [bound])
  have old := stale i xs[i] (List.getElem?_eq_getElem bound)
  rw [now] at old
  have bytes := congrArg byteNumber (Except.ok.inj old)
  rw [element_value, element_value] at bytes
  exact differ (BitVec.eq_of_toNat_eq bytes).symm

/-- Sixteen initialized bytes behind a read-write view, with a zero-width reference slot at byte 8. -/
def slotted : Memory where
  allocations id := if id = 0 then some ⟨.callerStack, ⟨16, 8, [(8, 0)]⟩, true, []⟩ else none
  cells _ _ := ⟨0, true⟩
  views := [⟨0, 0, 16, true, true⟩]
  nextIdentity := 1

/-- Each element reads back, yet the elements do not form one access across the reference slot. -/
theorem elements_need_cover :
    Contents slotted ⟨0, 0⟩ 8 [0, 0] ∧ read slotted ⟨0, 0⟩ (8 * 2) 1 = .error .unsupportedLayout := by
  refine ⟨(Contents.append (xs := [0]) (ys := [0])).mpr ⟨Contents.singleton.mpr ?_, Contents.singleton.mpr ?_⟩, ?_⟩ <;>
    rfl

/-- Sixteen initialized bytes that may be read but not written. -/
def readOnly : Memory where
  allocations id := if id = 0 then some ⟨.callerStack, ⟨16, 8, []⟩, true, []⟩ else none
  cells _ _ := ⟨0, true⟩
  views := [⟨0, 0, 16, true, false⟩]
  nextIdentity := 1

/-- Readable contents grant no write authority. -/
theorem contents_not_writable : Contents readOnly ⟨0, 0⟩ 8 [0, 0] ∧ ¬ Writable readOnly ⟨0, 0⟩ 8 0 1 := by
  refine ⟨(Contents.append (xs := [0]) (ys := [0])).mpr ⟨Contents.singleton.mpr ?_, Contents.singleton.mpr ?_⟩, ?_⟩
  · rfl
  · rfl
  · intro writable
    have denied : access readOnly ⟨0, 0⟩ 8 1 true = .error .unwritable := rfl
    have allowed := writable 0 (by decide)
    simp only [Reference.element, Nat.mul_zero, Nat.add_zero] at allowed
    rw [denied] at allowed
    cases allowed

/-- A fresh sixteen-byte buffer: writable, readable once written, no byte initialized. -/
def fresh : Memory where
  allocations id := if id = 0 then some ⟨.callerStack, ⟨16, 8, []⟩, true, []⟩ else none
  cells _ _ := ⟨0, false⟩
  views := [⟨0, 0, 16, true, true⟩]
  nextIdentity := 1

/-- The producer writes its first element; the second stays unreadable and only writable. -/
theorem producer_room_faults :
    ∃ after, write fresh ⟨0, 0⟩ (numberBytes (7 : BitVec (8 * 8)).toNat 8) 1 = .ok after ∧
      Filled after ⟨0, 0⟩ 8 [7] 1 ∧ read after ⟨0, 8⟩ 8 1 = .error .uninitialized := by
  have writable : Writable fresh ⟨0, 0⟩ 8 0 2 := by
    intro i bound
    rcases i with _ | _ | _
    · rfl
    · rfl
    · omega
  exact ⟨_, rfl, (Filled.start writable).push rfl, rfl⟩

/-- Sixteen bytes with no sentinel: offset 16 is not a valid position. -/
def unsentineled : Memory where
  allocations id := if id = 0 then some ⟨.callerStack, ⟨16, 8, []⟩, true, []⟩ else none
  cells _ _ := ⟨0, true⟩
  views := [⟨0, 0, 16, true, true⟩]
  nextIdentity := 1

/-- An empty buffer asserts nothing, so it holds past the end, where a zero-width read still faults. -/
theorem empty_past_end :
    Contents unsentineled ⟨0, 16⟩ 8 [] ∧ Writable unsentineled ⟨0, 16⟩ 8 0 0 ∧
      writeElements unsentineled ⟨0, 16⟩ 8 0 [] = .ok unsentineled ∧
      read unsentineled ⟨0, 16⟩ (8 * 0) 1 = .error .invalidReference :=
  ⟨Contents.nil, Writable.zero 0, rfl, rfl⟩

/-- Sixteen bytes with an end sentinel: offset 16 is a valid position. -/
def sentineled : Memory where
  allocations id := if id = 0 then some ⟨.callerStack, ⟨16, 8, []⟩, true, [16]⟩ else none
  cells _ _ := ⟨0, true⟩
  views := [⟨0, 0, 16, true, true⟩]
  nextIdentity := 1

/-- At an end sentinel the zero-width read succeeds, and `Contents.read` joins any empty buffer it covers. -/
theorem empty_at_sentinel :
    read sentineled ⟨0, 16⟩ (8 * 0) 1 = .ok [] ∧
      ∀ m : Memory, m.WellFormed → access m ⟨0, 16⟩ (8 * 0) 1 false = .ok () →
        read m ⟨0, 16⟩ (8 * ([] : List (BitVec (8 * 8))).length) 1 = .ok (elementBytes 8 []) :=
  ⟨rfl, fun _ formed covered => Contents.nil.read formed (by decide) covered⟩

/-- A buffer one element longer than its allocation has no write authority for the last element. -/
theorem overrun_not_writable : ¬ Writable unsentineled ⟨0, 0⟩ 8 0 3 := by
  intro writable
  have denied : access unsentineled ⟨0, 16⟩ 8 1 true = .error .invalidReference := rfl
  have allowed := writable 2 (by decide)
  simp only [Reference.element] at allowed
  rw [denied] at allowed
  cases allowed

/-- Transformed 32-bit elements load back as i32 values through the width-generic load. -/
theorem transform_loads {m : Memory} {base : Reference} {xs : List (BitVec (8 * 4))}
    (contents : Contents m base 4 xs) (writable : Writable m base 4 0 xs.length) {i : Nat} (bound : i < xs.length) :
    ∃ after, transformElements m base 4 (· + 1) 0 xs.length = .ok after ∧
      loadValue after (.address (base.element 4 i)) 4 = .ok (.i32 (xs[i] + 1)) := by
  obtain ⟨after, ran, mapped, _⟩ := transform_increments contents writable
  refine ⟨after, ran, ?_⟩
  have found : (xs.map (· + 1))[i]? = some (xs[i] + 1) := by simp [bound]
  rw [mapped.load (by decide) found]
  simp only [numericOfWidth, Except.ok.injEq, CIL.Value.i32.injEq]
  exact BitVec.eq_of_toNat_eq (by simp)

/-- An unsigned byte load zero-extends: 0xFF loads as 255, not as -1. -/
theorem byte_load_zero_extends {m : Memory} {base : Reference}
    (contents : Contents m base 1 [(0xFF : BitVec (8 * 1))]) :
    loadValue m (.address base) 1 = .ok (.i32 255) := by
  simpa [numericOfWidth] using contents.load (index := 0) (by decide) rfl

/-- A 16-byte element loads as a 128-bit vector, not through the snapshot fallback. -/
theorem vector_element_loads {m : Memory} {base : Reference} {xs : List (BitVec (8 * 16))}
    (contents : Contents m base 16 xs) {i : Nat} {x : BitVec (8 * 16)} (found : xs[i]? = some x) :
    loadValue m (.address (base.element 16 i)) 16 = .ok (.v128 x) := by
  simpa [numericOfWidth] using contents.load (by decide) found

/-- Four 64-bit limbs decode as one 256-bit number, lowest limb first: the generic flat sum
    instantiated at width 8 and folded, which stays fast where rewriting at width 8 does not. -/
theorem word_limbs_flat (a b c d : BitVec (8 * 8)) :
    byteNumber (elementBytes 8 [a, b, c, d]) =
      a.toNat + b.toNat * 2 ^ 64 + c.toNat * 2 ^ 128 + d.toNat * 2 ^ 192 := by
  have h := byteNumber_elementBytes_four 8 a b c d
  simp only [Nat.reduceMul, Nat.reducePow] at h
  exact h

/-- The four-limb decode fits 32 bytes, so it survives a round trip through a 256-bit vector. -/
theorem word_limbs_fit (a b c d : BitVec (8 * 8)) :
    (BitVec.ofNat 256 (byteNumber (elementBytes 8 [a, b, c, d]))).toNat =
      byteNumber (elementBytes 8 [a, b, c, d]) :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_eq (byteNumber_elementBytes_lt 8 [a, b, c, d])
    (by simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]))

/-- The 64-bit-limb form peels one limb at a time; it avoids the kernel unfolding `x * 256^(8*k)` literals. -/
theorem word_limbs_decode (a b c d : BitVec (8 * 8)) :
    byteNumber (elementBytes 8 [a, b, c, d]) =
      a.toNat + 256 ^ 8 * (b.toNat + 256 ^ 8 * (c.toNat + 256 ^ 8 * d.toNat)) := by
  simp only [byteNumber_elementBytes_cons, elementBytes_nil]
  rfl

/-- The limb sum is the byte order, not its reverse: limbs 1 and 2 decode to 1 + 2 * 2^16. -/
example : byteNumber (elementBytes 2 [1, 2]) = 1 + 2 * 2^16 := by
  rw [byteNumber_elementBytes]; rfl

/-- Two `Slice(1)` steps reach the third element through the head and tail lemmas alone. -/
theorem span_third_after_two_tails {m : Memory} {view : SpanView} {a b c : BitVec (8 * 8)}
    {rest : List (BitVec (8 * 8))} (contents : SpanContents m view 8 (a :: b :: c :: rest))
    (valid : view.validate m = .ok ()) :
    ∃ first second reference, view.slice m 1 (view.length - 1) = .ok first ∧
      first.slice m 1 (first.length - 1) = .ok second ∧ second.element m 0 = .ok reference ∧
      loadValue m (.address reference) 8 = .ok (.i64 c) := by
  obtain ⟨first, firstOK, firstValid, _, firstContents⟩ := contents.tail valid
  obtain ⟨second, secondOK, secondValid, _, secondContents⟩ := firstContents.tail firstValid
  obtain ⟨reference, found, loaded⟩ := secondContents.head secondValid (by decide)
  exact ⟨first, second, reference, firstOK, secondOK, found,
    by simpa [numericOfWidth, BitVec.ofNat_toNat] using loaded⟩

/-- A null view holds nothing, whatever length it claims, so it cannot stand for stale contents. -/
theorem null_span_holds_nothing {m : Memory} {length : Nat} {x : BitVec (8 * 8)}
    {rest : List (BitVec (8 * 8))} :
    ¬ SpanContents m ⟨.null, length, 8, false⟩ 8 (x :: rest) := fun contents => by
  simpa using contents.contents

/-- The view's length fixes how many elements it holds; a longer list is refuted. -/
theorem span_length_refutes_extra {m : Memory} {view : SpanView} {values : List (BitVec (8 * 8))}
    {x : BitVec (8 * 8)} (contents : SpanContents m view 8 values) :
    ¬ SpanContents m view 8 (x :: values) := fun extra => by
  have := extra.length.symm.trans contents.length
  simp at this

/-- Two calls whose postcondition is `SpanSum`'s `MemoryBelow` leave the caller's span valid and
    holding the same values, with no well-formedness fact about the memory between them. -/
theorem span_survives_consecutive_calls {program : CIL.Program} {fuel method : Nat}
    {args results : List Value} {memory middle final : Memory} {view : SpanView}
    {values : List (BitVec (8 * 8))} (wellFormed : memory.WellFormed)
    (valid : view.validate memory = .ok ()) (contents : SpanContents memory view 8 values)
    (first : invoke program fuel method args memory = .ok (middle, results))
    (firstKept : MemoryBelow memory.nextIdentity memory middle)
    (secondKept : MemoryBelow middle.nextIdentity middle final) :
    MemoryBelow memory.nextIdentity memory final ∧ view.validate final = .ok () ∧
      SpanContents final view 8 values := by
  have kept := firstKept.compose_invoke first secondKept
  exact ⟨kept, view.validate_below valid wellFormed kept, contents.after_below wellFormed kept⟩

/-- Contents a callee leaves in a caller's span reach the caller's final memory through a frame
    exit that keeps only the memory below the caller's entry watermark. -/
theorem callee_contents_reach_caller_exit {entry returned final : Memory} {view : SpanView}
    {values : List (BitVec (8 * 8))} (wellFormed : entry.WellFormed)
    (valid : view.validate entry = .ok ()) (written : SpanContents returned view 8 values)
    (stillValid : view.validate returned = .ok ())
    (exit : MemoryBelow entry.nextIdentity returned final) :
    view.validate final = .ok () ∧ SpanContents final view 8 values :=
  ⟨(view.validate_eq_below valid wellFormed exit).trans stillValid,
    written.after_below_valid valid wellFormed exit⟩

/-- Without the first call's watermark growth, two `MemoryBelow` facts do not compose: a middle
    memory with a lowered watermark lets the second step rewrite caller bytes. -/
theorem consecutive_calls_need_growth :
    ¬ ∀ first middle last : Memory, MemoryBelow first.nextIdentity first middle →
      MemoryBelow middle.nextIdentity middle last →
      MemoryBelow first.nextIdentity first last := by
  intro compose
  let first : Memory :=
    { allocations := fun _ => none
      cells := fun _ _ => ⟨0, false⟩
      views := []
      nextIdentity := 1 }
  have unchanged : MemoryBelow 1 first { first with nextIdentity := 0 } :=
    ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  have vacuous : MemoryBelow 0 { first with nextIdentity := 0 }
      { first with cells := fun _ _ => ⟨1, true⟩ } :=
    ⟨fun id bound => absurd bound (Nat.not_lt_zero id),
      fun id bound => absurd bound (Nat.not_lt_zero id),
      fun id bound => absurd bound (Nat.not_lt_zero id)⟩
  have rewritten := (compose first _ _ unchanged vacuous).cells 0 Nat.zero_lt_one 0
  simp [first] at rewritten

#print axioms fill_replicates
#print axioms transform_loads
#print axioms byte_load_zero_extends
#print axioms vector_element_loads
#print axioms word_limbs_flat
#print axioms word_limbs_fit
#print axioms word_limbs_decode
#print axioms transform_increments
#print axioms fill_loads
#print axioms fill_keeps_neighbours
#print axioms update_keeps_sibling_slice
#print axioms run_update
#print axioms producer_extends
#print axioms uninitialized_rejected
#print axioms room_not_readable
#print axioms past_end_rejected
#print axioms overlap_not_apart
#print axioms update_refutes_old
#print axioms elements_need_cover
#print axioms contents_not_writable
#print axioms producer_room_faults
#print axioms empty_past_end
#print axioms empty_at_sentinel
#print axioms overrun_not_writable
#print axioms span_third_after_two_tails
#print axioms null_span_holds_nothing
#print axioms span_length_refutes_extra
#print axioms span_survives_consecutive_calls
#print axioms callee_contents_reach_caller_exit
#print axioms consecutive_calls_need_growth

end Tests.BufferContents
