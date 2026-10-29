import CIL.Safety.MethodContract
import CIL.Safety.ByteRoundTrip
import CIL.Safety.WordMemory

/-!
# Typed buffers in checked memory

Contracts over arrays of `width`-byte little-endian elements at `base`. `Contents` says each
element reads back at its position, `Writable` grants write authority over a run of elements,
and `Filled` combines an initialized prefix with writable room for a producer. The lemmas
split and join runs, carry contents across writes, confined calls and frame changes, and
prove the element-by-element loops `writeElements` and `transformElements`.
-/

namespace CIL.Safety

/-- Element `index` of a buffer of `width`-byte elements starting at `base`, in the same
    allocation. -/
def Reference.element (base : Reference) (width index : Nat) : Reference :=
  ⟨base.allocation, base.offset + width * index⟩

@[simp] theorem Reference.element_allocation (base : Reference) (width index : Nat) :
    (base.element width index).allocation = base.allocation := rfl

@[simp] theorem Reference.element_offset (base : Reference) (width index : Nat) :
    (base.element width index).offset = base.offset + width * index := rfl

@[simp] theorem Reference.element_zero (base : Reference) (width : Nat) :
    base.element width 0 = base := by
  cases base
  simp [Reference.element]

theorem Reference.element_element (base : Reference) (width first second : Nat) :
    (base.element width first).element width second = base.element width (first + second) := by
  simp [Reference.element, Nat.mul_add, Nat.add_assoc]

/-- Little-endian bytes of a buffer, each element encoded as a scalar store of `width`
    bytes writes it. -/
def elementBytes (width : Nat) (xs : List (BitVec (8 * width))) : List (BitVec 8) :=
  xs.flatMap fun x => numberBytes x.toNat width

@[simp] theorem numberBytes_length (value width : Nat) :
    (numberBytes value width).length = width := by
  simp [numberBytes]

@[simp] theorem elementBytes_nil (width : Nat) : elementBytes width [] = [] := rfl

@[simp] theorem elementBytes_cons (width : Nat) (x : BitVec (8 * width))
    (xs : List (BitVec (8 * width))) :
    elementBytes width (x :: xs) = numberBytes x.toNat width ++ elementBytes width xs := rfl

@[simp] theorem elementBytes_length (width : Nat) (xs : List (BitVec (8 * width))) :
    (elementBytes width xs).length = width * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [elementBytes_cons, List.length_append, numberBytes_length, ih, List.length_cons,
      Nat.mul_succ]
    omega

/-- The `width` bytes at element `index` of an encoded buffer are that element's encoding. -/
theorem elementBytes_slice {width : Nat} {xs : List (BitVec (8 * width))} {index : Nat}
    {x : BitVec (8 * width)} (found : xs[index]? = some x) :
    ((elementBytes width xs).drop (width * index)).take width = numberBytes x.toNat width := by
  induction xs generalizing index with
  | nil => simp at found
  | cons y ys ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      simp
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      rw [elementBytes_cons, List.drop_append, List.drop_eq_nil_of_le (by simp [Nat.mul_succ]),
        List.nil_append, numberBytes_length, show width * (index + 1) - width = width * index by
          rw [Nat.mul_succ]; omega]
      exact ih found

/-- An element decodes to its own value, so a scalar load of its bytes returns it. -/
theorem element_value {width : Nat} (x : BitVec (8 * width)) :
    byteNumber (numberBytes x.toNat width) = x.toNat := by
  rw [byteNumber_numberBytes]
  apply Nat.mod_eq_of_lt
  have bound := x.isLt
  rwa [Nat.pow_mul] at bound

theorem byteNumber_cons (byte : BitVec 8) (bytes : List (BitVec 8)) :
    byteNumber (byte :: bytes) = byte.toNat + 256 * byteNumber bytes := rfl

/-- Little-endian: the high bytes are scaled past every low byte. -/
theorem byteNumber_append (low high : List (BitVec 8)) :
    byteNumber (low ++ high) = byteNumber low + 256 ^ low.length * byteNumber high := by
  induction low with
  | nil => simp [byteNumber]
  | cons byte low ih =>
    rw [List.cons_append, byteNumber_cons, ih, byteNumber_cons, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add]; ac_rfl

/-- Decoding a typed buffer peels its lowest element, which is scaled by one element width. -/
theorem byteNumber_elementBytes_cons (width : Nat) (x : BitVec (8 * width))
    (xs : List (BitVec (8 * width))) :
    byteNumber (elementBytes width (x :: xs)) =
      x.toNat + 256 ^ width * byteNumber (elementBytes width xs) := by
  rw [elementBytes_cons, byteNumber_append, element_value, numberBytes_length]

/-- The whole-value decode of a typed buffer is the sum of its elements, element `i` scaled
    by `256^(width*i)`. -/
theorem byteNumber_elementBytes (width : Nat) (xs : List (BitVec (8 * width))) :
    byteNumber (elementBytes width xs) =
      (xs.zipIdx.map fun p => p.1.toNat * 256 ^ (width * p.2)).sum := by
  suffices shifted : ∀ start, 256 ^ (width * start) * byteNumber (elementBytes width xs) =
      ((xs.zipIdx start).map fun p => p.1.toNat * 256 ^ (width * p.2)).sum by
    simpa using shifted 0
  induction xs with
  | nil => simp [byteNumber]
  | cons x xs ih =>
    intro start
    rw [byteNumber_elementBytes_cons, List.zipIdx_cons, List.map_cons, List.sum_cons,
      ← ih (start + 1), Nat.mul_succ, Nat.pow_add]
    rw [Nat.mul_add]; ac_rfl

/-- The decode of `xs.length` elements fits `width * xs.length` bytes, so a `BitVec` of that
    size keeps it. -/
theorem byteNumber_elementBytes_lt (width : Nat) (xs : List (BitVec (8 * width))) :
    byteNumber (elementBytes width xs) < 256 ^ (width * xs.length) := by
  simpa using byteNumber_lt (elementBytes width xs)

/-- Four limbs decode as one flat sum. Instantiate this at a literal width instead of rewriting
    `byteNumber_elementBytes` there, which makes the kernel unfold the literal powers. -/
theorem byteNumber_elementBytes_four (width : Nat) (a b c d : BitVec (8 * width)) :
    byteNumber (elementBytes width [a, b, c, d]) =
      a.toNat + b.toNat * 256 ^ width + c.toNat * 256 ^ (width * 2) +
        d.toNat * 256 ^ (width * 3) := by
  rw [byteNumber_elementBytes]
  simp [Nat.add_assoc]

/-- Interval `(r, width)` shares no byte with `entry`, so neither does any subinterval of it. -/
theorem Apart.sub {r : Reference} {width : Nat} {entry : Reference × Nat}
    (apart : Apart r width entry) {start count : Nat} (within : start + count ≤ width) :
    Apart ⟨r.allocation, r.offset + start⟩ count entry := by
  rcases apart with different | below | above
  · exact Or.inl different
  · exact Or.inr (Or.inl (by simp only; omega))
  · exact Or.inr (Or.inr (by simp only; omega))

/-- Element `index` lies inside the first `count` elements when `index < count`. -/
theorem element_le {width index count : Nat} (bound : index < count) :
    width * index + width ≤ width * count := by
  have := Nat.mul_le_mul_left width (Nat.succ_le_of_lt bound)
  rwa [Nat.mul_succ] at this

/-- Element runs `[first, first + left)` and `[second, second + right)` that do not overlap
    share no byte. -/
theorem Reference.element_run_apart (base : Reference) (width : Nat)
    {first left second right : Nat}
    (separate : first + left ≤ second ∨ second + right ≤ first) :
    Apart (base.element width first) (width * left) (base.element width second, width * right) := by
  rcases separate with before | after
  · have := Nat.mul_le_mul_left width before
    rw [Nat.mul_add] at this
    exact Or.inr (Or.inl (by simp only [Reference.element_offset]; omega))
  · have := Nat.mul_le_mul_left width after
    rw [Nat.mul_add] at this
    exact Or.inr (Or.inr (by simp only [Reference.element_offset]; omega))

/-- Distinct elements of one buffer share no byte. -/
theorem Reference.element_apart (base : Reference) (width : Nat) {first second : Nat}
    (different : first ≠ second) :
    Apart (base.element width first) width (base.element width second, width) := by
  simpa using base.element_run_apart width (left := 1) (right := 1) (by omega)

/-- A run of elements inside an enclosing run of the same buffer lies within it. -/
theorem Reference.element_run_within (base : Reference) (width : Nat)
    {first count outer total : Nat}
    (start : outer ≤ first) (finish : first + count ≤ outer + total) :
    Within (base.element width first, width * count) (base.element width outer, width * total) := by
  have low := Nat.mul_le_mul_left width start
  have high := Nat.mul_le_mul_left width finish
  rw [Nat.mul_add, Nat.mul_add] at high
  exact ⟨rfl, by simp only [Reference.element_offset]; omega,
    by simp only [Reference.element_offset]; omega⟩

/-- Offsetting a formed base by `index` elements reaches that element whenever it is accessible. -/
theorem add_element {m : Memory} {base : Reference} {width index : Nat} {writing : Bool}
    (formed : m.WellFormed) (valid : form m base = .ok base)
    (target : access m (base.element width index) width 1 writing = .ok ()) :
    add m base width (BitVec.ofNat 64 index) = .ok (base.element width index) := by
  obtain ⟨allocation, ready⟩ := access_requirements target
  have native := (formed.1 _ _ ready.present).2.1
  have extent := ready.extent
  have bound : base.offset + width * index < 2^64 := by
    change allocation.layout.size < 2^64 at native
    simp only [Reference.element_offset] at extent
    omega
  simp only [add, valid, Bind.bind, Except.bind, BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  exact access_reference_valid _ _ _ _ _ target

/-- Each element of `xs` reads back at its position with the byte alignment scalar loads
    use; grants no write authority. -/
def Contents (m : Memory) (base : Reference) (width : Nat) (xs : List (BitVec (8 * width))) :
    Prop :=
  ∀ index x, xs[index]? = some x →
    read m (base.element width index) width 1 = .ok (numberBytes x.toNat width)

/-- Write authority for `count` elements from element `start`; no byte need be readable or
    initialized. -/
def Writable (m : Memory) (base : Reference) (width start count : Nat) : Prop :=
  ∀ i < count, access m (base.element width (start + i)) width 1 true = .ok ()

/-- An initialized prefix `xs`, then `room` writable elements that need not be readable. -/
def Filled (m : Memory) (base : Reference) (width : Nat) (xs : List (BitVec (8 * width)))
    (room : Nat) : Prop :=
  Contents m base width xs ∧ Writable m base width xs.length room

section Contents

variable {m : Memory} {base : Reference} {width : Nat}

/-- The empty buffer has contents anywhere; it asserts no formation, access or initialization. -/
theorem Contents.nil : Contents m base width [] := fun _ _ found => by simp at found

/-- A one-element buffer is exactly one scalar-width read. -/
theorem Contents.singleton {x : BitVec (8 * width)} :
    Contents m base width [x] ↔ read m base width 1 = .ok (numberBytes x.toNat width) := by
  constructor
  · intro contents
    simpa using contents 0 x rfl
  · intro loaded index y found
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      simpa using loaded
    | succ index => simp at found

/-- A scalar 64-bit load of element `index` returns that element. -/
theorem Contents.load_word {base : Reference} {xs : List (BitVec (8 * 8))}
    (contents : Contents m base 8 xs) {index : Nat} {x : BitVec (8 * 8)}
    (found : xs[index]? = some x) :
    loadValue m (.address (base.element 8 index)) 8 = .ok (.i64 x) :=
  load_word64_of_read (contents index x found)

/-- A scalar load of element `index` at any scalar width returns that element. -/
theorem Contents.load {xs : List (BitVec (8 * width))} (contents : Contents m base width xs)
    (scalar : ScalarWidth width) {index : Nat} {x : BitVec (8 * width)}
    (found : xs[index]? = some x) :
    loadValue m (.address (base.element width index)) width =
      .ok (numericOfWidth width x.toNat) :=
  load_scalar_of_read scalar (contents index x found)

/-- The first `count` elements keep their contents. -/
theorem Contents.take {xs : List (BitVec (8 * width))} (contents : Contents m base width xs)
    (count : Nat) :
    Contents m base width (xs.take count) := fun index x found => by
  rw [List.getElem?_take] at found
  split at found
  · exact contents index x found
  · simp at found

/-- Dropping `count` elements moves the base to element `count`. -/
theorem Contents.drop {xs : List (BitVec (8 * width))} (contents : Contents m base width xs)
    (count : Nat) :
    Contents m (base.element width count) width (xs.drop count) := fun index x found => by
  rw [List.getElem?_drop] at found
  rw [Reference.element_element]
  exact contents _ x found

/-- Adjacent runs split and join at any element boundary. -/
theorem Contents.append {xs ys : List (BitVec (8 * width))} :
    Contents m base width (xs ++ ys) ↔
      Contents m base width xs ∧ Contents m (base.element width xs.length) width ys := by
  constructor
  · intro contents
    refine ⟨?_, ?_⟩
    · simpa using contents.take xs.length
    · simpa using contents.drop xs.length
  · rintro ⟨low, high⟩ index x found
    by_cases inside : index < xs.length
    · rw [List.getElem?_append_left inside] at found
      exact low index x found
    · rw [List.getElem?_append_right (by omega)] at found
      have loaded := high _ x found
      rwa [Reference.element_element, show xs.length + (index - xs.length) = index by omega]
        at loaded

/-- One checked read of a whole buffer gives the contents of each element. -/
theorem Contents.of_read {xs : List (BitVec (8 * width))} {alignment : Nat}
    (formed : m.WellFormed) (positive : 0 < width)
    (loaded : read m base (width * xs.length) alignment = .ok (elementBytes width xs)) :
    Contents m base width xs := fun index x found => by
  have bound : index < xs.length := (List.getElem?_eq_some_iff.mp found).1
  have slice := read_slice_bytes formed loaded (width * index) width positive (element_le bound)
  rwa [elementBytes_slice found] at slice

/-- Contents join into one checked read only with `covered`: separate elements need not form
    one access. -/
theorem Contents.read {xs : List (BitVec (8 * width))} {writing : Bool} (formed : m.WellFormed)
    (positive : 0 < width) (contents : Contents m base width xs)
    (covered : access m base (width * xs.length) 1 writing = .ok ()) :
    read m base (width * xs.length) 1 = .ok (elementBytes width xs) := by
  induction xs generalizing base with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero] at covered ⊢
    obtain ⟨allocation, ready⟩ := access_requirements covered
    have empty : AccessRequirements m base 0 1 false allocation :=
      { ready with
          mutable := (by simp)
          permission := fun _ bound => absurd bound (Nat.not_lt_zero _) }
    simpa using read_snapshot empty fun _ bound => absurd bound (Nat.not_lt_zero _)
  | cons x xs ih =>
    have split := Contents.append.mp (show Contents m base width ([x] ++ xs) from contents)
    have low := Contents.singleton.mp split.1
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm] at covered ⊢
    rw [elementBytes_cons]
    cases xs with
    | nil => simpa using low
    | cons y ys =>
      obtain ⟨allocation, ready⟩ := access_requirements covered
      have tail := (ready.slice formed width (width * (ys.length + 1))
        (Nat.mul_pos positive (by omega)) (by simp)).access
      have high := ih split.2 (by simpa [Reference.element] using tail)
      exact read_append covered low (by simpa [Reference.element] using high)

/-- A nonempty buffer lies inside its live allocation, so contents past its end are refutable. -/
theorem Contents.extent {xs : List (BitVec (8 * width))} (contents : Contents m base width xs)
    (nonempty : xs ≠ []) :
    ∃ allocation, m.allocations base.allocation = some allocation ∧ allocation.live = true ∧
      base.offset + width * xs.length ≤ allocation.layout.size := by
  obtain ⟨last, rest, rfl⟩ : ∃ last rest, xs = rest ++ [last] :=
    ⟨xs.getLast nonempty, xs.dropLast, (List.dropLast_concat_getLast nonempty).symm⟩
  have loaded := (Contents.append.mp contents).2 0 last (by simp)
  obtain ⟨allocation, present, live, bounds⟩ :=
    access_within_allocation _ _ _ _ _ (read_access loaded)
  refine ⟨allocation, by simpa using present, live, ?_⟩
  simp only [Reference.element_element, Nat.add_zero, Reference.element_offset] at bounds
  simpa [Nat.mul_succ, Nat.add_assoc] using bounds

/-- A write apart from the whole buffer keeps every element, including in the same allocation. -/
theorem Contents.after_write_apart {xs : List (BitVec (8 * width))} {r : Reference}
    {bytes : List (BitVec 8)} {alignment : Nat} {after : Memory}
    (contents : Contents m base width xs) (written : write m r bytes alignment = .ok after)
    (apart : Apart base (width * xs.length) (r, bytes.length)) :
    Contents after base width xs := fun index x found => by
  have bound : index < xs.length := (List.getElem?_eq_some_iff.mp found).1
  have separate := apart.sub (element_le bound)
  exact write_preserves_disjoint_read written (contents index x found) separate

/-- A write of element `index` sets that element and keeps the others. -/
theorem Contents.write_element {xs : List (BitVec (8 * width))} {index : Nat}
    {x : BitVec (8 * width)} {after : Memory} (contents : Contents m base width xs)
    (written : write m (base.element width index) (numberBytes x.toNat width) 1 = .ok after) :
    Contents after base width (xs.set index x) := fun other y found => by
  by_cases same : other = index
  · subst other
    have value : y = x := by
      rw [List.getElem?_set_self'] at found
      cases h : xs[index]? <;> simp_all
    subst value
    simpa using write_readback _ _ _ _ _ written
  · rw [List.getElem?_set_ne (Ne.symm same)] at found
    have separate := base.element_apart width same
    exact write_preserves_disjoint_read written (contents other y found)
      (by simpa only [Apart, numberBytes_length] using separate)

/-- One write of a run `ys` at element `index` replaces that run and keeps the rest of the
    buffer. -/
theorem Contents.write_run {xs ys : List (BitVec (8 * width))} {index : Nat} {after : Memory}
    (formed : m.WellFormed) (positive : 0 < width) (contents : Contents m base width xs)
    (written : write m (base.element width index) (elementBytes width ys) 1 = .ok after)
    (fits : index + ys.length ≤ xs.length) :
    Contents after base width (xs.take index ++ ys ++ xs.drop (index + ys.length)) := by
  have prefixLength : (xs.take index ++ ys).length = index + ys.length := by simp; omega
  refine Contents.append.mpr ⟨Contents.append.mpr ⟨?_, ?_⟩, ?_⟩
  · refine (contents.take index).after_write_apart written ?_
    have := base.element_run_apart width (first := 0) (left := (xs.take index).length)
      (second := index) (right := ys.length) (Or.inl (by simp [Nat.min_le_left]))
    simpa using this
  · have readback := write_readback _ _ _ _ _ written
    rw [elementBytes_length] at readback
    have middle :=
      Contents.of_read (write_preserves_wellFormed _ _ _ _ _ formed written) positive readback
    simpa [Nat.min_eq_left (show index ≤ xs.length by omega)] using middle
  · rw [prefixLength]
    refine (contents.drop (index + ys.length)).after_write_apart written ?_
    have := base.element_run_apart width (first := index + ys.length)
      (left := (xs.drop (index + ys.length)).length) (second := index) (right := ys.length)
      (Or.inr (by omega))
    simpa using this

/-- Contents of older memory apart from every footprint entry survive a confined call. -/
theorem Contents.after_confined {footprint : List (Reference × Nat)} {before after : Memory}
    {xs : List (BitVec (8 * width))} (contents : Contents before base width xs)
    (framed : Confined footprint before after) (formed : before.WellFormed)
    (apart : ∀ entry ∈ footprint, Apart base (width * xs.length) entry) :
    Contents after base width xs :=
  fun index x found =>
    have bound : index < xs.length := (List.getElem?_eq_some_iff.mp found).1
    framed.read_apart formed (contents index x found) fun entry member =>
      (apart entry member).sub (element_le bound)

/-- Contents of memory below `watermark` survive any change that keeps that memory, such as
    frame exit. -/
theorem Contents.after_below {watermark : Nat} {before after : Memory}
    {xs : List (BitVec (8 * width))} (contents : Contents before base width xs)
    (preserved : MemoryBelow watermark before after)
    (old : base.allocation < watermark) : Contents after base width xs :=
  fun index x found =>
    (preserved.read (base.element width index) old width 1).trans (contents index x found)

end Contents

section Writable

variable {m : Memory} {base : Reference} {width : Nat}

theorem Writable.zero (start : Nat) : Writable m base width start 0 :=
  fun _ bound => absurd bound (Nat.not_lt_zero _)

/-- Writable runs split and join at any element boundary. -/
theorem Writable.append {start left right : Nat} :
    Writable m base width start (left + right) ↔
      Writable m base width start left ∧ Writable m base width (start + left) right := by
  constructor
  · intro writable
    exact ⟨fun i bound => writable i (by omega), fun i bound => by
      simpa [Nat.add_assoc] using writable (left + i) (by omega)⟩
  · rintro ⟨low, high⟩ i bound
    by_cases inside : i < left
    · exact low i inside
    · simpa [Nat.add_assoc, show left + (i - left) = i by omega]
        using high (i - left) (by omega)

/-- Any checked write keeps write authority everywhere. -/
theorem Writable.after_write {start count : Nat} {r : Reference} {bytes : List (BitVec 8)}
    {alignment : Nat} {after : Memory} (writable : Writable m base width start count)
    (written : write m r bytes alignment = .ok after) :
    Writable after base width start count := fun i bound => by
  obtain ⟨_, ready⟩ := access_requirements (writable i bound)
  exact (ready.after_write written).access

/-- A confined call keeps write authority over older memory, inside its footprint too. -/
theorem Writable.after_confined {footprint : List (Reference × Nat)} {before after : Memory}
    {start count : Nat} (writable : Writable before base width start count)
    (framed : Confined footprint before after) (formed : before.WellFormed) :
    Writable after base width start count := fun i bound =>
  (framed.access_write _ (formed.access_bound (writable i bound)) width 1).trans (writable i bound)

/-- Write authority below `watermark` survives any change that keeps that memory, such as
    frame entry. -/
theorem Writable.after_below {watermark : Nat} {before after : Memory} {start count : Nat}
    (writable : Writable before base width start count)
    (preserved : MemoryBelow watermark before after)
    (old : base.allocation < watermark) : Writable after base width start count :=
  fun i bound =>
    (preserved.access (base.element width (start + i)) old width 1 true).trans (writable i bound)

/-- A writable element accepts its encoding; no prior initialization or read authority is needed. -/
theorem Writable.write_succeeds {start count : Nat}
    (writable : Writable m base width start (count + 1)) (x : BitVec (8 * width)) :
    ∃ after, write m (base.element width start) (numberBytes x.toNat width) 1 = .ok after :=
  CIL.Safety.write_succeeds (by simpa using writable 0 (by omega))

end Writable

section Filled

variable {m : Memory} {base : Reference} {width : Nat}

/-- A producer starts from write authority alone. -/
theorem Filled.start {room : Nat} (writable : Writable m base width 0 room) :
    Filled m base width [] room :=
  ⟨Contents.nil, writable⟩

/-- Writing the next element extends the initialized prefix by that element and shrinks the
    room by one. -/
theorem Filled.push {xs : List (BitVec (8 * width))} {room : Nat} {x : BitVec (8 * width)}
    {after : Memory} (filled : Filled m base width xs (room + 1))
    (written : write m (base.element width xs.length) (numberBytes x.toNat width) 1 = .ok after) :
    Filled after base width (xs ++ [x]) room := by
  obtain ⟨contents, writable⟩ := filled
  refine ⟨Contents.append.mpr
    ⟨contents.after_write_apart written ?_, Contents.singleton.mpr ?_⟩, ?_⟩
  · have := base.element_run_apart width (first := 0) (left := xs.length) (second := xs.length)
      (right := 1) (Or.inl (by omega))
    simpa using this
  · simpa using write_readback _ _ _ _ _ written
  · rw [Nat.add_comm room 1] at writable
    simpa using (Writable.append.mp writable).2.after_write written

/-- A full producer has written every element. -/
theorem Filled.complete {xs : List (BitVec (8 * width))} (filled : Filled m base width xs 0) :
    Contents m base width xs := filled.1

end Filled

/-- Write `xs` element by element from element `start`, stopping at the first fault. -/
def writeElements (m : Memory) (base : Reference) (width start : Nat) :
    List (BitVec (8 * width)) → Checked Memory
  | [] => .ok m
  | x :: xs => do
    let next ← write m (base.element width start) (numberBytes x.toNat width) 1
    writeElements next base width (start + 1) xs

/-- Read element `index` as a value and write `f` of it back, for `count` elements from
    `index`, stopping at the first fault. -/
def transformElements (m : Memory) (base : Reference) (width : Nat)
    (f : BitVec (8 * width) → BitVec (8 * width)) : Nat → Nat → Checked Memory
  | _, 0 => .ok m
  | index, count + 1 => do
    let bytes ← read m (base.element width index) width 1
    let next ← write m (base.element width index)
      (numberBytes (f (BitVec.ofNat (8 * width) (byteNumber bytes))).toNat width) 1
    transformElements next base width f (index + 1) count

/-- Mapping one more element of a partly mapped list is a `set` at the boundary. -/
theorem map_prefix_set {α : Type} (f : α → α) {xs : List α} {i : Nat} (h : i < xs.length) :
    ((xs.take i).map f ++ xs.drop i).set i (f xs[i]) =
      (xs.take (i + 1)).map f ++ xs.drop (i + 1) := by
  rw [List.set_append_right _ _ (by simp; omega)]
  simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt h), Nat.sub_self]
  rw [List.drop_eq_getElem_cons h, List.set_cons_zero, List.take_add_one,
    List.getElem?_eq_getElem h]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
    List.cons_append, List.nil_append]

/-- A producer loop of any length extends its prefix by exactly the written elements,
    confined to them. -/
theorem Filled.fill {m : Memory} {base : Reference} {width : Nat}
    {done xs : List (BitVec (8 * width))} {room : Nat}
    (filled : Filled m base width done (xs.length + room)) :
    ∃ after, writeElements m base width done.length xs = .ok after ∧
      Filled after base width (done ++ xs) room ∧
      Confined [(base.element width done.length, width * xs.length)] m after := by
  induction xs generalizing m done with
  | nil => exact ⟨m, rfl, by simpa using filled, Confined.refl _ m⟩
  | cons x xs ih =>
    have shifted : Filled m base width done ((xs.length + room) + 1) := by
      simpa [Nat.add_right_comm] using filled
    obtain ⟨next, written⟩ := shifted.2.write_succeeds (count := xs.length + room) x
    have pushed := shifted.push written
    obtain ⟨after, rest, result, framed⟩ := ih (by simpa using pushed)
    refine ⟨after, ?_, by simpa using result, ?_⟩
    · simp only [writeElements, written, Bind.bind, Except.bind]
      simpa using rest
    have first := Confined.write_within
      (footprint := [(base.element width done.length, width * (xs.length + 1))])
      written ⟨_, List.mem_singleton_self _, by
        simpa using base.element_run_within width (first := done.length) (count := 1)
          (outer := done.length) (total := xs.length + 1) (Nat.le_refl _) (by omega)⟩
    refine first.trans (framed.widen_within fun entry member => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at member
    subst member
    simpa using base.element_run_within width (first := done.length + 1) (count := xs.length)
      (outer := done.length) (total := xs.length + 1) (by omega) (by omega)

/-- An in-place transform of any length maps every element by `f`, leaving the buffer's
    write authority. -/
theorem Contents.transform {m : Memory} {base : Reference} {width : Nat}
    (f : BitVec (8 * width) → BitVec (8 * width)) {xs : List (BitVec (8 * width))}
    (contents : Contents m base width xs)
    (writable : Writable m base width 0 xs.length) :
    ∃ after, transformElements m base width f 0 xs.length = .ok after ∧
      Contents after base width (xs.map f) ∧ Writable after base width 0 xs.length ∧
      Confined [(base, width * xs.length)] m after := by
  -- After `done` steps the first `done` elements are mapped and the rest are unchanged.
  suffices step : ∀ done (m : Memory), done ≤ xs.length →
      Contents m base width ((xs.take done).map f ++ xs.drop done) →
      Writable m base width 0 xs.length →
      ∃ after, transformElements m base width f done (xs.length - done) = .ok after ∧
        Contents after base width (xs.map f) ∧ Writable after base width 0 xs.length ∧
        Confined [(base, width * xs.length)] m after by
    simpa using step 0 m (Nat.zero_le _) (by simpa using contents) writable
  intro done
  induction h : xs.length - done generalizing done with
  | zero =>
    intro m bound current writable
    have full : done = xs.length := by omega
    subst full
    exact ⟨m, rfl, by simpa using current, writable, Confined.refl _ m⟩
  | succ remaining ih =>
    intro m bound current writable
    have inside : done < xs.length := by omega
    let x := xs[done]
    have found : ((xs.take done).map f ++ xs.drop done)[done]? = some x := by
      rw [List.getElem?_append_right (by simp; omega)]
      simp [x, show done - min done xs.length = 0 by omega, List.getElem?_drop, inside]
    have loaded := current done x found
    obtain ⟨next, written⟩ := CIL.Safety.write_succeeds (bytes := numberBytes (f x).toNat width)
      (by simpa using writable done inside)
    have updated := current.write_element written
    rw [map_prefix_set f inside] at updated
    obtain ⟨after, rest, result, stillWritable, framed⟩ :=
      ih (done + 1) (by omega) next (by omega) updated (writable.after_write written)
    have decoded : BitVec.ofNat (8 * width) (byteNumber (numberBytes x.toNat width)) = x := by
      rw [element_value]; simp
    refine ⟨after, ?_, result, stillWritable, ?_⟩
    · simp only [transformElements, loaded, decoded, written, Bind.bind, Except.bind]
      exact rest
    · refine (Confined.write_within written ⟨_, List.mem_singleton_self _, ?_⟩).trans framed
      simpa using base.element_run_within width (first := done) (count := 1) (outer := 0)
        (total := xs.length) (Nat.zero_le _) (by omega)

#print axioms elementBytes_slice
#print axioms element_value
#print axioms byteNumber_cons
#print axioms byteNumber_append
#print axioms byteNumber_elementBytes_cons
#print axioms byteNumber_elementBytes
#print axioms byteNumber_elementBytes_lt
#print axioms byteNumber_elementBytes_four
#print axioms Reference.element_apart
#print axioms add_element
#print axioms Contents.singleton
#print axioms Contents.load_word
#print axioms Contents.load
#print axioms Contents.append
#print axioms Contents.of_read
#print axioms Contents.read
#print axioms Contents.extent
#print axioms Contents.after_write_apart
#print axioms Contents.write_element
#print axioms Contents.write_run
#print axioms Contents.after_confined
#print axioms Contents.after_below
#print axioms Writable.append
#print axioms Writable.after_write
#print axioms Writable.after_confined
#print axioms Writable.after_below
#print axioms Writable.write_succeeds
#print axioms Filled.push
#print axioms Filled.fill
#print axioms Contents.transform

/-- A successful whole-span fill establishes a repeated sequence, without any readable-input
    premise. In particular, the destination may initially be entirely uninitialized. -/
theorem SpanView.fill_contents (view : SpanView) {before after : Memory} (base : Reference)
    (value : BitVec (8 * view.width)) (formed : before.WellFormed)
    (address : view.reference = .address base) (positive : 0 < view.width)
    (filled : view.fill before (numberBytes value.toNat view.width) = .ok after) :
    Contents after base view.width (List.replicate view.length value) := by
  by_cases empty : view.length = 0
  · simp [empty, Contents]
  · have written := view.fill_written before after base _ address empty filled
    have encoding : elementBytes view.width (List.replicate view.length value) =
        (List.replicate view.length (numberBytes value.toNat view.width)).flatten := by
      simp [elementBytes, List.flatMap, List.map_replicate]
    have readback := write_readback _ _ _ _ _ written
    rw [← encoding, elementBytes_length] at readback
    exact Contents.of_read (write_preserves_wellFormed _ _ _ _ _ formed written) positive readback
#print axioms SpanView.fill_contents

/-- Filling a nonempty span preserves readable sequences disjoint from its extent, including
    neighbouring slices of the same allocation. -/
theorem Contents.after_span_fill {before after : Memory} {base target : Reference}
    {width : Nat} {values : List (BitVec (8 * width))} (view : SpanView)
    (element : List (BitVec 8)) (contents : Contents before base width values)
    (address : view.reference = .address target) (nonempty : view.length ≠ 0)
    (size : element.length = view.width)
    (filled : view.fill before element = .ok after)
    (apart : Apart base (width * values.length) (target, view.length * view.width)) :
    Contents after base width values := by
  apply contents.after_write_apart (view.fill_written before after target element address nonempty filled)
  simpa [List.length_flatten, List.map_replicate, size] using apart
#print axioms Contents.after_span_fill

end CIL.Safety
