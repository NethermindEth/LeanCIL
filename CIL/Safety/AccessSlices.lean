import CIL.Safety.AccessRequirements
import CIL.Safety.StaticReferences

namespace CIL.Safety

theorem access_requirements {m : Memory} {r : Reference} {width alignment : Nat}
    {writing : Bool} (h : access m r width alignment writing = .ok ()) :
    ∃ allocation, AccessRequirements m r width alignment writing allocation := by
  have formed := access_reference_valid _ _ _ _ _ h
  obtain ⟨allocation, present, live, position⟩ := formed_reference_live _ _ _ formed
  have lookup : liveAllocation m r.allocation = .ok allocation := by
    simp [liveAllocation, present, live, Pure.pure, Except.pure]
  unfold access at h
  simp only [formed, lookup, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i slots
    simp only [Pure.pure, Except.pure] at h
    split at h
    · rename_i extent
      split at h
      · rename_i aligned
        split at h
        · simp at h
        · rename_i mutable
          split at h
          · rename_i permission
            refine ⟨allocation, present, live, position, ?_, extent, ?_, ?_, ?_⟩
            · intro slot member overlap
              apply slots
              exact List.any_eq_true.mpr ⟨slot, member, by simp [overlap]⟩
            · simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using aligned
            · intro writes immutable
              simp [writes, immutable] at mutable
            · intro i bound
              exact List.all_eq_true.mp permission i (List.mem_range.mpr bound)
          · cases h
      · simp at h
    · simp at h

/-- Any reference a well-formed memory admits names an allocation below its watermark. -/
theorem Memory.WellFormed.access_bound {m : Memory} {r : Reference} {width alignment : Nat} {writing : Bool}
    (formed : m.WellFormed) (h : access m r width alignment writing = .ok ()) : r.allocation < m.nextIdentity := by
  obtain ⟨_, ready⟩ := access_requirements h
  exact (formed.1 _ _ ready.present).1

/-- A nonempty subinterval of an admitted access is itself accessible with
    byte alignment. Formation, GC layout and API authority are retained. -/
theorem AccessRequirements.slice {m : Memory} {r : Reference} {width alignment : Nat}
    {writing : Bool} {allocation : Allocation}
    (ready : AccessRequirements m r width alignment writing allocation) (wellFormed : m.WellFormed)
    (start count : Nat) (nonempty : 0 < count) (within : start + count ≤ width) :
    AccessRequirements m { r with offset := r.offset + start } count 1 writing allocation := by
  have interior : r.offset + start < allocation.layout.size := by have := ready.extent; omega
  have native := (wellFormed.1 _ _ ready.present).2.1
  refine ⟨ready.present, ready.live, ?_, ?_, ?_, ?_, ready.mutable, ?_⟩
  · simp [validPosition, interior, show r.offset + start < nativeLimit by omega]
  · intro slot member overlap
    dsimp only at overlap
    apply ready.layout slot member
    constructor <;> omega
  · change r.offset + start + count ≤ allocation.layout.size
    have := ready.extent
    omega
  · simp [Nat.mod_one]
  · intro i bound
    have permission := ready.permission (start + i) (by omega)
    simpa only [Nat.add_assoc] using permission

theorem read_slice {m : Memory} {r : Reference} {width alignment : Nat} {bytes : List (BitVec 8)}
    (wellFormed : m.WellFormed) (h : read m r width alignment = .ok bytes)
    (start count : Nat) (nonempty : 0 < count) (within : start + count ≤ width) :
    read m { r with offset := r.offset + start } count 1 =
      .ok ((List.range count).map fun i => (m.cells r.allocation (r.offset + start + i)).bits) := by
  obtain ⟨allocation, ready⟩ := access_requirements (read_access h)
  apply read_snapshot (ready.slice wellFormed start count nonempty within)
  intro i bound
  have initialized := read_requires_initialization _ _ _ _ _ h (start + i) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_assoc] using initialized

theorem AccessRequirements.add_slice {m : Memory} {r : Reference} {width alignment : Nat}
    {writing : Bool} {allocation : Allocation}
    (ready : AccessRequirements m r width alignment writing allocation) (wellFormed : m.WellFormed)
    (size index count : Nat) (nonempty : 0 < count) (within : size * index + count ≤ width) :
    add m r size (BitVec.ofNat 64 index) = .ok { r with offset := r.offset + size * index } := by
  have source := access_reference_valid _ _ _ _ _ ready.access
  have target := access_reference_valid _ _ _ _ _
    (ready.slice wellFormed (size * index) count nonempty within).access
  have bound : r.offset + size * index < 2^64 := by
    have extent := ready.extent
    have native := (wellFormed.1 _ _ ready.present).2.1
    change allocation.layout.size < 2^64 at native
    omega
  simp only [add, source, Bind.bind, Except.bind, BitVec.ofNat_mul_ofNat,
    BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  exact target

/-- A checked subread returns exactly the corresponding bytes from the admitted
    snapshot, not merely some initialized bytes in the same allocation. -/
theorem read_slice_bytes {m : Memory} {r : Reference} {width alignment : Nat}
    {bytes : List (BitVec 8)} (wellFormed : m.WellFormed)
    (loaded : read m r width alignment = .ok bytes)
    (start count : Nat) (nonempty : 0 < count) (within : start + count ≤ width) :
    read m { r with offset := r.offset + start } count 1 =
      .ok ((bytes.drop start).take count) := by
  rw [read_slice wellFormed loaded start count nonempty within]
  congr 1
  rw [read_result_snapshot loaded]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, List.length_drop]
    omega
  · intro i hi hj
    simp [Nat.add_assoc]

/-- Adjacent byte-aligned reads inside one admitted interval compose into one read of the whole interval. -/
theorem read_append {m : Memory} {r : Reference} {left right : Nat} {writing : Bool}
    {first second : List (BitVec 8)} (covered : access m r (left + right) 1 writing = .ok ())
    (low : read m r left 1 = .ok first)
    (high : read m { r with offset := r.offset + left } right 1 = .ok second) :
    read m r (left + right) 1 = .ok (first ++ second) := by
  have readable : ∀ {q width bytes}, read m q width 1 = .ok bytes → access m q width 1 false = .ok () := by
    intro q width bytes h
    unfold read at h
    cases ha : access m q width 1 false with
    | error fault => simp [ha, Bind.bind, Except.bind] at h
    | ok value => cases value; rfl
  obtain ⟨allocation, whole⟩ := access_requirements covered
  obtain ⟨_, lower⟩ := access_requirements (readable low)
  obtain ⟨_, upper⟩ := access_requirements (readable high)
  have ready : AccessRequirements m r (left + right) 1 false allocation := by
    refine ⟨whole.present, whole.live, whole.position, whole.layout, whole.extent, whole.aligned, by simp, ?_⟩
    intro i bound
    by_cases inside : i < left
    · exact lower.permission i inside
    · have permission := upper.permission (i - left) (by omega)
      simp only at permission
      rwa [show r.offset + left + (i - left) = r.offset + i by omega] at permission
  have initialized : ∀ i < left + right, (m.cells r.allocation (r.offset + i)).initialized = true := by
    intro i bound
    by_cases inside : i < left
    · exact read_requires_initialization _ _ _ _ _ low i (List.mem_range.mpr inside)
    · have cell := read_requires_initialization _ _ _ _ _ high (i - left) (List.mem_range.mpr (by omega))
      simp only at cell
      rwa [show r.offset + left + (i - left) = r.offset + i by omega] at cell
  rw [read_snapshot ready initialized, read_result_snapshot low, read_result_snapshot high]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i bound _
    simp only [List.length_map, List.length_range] at bound
    by_cases inside : i < left
    · rw [List.getElem_append_left (by simpa using inside)]
      simp
    · rw [List.getElem_append_right (by simpa using inside)]
      simp [show r.offset + left + (i - left) = r.offset + i by omega]

#print axioms read_slice_bytes
#print axioms read_append
#print axioms access_requirements
#print axioms Memory.WellFormed.access_bound
#print axioms AccessRequirements.slice
#print axioms read_slice
#print axioms AccessRequirements.add_slice

end CIL.Safety
