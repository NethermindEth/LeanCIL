import CIL.Safety.MethodContract
import CIL.Safety.ValueBitCasts

/-! Caller memory for the in-place `DivisionIntrinsics.SwapHalves` contract. Both spans
start at the same address. The vector local occupies a separate frame-owned allocation. -/

namespace Tests.HalfSwapContract
open CIL.Safety

/-- A live caller allocation grants read and write access to its 32 initialized bytes. -/
def memory (data : Nat → BitVec 8) : Memory := { Memory.empty with
  allocations := fun id => if id == 0 then some ⟨.callerStack, ⟨32, 1, []⟩, true, [32]⟩ else none
  cells := fun _ offset => ⟨data offset, true⟩
  views := [⟨0, 0, 32, true, true⟩]
  nextIdentity := 1 }

/-- Swapping in place rotates the 32 caller bytes by 16 and returns no value. -/
def swap : MethodContract (Nat → BitVec 8) Unit where
  args _ := [.bufferSpan ⟨.address ⟨0, 0⟩, 32, 1, false⟩, .bufferSpan ⟨.address ⟨0, 0⟩, 32, 1, true⟩]
  results _ := []
  footprint _ := [(⟨0, 0⟩, 32)]
  pre data before := before = memory data
  post data _ after _ := ∀ i, i < 32 → (after.cells 0 i).bits = data ((i + 16) % 32)

/-- Sixteen input bytes in increasing address order. -/
def bytes (data : Nat → BitVec 8) (start : Nat) : List (BitVec 8) :=
  (List.range 16).map fun i => data (start + i)

/-- The little-endian vector value of one input half. -/
def packed (data : Nat → BitVec 8) (start : Nat) :=
  BitVec.ofNat 128 (byteNumber (bytes data start))

/-- Storing the vector writes its sixteen source bytes. -/
theorem unpack (data : Nat → BitVec 8) (start : Nat) :
    numberBytes (packed data start).toNat 16 = bytes data start :=
  vector128_bytes_roundtrip _ (by simp [bytes])
#print axioms unpack

/-- After the destination reference is saved, the vector local owns allocation one. -/
def saved : Frame := ⟨1, [.root (some (.address ⟨0, 0⟩)), .bytes .vector128 ⟨1, 0⟩], [1], 0, []⟩

/-- Contents after a checked write into an already readable window. -/
def put (m : Memory) (id offset : Nat) (block : List (BitVec 8)) : Memory :=
  { m with cells := fun target i =>
      if target = id ∧ offset ≤ i then
        match block[i - offset]? with
        | some bits => ⟨bits, true⟩
        | none => m.cells target i
      else m.cells target i }

/-- Frame entry initializes the private vector home to zero. -/
def entered (data : Nat → BitVec 8) : Memory :=
  let m := memory data
  let fresh := ((allocateHome m 1 16 1).toOption.getD (⟨1, 0⟩, m)).2
  put fresh 1 0 (numberBytes 0 16)

/-- The private home holds the lower half before the first caller write. -/
def savedLow (data : Nat → BitVec 8) := put (entered data) 1 0 (bytes data 0)
/-- The low half holds the original high half. -/
def highWritten (data : Nat → BitVec 8) := put (savedLow data) 0 0 (bytes data 16)
/-- The high half holds the saved low half. -/
def lowWritten (data : Nat → BitVec 8) := put (highWritten data) 0 16 (bytes data 0)

private theorem highWrite (data : Nat → BitVec 8) :
    write (savedLow data) ⟨0, 0⟩ (bytes data 16) 1 = .ok (highWritten data) := by with_unfolding_all rfl
#print axioms highWrite

private theorem lowWrite (data : Nat → BitVec 8) :
    write (highWritten data) ⟨0, 16⟩ (bytes data 0) 1 = .ok (lowWritten data) := by with_unfolding_all rfl
#print axioms lowWrite

/-- Retiring the frame preserves caller allocations, permissions and bytes outside the span. -/
theorem framed (data : Nat → BitVec 8) :
    Confined [(⟨0, 0⟩, 32)] (memory data) (expire (lowWritten data) 1) := by
  constructor
  · change 1 ≤ 2
    decide
  all_goals
    intro id old
    have h : id = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ old)
    subst id
  · with_unfolding_all rfl
  · intro offset outside
    have endBound : 32 ≤ offset := by simpa [Outside] using outside
    change (lowWritten data).cells 0 offset = _
    rw [write_outside _ _ _ _ _ _ _ (lowWrite data) (Or.inr (Or.inr (by simpa [bytes] using endBound))),
        write_outside _ _ _ _ _ _ _ (highWrite data) (Or.inr (Or.inr (by simp [bytes]; omega)))]
    with_unfolding_all rfl
  · intro offset
    with_unfolding_all rfl
  · intro offset _
    with_unfolding_all rfl
  · intro offset _
    with_unfolding_all rfl
#print axioms framed

/-- Each output byte comes from the opposite half of the original input. -/
theorem swapped (data : Nat → BitVec 8) (i : Nat) (bound : i < 32) :
    ((expire (lowWritten data) 1).cells 0 i).bits = data ((i + 16) % 32) := by
  change ((lowWritten data).cells 0 i).bits = _
  by_cases low : i < 16
  · rw [write_outside _ _ _ _ _ _ _ (lowWrite data) (Or.inr (Or.inl low))]
    have inside : i < (bytes data 16).length := by simpa [bytes] using low
    have same := write_initializes _ _ _ _ _ i (highWrite data) inside
    simpa [bytes, Nat.add_comm, Nat.mod_eq_of_lt (show i + 16 < 32 by omega)] using congrArg Cell.bits same
  · have inside : i - 16 < (bytes data 0).length := by simp [bytes]; omega
    have same := write_initializes _ _ _ _ _ (i - 16) (lowWrite data) inside
    have idx : 16 + (i - 16) = i := by omega
    have rotated : (i + 16) % 32 = i - 16 := by omega
    simpa [bytes, idx, rotated] using congrArg Cell.bits same
#print axioms swapped

/-- Only the first byte of the high half is set. -/
def witness (offset : Nat) : BitVec 8 := if offset == 16 then 1 else 0

/-- A successful return leaving zero at byte zero violates the swap on this input. -/
theorem refuted_of_first_byte {program : CIL.Program}
    (observed : (invoke program 64 0 (swap.args witness) (memory witness)).map
      (fun r => (r.2, (r.1.cells 0 0).bits)) = .ok ([], 0)) : swap.Refuted program 0 := by
  cases h : invoke program 64 0 (swap.args witness) (memory witness) with
  | error error => rw [h] at observed; cases observed
  | ok pair =>
    obtain ⟨after, values⟩ := pair
    rw [h] at observed
    have eq : (values, (after.cells 0 0).bits) = (([] : List Value), (0 : BitVec 8)) :=
      Except.ok.inj observed
    apply MethodContract.Refuted.of_return (c := swap) (input := witness) rfl h
    rintro ⟨_, _, _, post⟩
    have expected : (after.cells 0 0).bits = 1 := post 0 (by decide)
    have first : (after.cells 0 0).bits = 0 := congrArg Prod.snd eq
    rw [first] at expected
    contradiction
#print axioms refuted_of_first_byte

end Tests.HalfSwapContract
