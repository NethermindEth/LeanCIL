import CIL.Safety.ByteRoundTrip
import CIL.Safety.Execution
import CIL.Safety.WriteEffects

namespace CIL.Safety

theorem vector128_bytes_roundtrip (bytes : List (BitVec 8)) (length : bytes.length = 16) :
    numberBytes (BitVec.ofNat 128 (byteNumber bytes)).toNat 16 = bytes := by
  have bound : byteNumber bytes < 2^128 := by simpa [length] using byteNumber_lt bytes
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  simpa [length] using numberBytes_byteNumber bytes

theorem vector256_bytes_roundtrip (bytes : List (BitVec 8)) (length : bytes.length = 32) :
    numberBytes (BitVec.ofNat 256 (byteNumber bytes)).toNat 32 = bytes := by
  have bound : byteNumber bytes < 2^256 := by simpa [length] using byteNumber_lt bytes
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  simpa [length] using numberBytes_byteNumber bytes

theorem vector512_bytes_roundtrip (bytes : List (BitVec 8)) (length : bytes.length = 64) :
    numberBytes (BitVec.ofNat 512 (byteNumber bytes)).toNat 64 = bytes := by
  have bound : byteNumber bytes < 2^512 := by simpa [length] using byteNumber_lt bytes
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  simpa [length] using numberBytes_byteNumber bytes

theorem initialized_snapshot_bytes (bytes : List (BitVec 8 × Bool))
    (initialized : bytes.all Prod.snd = true) :
    (bytes.map Prod.fst).map (fun b => (b, true)) = bytes := by
  induction bytes with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨bits, flag⟩ := head
    simp only [List.all_cons, Bool.and_eq_true] at initialized
    simp only [List.map_cons, ih initialized.2]
    simp_all

/-- Both bits and initialization flags survive reinterpretation, including
    completely unknown and partially initialized snapshots. -/
theorem valueSnapshot_snapshotValue (shape : CIL.SnapshotShape) (bytes : List (BitVec 8 × Bool))
    (length : bytes.length = shape.width) :
    valueSnapshot shape (snapshotValue shape bytes) = some bytes := by
  unfold snapshotValue
  split
  · rename_i initialized
    have same := initialized_snapshot_bytes bytes initialized
    cases shape with
    | aggregate width =>
      simp [valueSnapshot, CIL.SnapshotShape.width] at length ⊢
      exact ⟨length, by simpa using same⟩
    | vector128 =>
      simp only [valueSnapshot, ↓reduceIte]
      rw [vector128_bytes_roundtrip _ (by simpa [CIL.SnapshotShape.width] using length), same]
    | vector256 =>
      simp only [valueSnapshot, ↓reduceIte]
      rw [vector256_bytes_roundtrip _ (by simpa [CIL.SnapshotShape.width] using length), same]
    | vector512 =>
      simp only [valueSnapshot, ↓reduceIte]
      rw [vector512_bytes_roundtrip _ (by simpa [CIL.SnapshotShape.width] using length), same]
  · simp [valueSnapshot, length]

theorem bitcastValue_preserves_snapshot (source target : CIL.SnapshotShape) (input : CIL.Value)
    (bytes : List (BitVec 8 × Bool)) (sizes : source.width = target.width)
    (snapshot : valueSnapshot source input = some bytes) :
    ∃ output, bitcastValue source target input = .ok output ∧ valueSnapshot target output = some bytes := by
  have known : input.hasUnspecified = false := by
    cases input <;> simp_all [CIL.Value.hasUnspecified, valueSnapshot]
  refine ⟨snapshotValue target bytes, ?_, ?_⟩
  · simp [bitcastValue, known, sizes, snapshot, Pure.pure, Except.pure]
  · exact valueSnapshot_snapshotValue target bytes ((valueSnapshot_length snapshot).trans sizes)

/-- Snapshot stores preserve each byte's initialization flag, rather than
    turning copied unknown bytes into initialized bytes. -/
theorem writeSnapshot_cell (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8 × Bool)) (alignment i : Nat)
    (written : writeSnapshot m r bytes alignment = .ok result) (bound : i < bytes.length) :
    result.cells r.allocation (r.offset + i) = ⟨bytes[i].1, bytes[i].2⟩ := by
  unfold writeSnapshot at written
  cases hw : write m r (bytes.map Prod.fst) alignment <;>
    simp only [hw, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
  · cases written
  · cases written
    simp [List.getElem?_eq_getElem bound]

theorem writeSnapshot_readback (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8 × Bool)) (alignment : Nat)
    (written : writeSnapshot m r bytes alignment = .ok result) :
    readSnapshot result r bytes.length alignment = .ok bytes := by
  unfold writeSnapshot at written
  cases hw : write m r (bytes.map Prod.fst) alignment <;>
    simp only [hw, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
  · cases written
  · rename_i stored
    have readback := write_readback _ _ _ _ _ hw
    have accessOK : access stored r bytes.length alignment false = .ok () := by
      unfold read at readback
      simp only [List.length_map] at readback
      cases ha : access stored r bytes.length alignment false <;>
        simp_all [Bind.bind, Except.bind]
    cases written
    simp only [readSnapshot]
    change (do
      access stored r bytes.length alignment false
      pure ((List.range bytes.length).map fun i => _)) = _
    rw [accessOK]
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq]
    apply List.ext_getElem
    · simp
    · intro i left right
      simp only [List.getElem_map, List.getElem_range]
      simp [List.getElem?_eq_getElem right]

#print axioms vector128_bytes_roundtrip
#print axioms vector256_bytes_roundtrip
#print axioms vector512_bytes_roundtrip
#print axioms valueSnapshot_snapshotValue
#print axioms bitcastValue_preserves_snapshot
#print axioms writeSnapshot_cell
#print axioms writeSnapshot_readback

end CIL.Safety
