import CIL.Safety.NumericLocalStore
import CIL.Safety.ByteRoundTrip

namespace CIL.Safety

/-- Decode a complete initialized typed home, including narrow integer normalization. -/
theorem load_numeric_local {memory : Memory} {reference : Reference}
    (kind : CIL.LocalKind) (value : CIL.Value) (number : Nat)
    (fits : localNumber kind value = .ok number)
    (loaded : read memory reference (localWidth kind) 1 =
      .ok (numberBytes number (localWidth kind))) :
    loadLocal memory (.bytes kind reference) = .ok (.scalar (localResult kind value)) := by
  rw [loadLocal_of_read loaded]
  cases kind <;> cases value <;>
    simp_all [localNumber, CIL.Value.hasUnspecified, localWidth, localResult, byteNumber_numberBytes]

  case aggregate.aggregate size bytes =>
    split at fits <;> simp_all
    simpa only [← ‹bytes.length = size.val›, ← fits] using numberBytes_byteNumber bytes
  case byte.i32 bits =>
    split at fits <;> simp_all
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  case narrow.i32 kind bits =>
    cases kind <;> simp_all [CIL.NarrowKind.width, CIL.NarrowKind.extend]
    all_goals
      rw [← fits]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega


/-- A checked typed store initializes precisely the bytes needed by its load. -/
theorem store_load_numeric_local {memory : Memory} {reference : Reference}
    (kind : CIL.LocalKind) (value : CIL.Value) (number : Nat)
    (fits : localNumber kind value = .ok number)
    (ready : access memory reference (localWidth kind) 1 true = .ok ()) :
    ∃ result,
      storeLocal memory (.bytes kind reference) (.scalar value) = .ok (.bytes kind reference, result) ∧
      loadLocal result (.bytes kind reference) = .ok (.scalar (localResult kind value)) := by
  obtain ⟨result, _, stored, loaded⟩ := store_numeric_local kind value number fits ready
  exact ⟨result, stored, load_numeric_local kind value number fits loaded⟩

#print axioms store_load_numeric_local

#print axioms load_numeric_local
end CIL.Safety
