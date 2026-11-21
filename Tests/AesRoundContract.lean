import CIL.Safety.MethodContract

/-! The compiled portable AES round on its two 64-bit state halves and two round-key halves. -/

namespace Tests.AesRoundContract
open CIL.Safety

/-- The round returns AESENC and writes only its fresh frame storage. -/
def roundContract : MethodContract (CIL.W64 × CIL.W64 × CIL.W64 × CIL.W64) (BitVec 128) where
  args := fun (a, b, k, l) => [.scalar (.i64 a), .scalar (.i64 b), .scalar (.i64 k), .scalar (.i64 l)]
  results value := [.scalar (.v128 value)]
  pre _ memory := memory.WellFormed
  footprint _ := []
  post := fun (a, b, k, l) _ _ value =>
    value = CIL.Vector.aesEncryptRound (CIL.Vector.pack128 a b) (CIL.Vector.pack128 k l)

/-- For a zero state, changing only the high key half flips one output bit. Loading the low
    half twice returns 0x63 in every byte and violates the same contract on both profiles. -/
theorem refuted_of_dropped_key {program : CIL.Program} {fuel : Nat}
    (observed : (invoke program fuel 0 (roundContract.args (0, 0, 0, 1)) Memory.empty).map Prod.snd =
      .ok [.scalar (.v128 0x63636363636363636363636363636363)]) :
    roundContract.Refuted program 0 := by
  cases ran : invoke program fuel 0 (roundContract.args (0, 0, 0, 1)) Memory.empty with
  | error fault => rw [ran] at observed; cases observed
  | ok result =>
    obtain ⟨after, values⟩ := result
    rw [ran] at observed
    have actual : values = [.scalar (.v128 0x63636363636363636363636363636363)] := Except.ok.inj observed
    subst values
    apply MethodContract.Refuted.of_return (c := roundContract) (input := (0, 0, 0, 1))
      Memory.empty_wellFormed ran
    rintro ⟨_, value, encoded, rfl⟩
    revert encoded
    decide +kernel

#print axioms refuted_of_dropped_key

end Tests.AesRoundContract
