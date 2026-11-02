import Extracted
import CIL.Safety.StaticBindings
import CIL.Safety.WordMemory

open CIL CIL.Safety
namespace ExampleProof

/-- The identity extraction gave the static field with this metadata name. -/
def fieldIdentity (name : String) : Nat :=
  ((Extracted.program.flatMap (·.staticSites.map Prod.snd)).find? (·.fieldName == name)).elim 0
    (·.identity)

/-- Caller memory in which the two process-random seeds hold `seed0` and `seed1`. -/
def seeded (seed0 seed1 : W64) : Safety.Memory := Safety.Memory.boundStatics
  [(fieldIdentity "System.UInt64 Examples.SeededHash::Seed0", numberBytes seed0.toNat 8),
   (fieldIdentity "System.UInt64 Examples.SeededHash::Seed1", numberBytes seed1.toNat 8)]

/-- The hash `SeededHash.Hash` computes from its seeds. -/
def mix (seed0 seed1 value : W64) : W64 := (value ^^^ seed0) * 0x9E3779B97F4A7C15#64 + seed1

/-- For every pair of seeds the caller's memory binds, the method returns `mix` of them. -/
theorem correctness (seed0 seed1 value : W64) :
    (invoke Extracted.program 16 0 [.scalar (.i64 value)] (seeded seed0 seed1)).map Prod.snd =
      .ok [.scalar (.i64 (mix seed0 seed1 value))] := by
  have run : (invoke Extracted.program 16 0 [.scalar (.i64 value)]
      (seeded seed0 seed1)).map Prod.snd = .ok [.scalar (.i64 (mix
        (BitVec.ofNat 64 (byteNumber (numberBytes seed0.toNat 8)))
        (BitVec.ofNat 64 (byteNumber (numberBytes seed1.toNat 8))) value))] := by
    -- The seeds are symbolic, so the run is checked by unfolding rather than by evaluation.
    with_unfolding_all rfl
  rwa [decode_word64, decode_word64] at run

/-- No fixed seed is the universal contract: changing one seed changes the result. -/
theorem seed_matters :
    ¬ ∀ seed0 seed1 value : W64,
      (invoke Extracted.program 16 0 [.scalar (.i64 value)] (seeded seed0 seed1)).map Prod.snd =
        .ok [.scalar (.i64 (mix 0 0 value))] := by
  intro guessed
  have changed := (correctness 1 0 0).symm.trans (guessed 1 0 0)
  simp [mix] at changed

/-- Without a caller binding the seed loads fault, so no result is ever computed. -/
theorem unbound_faults (value : W64) :
    (invoke Extracted.program 16 0 [.scalar (.i64 value)] Safety.Memory.empty).toOption = none :=
  rfl

#print axioms correctness
#print axioms seed_matters
#print axioms unbound_faults
end ExampleProof
