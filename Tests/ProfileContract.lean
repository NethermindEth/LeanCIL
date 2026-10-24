import CIL.Safety.ProfileContract

/-! A contract proved once under one feature profile and carried to other profiles by
    `MethodContract.Holds.reprofile`, with the profile agreement decided from the flags the
    program reads. A method that tests AVX2 returns `1` exactly where AVX2 is on, so the
    transport must hold for profiles that agree on AVX2 and must not reach one that does not. -/
namespace Tests.ProfileContract

open CIL CIL.Safety

/-- The profile the program is extracted and proved under. -/
def avx2Profile : FeatureProfile := { architecture := .x64, avx2 := true }

/-- Agrees with `avx2Profile` on AVX2 and turns on AVX-512, which the program never reads. -/
def avx512Profile : FeatureProfile := { architecture := .x64, avx2 := true, avx512F := true }

/-- Agrees with `avx2Profile` on AVX2 and turns on BMI2, which the program never reads. -/
def bmi2Profile : FeatureProfile := { architecture := .x64, avx2 := true, bmi2 := true }

/-- Turns AVX2 off, so the feature test answers differently. -/
def scalarProfile : FeatureProfile := { architecture := .x64 }

/-- `IsSupported(Avx2) ? 1 : 0`, as one method under `avx2Profile`. -/
@[cil_code] def program : Program :=
  [{ profile := avx2Profile, returnsValue := true, locals := [], code := [.feature .avx2, .ret] }]

/-- Calling with no arguments returns the AVX2 answer of `avx2Profile` and changes no memory. -/
def avx2Contract : MethodContract Unit where
  args _ := []
  pre _ _ := True
  footprint _ := []
  post _ _ _ values := values = [.scalar (.i32 1)]

theorem uniform : ∀ body ∈ program, body.profile = avx2Profile := by decide

/-- The single proof that steps the body. -/
theorem avx2_holds : avx2Contract.Holds program 0 := by
  rintro - memory -
  refine ⟨10, memory, _, ?_, Confined.refl _ memory, _, rfl, rfl⟩
  cil_checked_steps [program, avx2Profile]
  rfl

theorem avx512_holds : avx2Contract.Holds (reprofile program avx512Profile) 0 :=
  avx2_holds.reprofile uniform (Program.ProfileAgreement.of_flags _ _ _ (by decide))

theorem bmi2_holds : avx2Contract.Holds (reprofile program bmi2Profile) 0 :=
  avx2_holds.reprofile uniform (Program.ProfileAgreement.of_flags _ _ _ (by decide))

/-- The extraction under `avx512Profile`: the same body with its own profile. -/
@[cil_code] def avx512Program : Program :=
  [{ profile := avx512Profile, returnsValue := true, locals := [],
     code := [.feature .avx2, .ret] }]

/-- A separate per-profile extraction is certified once it is shown to be the reprofiling. -/
theorem extraction_holds : avx2Contract.Holds avx512Program 0 := by
  rw [show avx512Program = reprofile program avx512Profile from rfl]
  exact avx512_holds

/-- One statement covers every profile with AVX2 on, whatever else it enables. -/
theorem avx2_family_holds (target : FeatureProfile) (wide : target.avx2 = true) :
    avx2Contract.Holds (reprofile program target) 0 :=
  avx2_holds.reprofile uniform (Program.ProfileAgreement.of_flags _ _ _ (by
    simp [Program.profileReads, Op.profileReads, program, avx2Profile, FeatureProfile.evaluate,
      wide]))

/-- The agreement check is not vacuous: it rejects a profile that answers AVX2 differently. -/
example : ¬ ∀ featureId ∈ program.profileReads,
    avx2Profile.evaluate featureId = scalarProfile.evaluate featureId := by decide

/-- A memory with no allocations; the method reads none, so it shows the difference. -/
def emptyMemory : CIL.Safety.Memory :=
  { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }

/-- The contract really depends on AVX2: under `scalarProfile` the method returns `0`. -/
theorem scalar_rejected : ¬ avx2Contract.Holds (reprofile program scalarProfile) 0 := by
  intro holds
  obtain ⟨fuel, final, values, invoked, -, out, encoded, returned⟩ :=
    holds () emptyMemory trivial
  have scalarRun : CIL.Safety.invoke (reprofile program scalarProfile) 10 0 [] emptyMemory =
      Except.ok (emptyMemory, [.scalar (.i32 0)]) := by
    cil_checked_steps [reprofile, program, scalarProfile]
  have same := invoke_ok_unique invoked scalarRun
  simp only [avx2Contract] at encoded returned
  subst encoded returned
  simp at same

/-- info: 'Tests.ProfileContract.avx512_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms avx512_holds
/-- info: 'Tests.ProfileContract.bmi2_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bmi2_holds
/-- info: 'Tests.ProfileContract.extraction_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms extraction_holds
/-- info: 'Tests.ProfileContract.avx2_family_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms avx2_family_holds
/-- info: 'Tests.ProfileContract.scalar_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms scalar_rejected

end Tests.ProfileContract
