import CIL.Safety.ProfileContract

/-! A contract proved once under one feature profile and carried to other profiles by
    `MethodContract.Holds.reprofile` and its outcome forms, with the profile agreement decided
    from the flags the program reads. A method that tests AVX2 returns `1` exactly where AVX2
    is on, so the transport must reach profiles that agree on AVX2 and no profile that does
    not. The programs are synthetic stand-ins for extractions. -/
namespace Tests.ProfileContract

open CIL CIL.Safety

/-- x86-64-v3: the profile the program is proved under. -/
def avx2Profile : FeatureProfile := {
  architecture := .x64, x86Base64 := true, sse2 := true, ssse3 := true, sse41 := true,
  sse42 := true, avx := true, avx2 := true, bmi1 := true, bmi2 := true,
  vector128Accelerated := true, vector256Accelerated := true }

/-- x86-64-v4: agrees with `avx2Profile` on AVX2 and turns on AVX-512. -/
def avx512Profile : FeatureProfile :=
  { avx2Profile with avx512F := true, avx512FVL := true, avx512DQ := true, avx512DQVL := true }

/-- x86-64-v3 with 256-bit vectors disabled: agrees on AVX2, differs in acceleration. -/
def narrowProfile : FeatureProfile := { avx2Profile with vector256Accelerated := false }

/-- The x86-64 baseline: AVX2 is off, so the feature test answers differently. -/
def baselineProfile : FeatureProfile :=
  { architecture := .x64, x86Base64 := true, sse2 := true, vector128Accelerated := true }

/-- Every profile the contract is carried between is a supported runtime configuration. -/
theorem profiles_valid : avx2Profile.Valid ∧ avx512Profile.Valid ∧ narrowProfile.Valid ∧
    baselineProfile.Valid := by decide

/-- Method 0 is `IsSupported(Avx2) ? 1 : 0`; method 1 always throws. Both use `avx2Profile`. -/
@[cil_code] def program : Program :=
  [{ profile := avx2Profile, returnsValue := true, locals := [],
     code := [.feature .avx2, .ret] },
   { profile := avx2Profile, returnsValue := false, locals := [],
     code := [.throw "System.PlatformNotSupportedException"] }]

/-- Calling with no arguments returns `1` and changes no memory. -/
def avx2Contract : MethodContract Unit where
  args _ := []
  pre _ _ := True
  footprint _ := []
  post _ _ _ values := values = [.scalar (.i32 1)]

/-- Every method of `program` uses `avx2Profile`. -/
theorem uniform : ∀ body ∈ program, body.profile = avx2Profile := by decide

/-- Under `avx2Profile` the method returns `1`; the only proof that steps the body. -/
theorem avx2_holds : avx2Contract.Holds program 0 := by
  rintro - memory -
  refine ⟨10, memory, _, ?_, Confined.refl _ memory, _, rfl, rfl⟩
  cil_checked_steps [program, avx2Profile]
  rfl

/-- The contract holds on x86-64-v4, with agreement checked by `decide`. -/
theorem avx512_holds : avx2Contract.Holds (reprofile program avx512Profile) 0 :=
  avx2_holds.reprofile uniform (Program.ProfileAgreement.of_flags _ _ _ (by decide))

/-- The contract holds with 256-bit vectors disabled. -/
theorem narrow_holds : avx2Contract.Holds (reprofile program narrowProfile) 0 :=
  avx2_holds.reprofile uniform (Program.ProfileAgreement.of_flags _ _ _ (by decide))

/-- The same bodies written with their own profile, as a per-profile extraction would be. -/
@[cil_code] def avx512Program : Program :=
  [{ profile := avx512Profile, returnsValue := true, locals := [],
     code := [.feature .avx2, .ret] },
   { profile := avx512Profile, returnsValue := false, locals := [],
     code := [.throw "System.PlatformNotSupportedException"] }]

/-- A per-profile program is certified once it is shown to be the reprofiling. -/
theorem extraction_holds : avx2Contract.Holds avx512Program 0 := by
  rw [show avx512Program = reprofile program avx512Profile from rfl]
  exact avx512_holds

/-- One statement covers every profile with AVX2 on, whatever else it enables. -/
theorem avx2_family_holds (target : FeatureProfile) (wide : target.avx2 = true) :
    avx2Contract.Holds (reprofile program target) 0 :=
  avx2_holds.reprofile uniform (Program.ProfileAgreement.of_flags _ _ _ (by
    simp [Program.profileReads, Op.profileReads, program, avx2Profile, FeatureProfile.evaluate,
      wide]))

/-- The normal-return outcome form carries over: method 0 never raises. -/
theorem outcome_holds :
    ({ avx2Contract with raises := fun _ _ => none } : OutcomeContract Unit).Holds
      (reprofile program narrowProfile) 0 :=
  avx2_holds.outcomes.reprofile uniform (Program.ProfileAgreement.of_flags _ _ _ (by decide))

/-- Method 1 raises `PlatformNotSupportedException` and returns nothing. -/
def throwContract : OutcomeContract Unit where
  args _ := []
  pre _ _ := True
  footprint _ := []
  post _ _ _ _ := False
  raises _ _ := some "System.PlatformNotSupportedException"

/-- Under `avx2Profile` method 1 raises the named exception. -/
theorem throw_holds : throwContract.Holds program 1 := by
  rintro - memory -
  cil_raise_steps []

/-- The raising branch carries over, as an outcome and with the CLR-named exception. -/
theorem throw_transported : throwContract.Holds (reprofile program avx512Profile) 1 ∧
    throwContract.HoldsCLR (reprofile program narrowProfile) 1 :=
  ⟨throw_holds.reprofile uniform (Program.ProfileAgreement.of_flags _ _ _ (by decide)),
    throw_holds.clr.reprofile uniform (Program.ProfileAgreement.of_flags _ _ _ (by decide))⟩

/-- `avx2Contract` with a precondition that reads the program's static descriptors. -/
def staticContract (descriptors : List StaticDescriptor) : MethodContract Unit :=
  { avx2Contract with pre := fun _ memory => StaticWorldValid descriptors memory }

/-- `throwContract` with a precondition that reads the program's static descriptors. -/
def staticThrowContract (descriptors : List StaticDescriptor) : OutcomeContract Unit :=
  { throwContract with pre := fun _ memory => StaticWorldValid descriptors memory }

/-- Descriptor-indexed contracts are stated for the target program's own descriptors. -/
theorem statics_transported :
    (staticContract (programStaticDescriptors (reprofile program avx512Profile))).Holds
      (reprofile program avx512Profile) 0 ∧
    (staticThrowContract (programStaticDescriptors (reprofile program avx512Profile))).Holds
      (reprofile program avx512Profile) 1 :=
  ⟨MethodContract.Holds.reprofile_statics (contract := staticContract) uniform
      (Program.ProfileAgreement.of_flags _ _ _ (by decide))
      (fun input memory _ => avx2_holds input memory trivial),
    OutcomeContract.Holds.reprofile_statics (contract := staticThrowContract) uniform
      (Program.ProfileAgreement.of_flags _ _ _ (by decide))
      (fun input memory _ => throw_holds input memory trivial)⟩

/-- The agreement check is not vacuous: it rejects a profile that answers AVX2 differently. -/
theorem baseline_disagrees : ¬ ∀ featureId ∈ program.profileReads,
    avx2Profile.evaluate featureId = baselineProfile.evaluate featureId := by decide

/-- A memory with no allocations; the method reads none, so it shows the difference. -/
def emptyMemory : CIL.Safety.Memory :=
  { allocations := fun _ => none, cells := fun _ _ => ⟨0, false⟩, views := [], nextIdentity := 0 }

/-- The contract really depends on AVX2: on the baseline the method returns `0`. -/
theorem baseline_rejected : ¬ avx2Contract.Holds (reprofile program baselineProfile) 0 := by
  intro holds
  obtain ⟨fuel, final, values, invoked, -, out, encoded, returned⟩ :=
    holds () emptyMemory trivial
  have baselineRun :
      CIL.Safety.invoke (reprofile program baselineProfile) 10 0 [] emptyMemory =
        Except.ok (emptyMemory, [.scalar (.i32 0)]) := by
    cil_checked_steps [reprofile, program, baselineProfile]
  have same := invoke_ok_unique invoked baselineRun
  simp only [avx2Contract] at encoded returned
  subst encoded returned
  simp at same

/-- An AVX-512 DQ multiply needs four flags, all of which the agreement check reads. -/
def intrinsicProgram : Program :=
  [{ profile := avx512Profile, returnsValue := true, locals := [],
     code := [.arg 0, .arg 1, .intrinsic (.avx512DQ .mul64) 2, .ret] }]

/-- Profiles that agree on the four flags agree on the multiply. -/
theorem intrinsic_agrees : intrinsicProgram.ProfileAgreement avx512Profile
    { avx512Profile with vector256Accelerated := false } :=
  Program.ProfileAgreement.of_flags _ _ _ (by decide)

/-- Turning off only the VL extension changes availability, and the check sees it. This
    profile is not `Valid`; it isolates one of the four flags. -/
theorem intrinsic_check_rejects : ¬ ∀ featureId ∈ intrinsicProgram.profileReads,
    avx512Profile.evaluate featureId =
      ({ avx512Profile with avx512DQVL := false } : FeatureProfile).evaluate featureId := by
  decide

/-- The rejection is real: the two profiles disagree on the multiply's availability. -/
theorem intrinsic_disagrees : ¬ intrinsicProgram.ProfileAgreement avx512Profile
    { avx512Profile with avx512DQVL := false } := by
  intro agreement
  have available := agreement _ (List.mem_singleton_self _) (.intrinsic (.avx512DQ .mul64) 2)
    (by simp)
  simp [Op.ProfileAgreement, Intrinsic.available, avx512Profile, avx2Profile] at available

/-- info: 'Tests.ProfileContract.uniform' does not depend on any axioms -/
#guard_msgs in #print axioms uniform
/-- info: 'Tests.ProfileContract.avx2_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms avx2_holds
/-- info: 'Tests.ProfileContract.avx512_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms avx512_holds
/-- info: 'Tests.ProfileContract.narrow_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms narrow_holds
/-- info: 'Tests.ProfileContract.extraction_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms extraction_holds
/-- info: 'Tests.ProfileContract.avx2_family_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms avx2_family_holds
/-- info: 'Tests.ProfileContract.baseline_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms baseline_rejected
/-- info: 'Tests.ProfileContract.profiles_valid' does not depend on any axioms -/
#guard_msgs in #print axioms profiles_valid
/-- info: 'Tests.ProfileContract.outcome_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms outcome_holds
/-- info: 'Tests.ProfileContract.throw_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms throw_holds
/-- info: 'Tests.ProfileContract.throw_transported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms throw_transported
/-- info: 'Tests.ProfileContract.statics_transported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms statics_transported
/-- info: 'Tests.ProfileContract.baseline_disagrees' depends on axioms: [propext] -/
#guard_msgs in #print axioms baseline_disagrees
/-- info: 'Tests.ProfileContract.intrinsic_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms intrinsic_agrees
/-- info: 'Tests.ProfileContract.intrinsic_check_rejects' depends on axioms: [propext] -/
#guard_msgs in #print axioms intrinsic_check_rejects
/-- info: 'Tests.ProfileContract.intrinsic_disagrees' depends on axioms: [propext] -/
#guard_msgs in #print axioms intrinsic_disagrees

end Tests.ProfileContract
