import CIL.Embedding.Tactic

/-!
# Profile-parametric method embeddings

One template is bound to three extraction profiles using proved local flag and callee facts.
The extracted layout has extra dead instructions, so its branch map is not the identity.
-/

namespace Tests.ProfileEmbedding

open CIL

/-- Portable extraction with both dispatch flags disabled. -/
def portable : FeatureProfile := .scalar

/-- SSE4.2 extraction with the required runtime capability group enabled. -/
def narrow : FeatureProfile := {
  architecture := .x64, sse2 := true, x86Base64 := true, vector128Accelerated := true
  ssse3 := true, sse41 := true, sse42 := true }

/-- AVX2 extraction with its required runtime capability group enabled. -/
def wide : FeatureProfile := {
  narrow with avx := true, avx2 := true, bmi1 := true, bmi2 := true }

/-- All three extraction profiles satisfy the runtime capability policy. -/
theorem profiles_valid : portable.Valid ∧ narrow.Valid ∧ wide.Valid := by decide +kernel
#print axioms profiles_valid

/-- Code removed by profile extraction has no live instruction to match. -/
abbrev unreachable : Op := .unsupported "Unreachable under selected profile"

/-- One body over two feature flags and a callee, shared by all extraction profiles. -/
def template (profile : FeatureProfile) (sse42 avx2 : Bool) (callee : Nat) : Method := {
  profile, returnsValue := true, locals := [], code := [
    .feature .avx2, .brzero 6,
    if avx2 then .arg 0 else unreachable,
    if avx2 then .arg 1 else unreachable,
    if avx2 then .call callee 2 else unreachable,
    if avx2 then .ret else unreachable,
    if avx2 then unreachable else if sse42 then .arg 1 else .arg 0,
    if avx2 then unreachable else .ret] }

/-- An extracted layout has two extra dead instructions before the scalar branch target. -/
def extracted (profile : FeatureProfile) (callee : Nat) : Method := {
  profile, returnsValue := true, locals := [], code := [
    .feature .avx2, .brzero 8,
    if profile.avx2 then .arg 0 else unreachable,
    if profile.avx2 then .arg 1 else unreachable,
    if profile.avx2 then .call callee 2 else unreachable,
    if profile.avx2 then .ret else unreachable,
    unreachable, unreachable,
    if profile.avx2 then unreachable else if profile.sse42 then .arg 1 else .arg 0,
    if profile.avx2 then unreachable else .ret] }

/-- Local equalities bind an open template to each of three profile extractions. -/
theorem profiles_embed (profile : FeatureProfile) (sse42 avx2 : Bool) (callee : Nat)
    (selected : profile = portable ∨ profile = narrow ∨ profile = wide)
    (sse : sse42 = profile.sse42) (avx : avx2 = profile.avx2) (called : callee = 3) :
    MethodEmbeds [extracted profile 3] 0 (template profile sse42 avx2 callee) := by
  rcases selected with rfl | rfl | rfl <;> cil_embed [sse, avx, called]
#print axioms profiles_embed

/-- Closed local definitions do not require an explicit rewrite list. -/
theorem local_definitions : MethodEmbeds [extracted wide 3] 0
    (template wide true true 3) := by
  let profile := wide
  let avx := profile.avx2
  let sse := profile.sse42
  let callee := 3
  change MethodEmbeds [extracted profile callee] 0 (template profile sse avx callee)
  cil_embed
#print axioms local_definitions

/-- The unused parameter has no effect on this body. -/
def ignoresFlag (_flag : Bool) : Method := template portable false false 3

/-- An open argument may remain only when explicit unfolding proves it irrelevant. -/
theorem irrelevant_flag (flag : Bool) :
    MethodEmbeds [extracted portable 3] 0 (ignoresFlag flag) := by
  cil_embed [ignoresFlag]
#print axioms irrelevant_flag

/-- A supplied embedding proof closes the current goal without consuming its sibling. -/
theorem sibling_goal
    (embedded : MethodEmbeds [extracted portable 3] 0 (template portable false false 3)) :
    MethodEmbeds [extracted portable 3] 0 (template portable false false 3) ∧ True := by
  constructor
  cil_embed [embedded]
  trivial
#print axioms sibling_goal

/-- An incorrect flag equality cannot be established for the portable extraction. -/
theorem false_flag_refuted : ¬ (true = portable.sse42) := by decide +kernel
#print axioms false_flag_refuted

/-- error: cil_embed: unresolved parameters remain -/
#guard_msgs (substring := true) in
example (sse42 : Bool) :
    MethodEmbeds [extracted portable 3] 0 (template portable sse42 false 3) := by
  cil_embed

/-- error: cil_embed: unresolved parameters remain -/
#guard_msgs (substring := true) in
example (sse42 avx2 : Bool) (avx : avx2 = false) :
    MethodEmbeds [extracted portable 3] 0 (template portable sse42 avx2 3) := by
  cil_embed [avx]

/-- error: cil_embed: the expected body does not embed -/
#guard_msgs (substring := true) in
example : MethodEmbeds [extracted portable 3] 0 (template portable true false 3) := by
  cil_embed

/-- error: cil_embed: the expected body does not embed -/
#guard_msgs (substring := true) in
example (callee : Nat) (called : callee = 4) :
    MethodEmbeds [extracted wide 3] 0 (template wide true true callee) := by
  cil_embed [called]

/-- error: cil_embed: the expected body does not embed -/
#guard_msgs (substring := true) in
example : MethodEmbeds
    [{ extracted portable 3 with code := (extracted portable 3).code.set 1 (.brzero 9) }] 0
    (template portable false false 3) := by
  cil_embed

end Tests.ProfileEmbedding
