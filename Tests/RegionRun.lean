import CIL.Safety.RegionRun
import CIL.Safety.Embedding.Simulation
import CIL.Safety.Embedding.Suffix
import Tests.Support

/-! A suffix run moves to a body whose prefix is a call instead of inline code. -/
namespace Tests.RegionRun

open CIL (Method Instruction Embeds)
open CIL.Safety

def helper : Method :=
  { code := [.ldarg 0, .ldc_i4 6, .shr, .ret], locals := [], returnsValue := true }

/-- Computes `count >> 6` inline, then adds one. -/
def expected : Method :=
  { code := [.ldarg 0, .ldc_i4 6, .shr, .ldc_i4 1, .add, .ret], locals := [],
    returnsValue := true }

/-- The same suffix after a compiled helper call, one pc earlier. -/
def actual : Method :=
  { code := [.ldarg 0, .call (Tests.callee 1) {}, .ldc_i4 1, .add, .ret],
    links := [(1, .direct 1)], locals := [], returnsValue := true }

def masked : Method :=
  { expected with code := List.replicate 3 (.unadmitted 0) ++ expected.code.drop 3 }

abbrev suffix : Nat → Nat → Prop := fun method pc => inStarts [(0, 3)] method pc = true

theorem suffix_closed : RegionClosed [expected, helper] suffix := RegionClosed.of_check (by decide)

theorem suffix_agrees : AgreesOn [expected, helper] [masked, helper] suffix :=
  AgreesOn.set (program := [expected, helper]) (index := 0) rfl masked.code fun _ inside =>
    code_agrees_of_drop (lower := 3) rfl (by simpa [suffix, inStarts] using inside)

/-- The masked prefix is dead, so only the suffix needs an image. -/
theorem masked_embeds : Embeds masked actual [0, 0, 0, 2, 3, 4] := by
  constructor <;> rfl

theorem suffix_moves (fuel : Nat) (args stack : List Value) (frame : Frame) (m : Memory) (result : Memory × List Value)
    (ran : run [expected, helper] fuel 0 3 args frame stack m = .ok result) :
    run [actual, helper] fuel 0 2 args frame stack m = .ok result := by
  rw [← run_congr_region suffix_closed suffix_agrees _ _ _ _ _ _ _ (by decide)] at ran
  exact run_refines ((ProgramRefines.refl [actual, helper]).set (index := 0) rfl masked_embeds)
    fuel 0 3 args frame stack m result ran

/-- A region may call into a whole method listed from pc 0. -/
def caller : Method :=
  { code := [.ldc_i4 5, .ret, .ldarg 0, .call (Tests.callee 1) {}, .ret],
    links := [(3, .direct 1)], locals := [], returnsValue := true }
def rewritten : Method :=
  { caller with code := [.unadmitted 0, .throw (some .baseException),
      .ldarg 0, .call (Tests.callee 1) {}, .ret], links := [(3, .direct 1)] }

abbrev calling : Nat → Nat → Prop := fun method pc => inStarts [(0, 2), (1, 0)] method pc = true

theorem calling_run (fuel : Nat) (args stack : List Value) (frame : Frame) (m : Memory) :
    run [rewritten, helper] fuel 0 2 args frame stack m = run [caller, helper] fuel 0 2 args frame stack m :=
  run_congr_region (program := [caller, helper]) (region := calling) (RegionClosed.of_check (by decide))
    (AgreesOn.set (program := [caller, helper]) (index := 0) rfl rewritten.code fun _ inside =>
      code_agrees_of_drop (lower := 2) rfl (by simpa [calling, inStarts] using inside)) _ _ _ _ _ _ _ (by decide)

/-- A branch back into the prefix leaves the region. -/
example : regionClosedCheck [caller.withCode [.ldc_i4 0, .ret, .br 0]] [(0, 2)] = false := by
  decide

/-- A call into a method the region does not cover from pc 0 leaves it. -/
example : regionClosedCheck [caller, helper] [(0, 2)] = false := by decide

/-- A whole method of straight-line code is closed. -/
example : regionClosedCheck [caller.withCode [.ldc_i4 0, .ldc_i4 1, .ret]] [(0, 0)] = true := by
  decide

def longSuffix : List Instruction :=
  List.replicate 96 .nop ++ [.brfalse 102, .switch [3, 102], .bge 102, .ret]

def longExpected (profile : CIL.FeatureProfile) : Method :=
  { code := [.ldarg 0, .ldc_i4 6, .shr] ++ longSuffix, locals := [], returnsValue := true,
    profile := profile }

def longMasked (profile : CIL.FeatureProfile) : Method :=
  (longExpected profile).withCode
    (List.replicate 3 (.unadmitted 0) ++ longSuffix)

def longActual (profile : CIL.FeatureProfile) (callee : Nat) : Method :=
  { (longExpected profile).withCode ([.ldarg 0, .call (Tests.callee 1)] ++ longSuffix.map
      (Instruction.relabel (fun pc => pc - 3 + 2))) with
    links := [(1, .direct callee)] }

theorem longSuffix_length : longSuffix.length = 100 := by simp [longSuffix]

/-- The expected body calls nothing, so its link table is empty. -/
theorem longExpected_links (profile : CIL.FeatureProfile) :
    (longExpected profile).links = [] := rfl

#print axioms longExpected_links

theorem longSuffix_refines (profile : CIL.FeatureProfile) (callee : Nat) :
    CIL.Embedding.BodyRefines (longMasked profile) (longActual profile callee)
      (CIL.Embedding.suffixRename 3 2) := by
  apply CIL.Embedding.BodyRefines.of_relocated_suffix
  · rfl
  · rfl
  · omega
  · intro pc op before found
    have lookup : (longMasked profile).code[pc]? = some (.unadmitted 0) := by
      exact (List.getElem?_append_left (l₁ := List.replicate 3 (.unadmitted 0))
        (l₂ := longSuffix) (by simpa only [List.length_replicate] using before)).trans
          (List.getElem?_replicate_of_lt before)
    rw [lookup] at found
    cases found
    rfl
  · simp [longActual, longMasked, Method.withCode]
  · simp only [longMasked, Method.withCode, List.drop_append, List.length_replicate,
      Nat.sub_self, List.drop_zero, List.drop_replicate, List.replicate_zero, List.nil_append]
    intro op member target inside
    simp only [longSuffix, List.mem_append, List.mem_replicate, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with ⟨_, rfl⟩ | rfl | rfl | rfl | rfl <;>
      simp_all [Instruction.targets] <;> omega
  · intro pc after
    rfl
  · exact CIL.Embedding.links_of_shifted_table (expectedBefore := []) (expectedAfter := [])
      (actualBefore := [(1, .direct callee)]) rfl rfl nofun (by simp) nofun

/-- A call inside the relocated suffix keeps its link at the shifted pc. -/
def callExpected : Method :=
  { code := [.ldarg 0, .ldc_i4 6, .shr, .ldarg 1, .call (Tests.callee 1) {}, .ret],
    links := [(4, .direct 2)], locals := [], returnsValue := true }

def callMasked : Method :=
  { callExpected.withCode (List.replicate 3 (.unadmitted 0) ++ callExpected.code.drop
    3) with links := callExpected.links }

/-- A call to method 1 replaces the masked prefix, and the suffix's call moves to pc 3. -/
def callActual : Method :=
  { callExpected.withCode ([.ldarg 0, .call (Tests.callee 1)] ++ callExpected.code.drop
    3) with links := [(1, .direct 1), (3, .direct 2)] }

theorem callSuffix_refines :
    CIL.Embedding.BodyRefines callMasked callActual (CIL.Embedding.suffixRename 3 2) := by
  apply CIL.Embedding.BodyRefines.of_relocated_suffix
  · rfl
  · rfl
  · omega
  · intro pc op before found
    have unmasked : pc = 0 ∨ pc = 1 ∨ pc = 2 := by omega
    rcases unmasked with rfl | rfl | rfl <;>
      (simp [callMasked, Method.withCode] at found; subst found; rfl)
  · rfl
  · intro op member target inside
    simp [callMasked, callExpected, Method.withCode] at member
    rcases member with rfl | rfl | rfl <;> simp [Instruction.targets] at inside
  · intro pc after
    rfl
  · exact CIL.Embedding.links_of_shifted_table (expectedBefore := [])
      (expectedAfter := [(4, .direct 2)]) (actualBefore := [(1, .direct 1)]) rfl rfl nofun
      (by simp) (by simp)

#print axioms callSuffix_refines

theorem longSuffix_moves (profile : CIL.FeatureProfile) (callee fuel : Nat) (args stack : List Value)
    (frame : Frame) (m : Memory) (result : Memory × List Value)
    (ran : run [longExpected profile] fuel 0 3 args frame stack m = .ok result) :
    run [longActual profile callee] fuel 0 2 args frame stack m = .ok result := by
  have closed : RegionClosed [longExpected profile] suffix := RegionClosed.of_check (by rfl)
  have agrees : AgreesOn [longExpected profile] [longMasked profile] suffix :=
    AgreesOn.set (program := [longExpected profile]) (index := 0) rfl (longMasked profile).code fun _ inside =>
      code_agrees_of_drop (lower := 3) (by simp [longMasked, longExpected, Method.withCode])
        (by simpa [suffix, inStarts] using inside)
  rw [← run_congr_region closed agrees _ _ _ _ _ _ _ (by decide)] at ran
  exact run_refines ((ProgramRefines.refl [longActual profile callee]).set_body (index := 0) rfl
    (longSuffix_refines profile callee)) fuel 0 3 args frame stack m result ran

#print axioms CIL.Embedding.BodyRefines.of_relocated_suffix
#print axioms longSuffix_refines
#print axioms longSuffix_moves
#print axioms run_congr_region
#print axioms RegionClosed.of_check
#print axioms AgreesOn.set
#print axioms suffix_moves

/-- Repeated and overlapping starts describe one union, independent of input order. -/
theorem duplicateStarts :
    regionClosedCheck [caller, helper] [(0, 4), (1, 0), (0, 2), (0, 2)] = true := by
  decide +kernel
#print axioms duplicateStarts

/-- A later duplicate cannot hide the earlier suffix's escaping branch. -/
theorem earlierStartRejects : regionClosedCheck
    [caller.withCode [.ret, .br 0, .ret]] [(0, 2), (0, 1)] = false := by
  decide +kernel
#print axioms earlierStartRejects

/-- Region closure concerns existing instructions, even when starts name absent methods. -/
theorem absentAndEmpty : regionClosedCheck [caller, helper] [(99, 0), (0, 999)] = true := by
  decide +kernel
#print axioms absentAndEmpty

/-- A listed absent callee still belongs to the region; execution separately rejects it. -/
theorem absentCallee : regionClosedCheck
    [{ caller.withCode [.call (Tests.callee 0), .ret] with links := [(0, .direct 99)] }]
    [(0, 0), (99, 0)] = true := by
  decide +kernel
#print axioms absentCallee

/-- No code is checked for an empty region. -/
theorem emptyStarts : regionClosedCheck [caller, helper] [] = true := by decide +kernel
#print axioms emptyStarts
/-- Region membership extends past the body; execution checks instruction availability. -/
theorem finalFallthrough : regionClosedCheck
    [caller.withCode [.nop]] [(0, 0)] = true := by decide +kernel
#print axioms finalFallthrough
end Tests.RegionRun
