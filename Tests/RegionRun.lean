import CIL.Safety.RegionRun
import CIL.Safety.Embedding.Simulation
import CIL.Safety.Embedding.Suffix

/-! A suffix run moves to a body whose prefix is a call instead of inline code. -/
namespace Tests.RegionRun

open CIL (Method Op Embeds)
open CIL.Safety

def helper : Method := { code := [.arg 0, .const32 6, .shr, .ret], locals := [], returnsValue := true }

/-- Computes `count >> 6` inline, then adds one. -/
def expected : Method := { code := [.arg 0, .const32 6, .shr, .const32 1, .add, .ret], locals := [], returnsValue := true }

/-- The same suffix after a compiled helper call, one pc earlier. -/
def actual : Method := { code := [.arg 0, .call 1 1, .const32 1, .add, .ret], locals := [], returnsValue := true }

def masked : Method :=
  { expected with code := List.replicate 3 (.unsupported "Outside the region") ++ expected.code.drop 3 }

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
def caller : Method := { code := [.const32 5, .ret, .arg 0, .call 1 1, .ret], locals := [], returnsValue := true }
def rewritten : Method := { caller with code := [.unsupported "Outside the region", .throw "System.Exception", .arg 0, .call 1 1, .ret] }

abbrev calling : Nat → Nat → Prop := fun method pc => inStarts [(0, 2), (1, 0)] method pc = true

theorem calling_run (fuel : Nat) (args stack : List Value) (frame : Frame) (m : Memory) :
    run [rewritten, helper] fuel 0 2 args frame stack m = run [caller, helper] fuel 0 2 args frame stack m :=
  run_congr_region (program := [caller, helper]) (region := calling) (RegionClosed.of_check (by decide))
    (AgreesOn.set (program := [caller, helper]) (index := 0) rfl rewritten.code fun _ inside =>
      code_agrees_of_drop (lower := 2) rfl (by simpa [calling, inStarts] using inside)) _ _ _ _ _ _ _ (by decide)

/-- A branch back into the prefix leaves the region. -/
example : regionClosedCheck [{ caller with code := [.const32 0, .ret, .branch 0] }] [(0, 2)] = false := by decide

/-- A call into a method the region does not cover from pc 0 leaves it. -/
example : regionClosedCheck [caller, helper] [(0, 2)] = false := by decide

/-- A whole method of straight-line code is closed. -/
example : regionClosedCheck [{ caller with code := [.const32 0, .const32 1, .ret] }] [(0, 0)] = true := by decide

def longSuffix : List Op :=
  List.replicate 96 .nop ++ [.brzero 102, .switch [3, 102], .nativeBinary (.bge 102), .ret]

def longExpected (profile : CIL.FeatureProfile) : Method :=
  { code := [.arg 0, .const32 6, .shr] ++ longSuffix, locals := [], returnsValue := true, profile := profile }

def longMasked (profile : CIL.FeatureProfile) : Method :=
  { longExpected profile with code := List.replicate 3 (.unsupported "Outside the region") ++ longSuffix }

def longActual (profile : CIL.FeatureProfile) (callee : Nat) : Method :=
  { longExpected profile with code := [.arg 0, .call callee 1] ++
      longSuffix.map (Op.relabel (fun pc => pc - 3 + 2)) }

theorem longSuffix_length : longSuffix.length = 100 := by simp [longSuffix]

theorem longSuffix_refines (profile : CIL.FeatureProfile) (callee : Nat) :
    CIL.Embedding.BodyRefines (longMasked profile) (longActual profile callee)
      (CIL.Embedding.suffixRename 3 2) := by
  apply CIL.Embedding.BodyRefines.of_relocated_suffix
  · rfl
  · rfl
  · omega
  · intro pc op before found
    have lookup : (longMasked profile).code[pc]? = some (.unsupported "Outside the region") := by
      simp only [longMasked]
      rw [List.getElem?_append_left (by simpa using before)]
      simp [List.getElem?_replicate, before]
    rw [lookup] at found
    cases found
    rfl
  · simp [longActual, longMasked]
  · simp only [longMasked, List.drop_append, List.length_replicate, Nat.sub_self, List.drop_zero,
      List.drop_replicate, List.replicate_zero, List.nil_append]
    intro op member target inside
    simp only [longSuffix, List.mem_append, List.mem_replicate, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at member
    rcases member with ⟨_, rfl⟩ | rfl | rfl | rfl | rfl <;> simp_all [Op.targets]
  · intro pc after
    rfl

theorem longSuffix_moves (profile : CIL.FeatureProfile) (callee fuel : Nat) (args stack : List Value)
    (frame : Frame) (m : Memory) (result : Memory × List Value)
    (ran : run [longExpected profile] fuel 0 3 args frame stack m = .ok result) :
    run [longActual profile callee] fuel 0 2 args frame stack m = .ok result := by
  have closed : RegionClosed [longExpected profile] suffix := RegionClosed.of_check (by decide)
  have agrees : AgreesOn [longExpected profile] [longMasked profile] suffix :=
    AgreesOn.set (program := [longExpected profile]) (index := 0) rfl (longMasked profile).code fun _ inside =>
      code_agrees_of_drop (lower := 3) (by simp [longMasked, longExpected])
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

end Tests.RegionRun
