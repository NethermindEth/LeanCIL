import CIL.Safety.CallingFields
import CIL.Safety.LoopFrames
import CIL.Safety.CallSegments

/-!
# Checked by-reference field evidence

These fixtures take two four-word inputs and a writable output, with arbitrary overlap.
The stepper obtains field reads and formed references from `ValidCall` itself.
-/

namespace Tests.CallingFields
open CIL.Safety

/-- A four-word argument range. -/
def words (reference : Reference) : ArgumentView := ⟨reference, 32⟩

/-- Read every input field before any output could be written. -/
@[cil_code] def reader : CIL.Method :=
  { locals := [], returnsValue := true, code := [
    .arg 2, .skipInit,
    .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 0 8, .add,
    .arg 0, .fieldAt 8 8, .arg 1, .fieldAt 8 8, .add, .add,
    .arg 0, .fieldAt 16 8, .arg 1, .fieldAt 16 8, .add, .add,
    .arg 0, .fieldAt 24 8, .arg 1, .fieldAt 24 8, .add, .add, .ret] }

/-- Field evidence is gathered with no per-field hypotheses or stepper arguments. -/
theorem reads_four_words (memory : Memory) (left right output : Reference)
    (call : ValidCall memory [words left, words right] [words output]) :
    WP (fun fuel => invoke [reader] fuel 0
      [.reference (.address left), .reference (.address right),
        .reference (.address output)] memory)
      (fun final values => final = memory ∧ values = [.scalar (.i64 (
        ((words left).word memory 0 + (words right).word memory 0) +
        ((words left).word memory 8 + (words right).word memory 8) +
        ((words left).word memory 16 + (words right).word memory 16) +
        ((words left).word memory 24 + (words right).word memory 24)))]) := by
  cil_contract_steps []
  exact ⟨rfl, rfl⟩

#print axioms reads_four_words

/-- The same proof allows the output to be exactly the left input. -/
theorem overlapping_read (memory : Memory) (left right : Reference)
    (call : ValidCall memory [words left, words right] [words left]) :
    WP (fun fuel => invoke [reader] fuel 0
      [.reference (.address left), .reference (.address right), .reference (.address left)] memory)
      (fun final _ => final = memory) :=
  (reads_four_words memory left right left call).consequence (fun _ _ result => result.1)

#print axioms overlapping_read

/-- Sum all input words and write the result only after reading every input. -/
@[cil_code] def writer : CIL.Method :=
  { locals := [], returnsValue := false,
    code := [.arg 2] ++ reader.code.dropLast ++ [.store64, .ret] }

/-- The checksum uses the original input snapshots, including when output overlaps an input. -/
def checksum (memory : Memory) (left right : Reference) : CIL.W64 :=
  ((words left).word memory 0 + (words right).word memory 0) +
  ((words left).word memory 8 + (words right).word memory 8) +
  ((words left).word memory 16 + (words right).word memory 16) +
  ((words left).word memory 24 + (words right).word memory 24)

/-- Output requires write access, not initial contents or separation from either input. -/
theorem writes_after_reads (memory : Memory) (left right output : Reference)
    (call : ValidCall memory [words left, words right] [words output]) :
    WP (fun fuel => invoke [writer] fuel 0
      [.reference (.address left), .reference (.address right),
        .reference (.address output)] memory)
      (fun final values => values = [] ∧
        read final output 8 1 = .ok (numberBytes (checksum memory left right).toNat 8) ∧
        ValidCall final [words left, words right] [words output]) := by
  have ready : access memory output 8 1 true = .ok () := by
    simpa only [words, Nat.add_zero] using
      call.output_slice (words output) (by simp) 0 8 (by decide) (by simp [words])
  obtain ⟨final, written, _, readback⟩ := store_word64 (checksum memory left right) ready
  have stored := step_store64_of_write written
  simp only [checksum, words] at stored
  cil_contract_steps [stored]
  exact ⟨rfl, readback, call.after_write written⟩

#print axioms writes_after_reads

/-- The two scalar helpers differ only in their checked arithmetic instruction. -/
@[cil_code] def helper (subtract : Bool) : CIL.Method :=
  { locals := [], returnsValue := true,
    code := [.arg 0, .arg 1, if subtract then .sub else .add, .ret] }

/-- A helper preserves memory and returns its specified wrapping arithmetic result. -/
def arithmetic (subtract : Bool) : MethodContract (CIL.W64 × CIL.W64) CIL.W64 where
  args input := [.scalar (.i64 input.1), .scalar (.i64 input.2)]
  results value := [.scalar (.i64 value)]
  pre _ _ := True
  footprint _ := []
  post input initial final value := final = initial ∧
    value = if subtract then input.1 - input.2 else input.1 + input.2

/-- Each helper contract is proved against its instructions in the actual program. -/
theorem helper_checked (subtract : Bool) {program : CIL.Program} {callee : Nat}
    (found : program[callee]? = some (helper subtract)) :
    (arithmetic subtract).Holds program callee := by
  intro input memory _
  cases subtract <;> cil_contract_steps [found, helper, arithmetic]
  all_goals exact ⟨Confined.refl [] memory, _, rfl, rfl, rfl⟩

#print axioms helper_checked

/-- Both helper choices share the same caller segment and return convention. -/
@[cil_code] def caller (callee : Nat) : CIL.Method :=
  { locals := [], returnsValue := false, code := loadCallStoreCode callee ++ [.ret] }

/-- The shared segment writes the chosen operation on the original input snapshots. -/
def Composed (subtract : Bool) : Prop :=
  ∀ (memory : Memory) (left right output : Reference),
    ValidCall memory [⟨left, 8⟩, ⟨right, 8⟩] [⟨output, 8⟩] →
    WP (fun fuel => run [caller 1, helper subtract] fuel 0 0
      [.reference (.address left), .reference (.address right), .reference (.address output)]
      { activation := 0, locals := [], owned := [] } [] memory)
      (fun final values => values = [] ∧
        read final output 8 1 = .ok (numberBytes
          ((if subtract then
            (⟨left, 8⟩ : ArgumentView).word memory 0 -
              (⟨right, 8⟩ : ArgumentView).word memory 0
          else (⟨left, 8⟩ : ArgumentView).word memory 0 +
              (⟨right, 8⟩ : ArgumentView).word memory 0)).toNat 8))

/-- One caller proof composes either checked helper, including overlapping output. -/
theorem composed (subtract : Bool) : Composed subtract := by
  intro memory left right output call
  apply WP.load_call_store (helper_checked subtract rfl)
    ((⟨left, 8⟩ : ArgumentView).word memory 0,
      (⟨right, 8⟩ : ArgumentView).word memory 0) id left right output
    rfl (by rfl) call rfl trivial (fun _ => rfl)
  intro middle value after result written
  have readback := write_readback _ _ _ _ _ written
  simp only [numberBytes, List.length_map, List.length_range] at readback
  have value_eq := result.post.2
  cil_contract_steps [caller]
  exact ⟨rfl, value_eq ▸ readback⟩

#print axioms composed

/-- Addition instantiates the shared segment with the addition contract. -/
theorem composed_add : Composed false := composed false

#print axioms composed_add

/-- Subtraction instantiates the same segment with the subtraction contract. -/
theorem composed_subtract : Composed true := composed true

#print axioms composed_subtract

end Tests.CallingFields
