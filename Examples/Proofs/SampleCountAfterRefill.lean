import Extracted
import CIL.MethodIdentity
import CIL.Safety.ObjectFields
import CIL.Safety.SymbolicExecution

/-!
# Reading an array field after a call that may replace it

`SampleArrays.CountAfterRefill(samples, other, values)` calls `Refill(other, values)`, then
returns the length of the array `samples.Values` holds. The two holders may be the same
instance, so the proof composes the call through its contract and decides the aliasing of
`samples.Values` across it with `Readable.across`; whichever array the field then holds is
still whole after the call (`WholeArray.after_confined`).
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

bind_method countAfterRefill countAfterRefillBody :=
  "System.Int32 Examples.SampleArrays::CountAfterRefill(Examples.Samples,Examples.Samples,\
System.Int32[])"
bind_callee refill refillBody :=
  "System.Void Examples.SampleArrays::Refill(Examples.Samples,System.Int32[])"
  from countAfterRefillBody [0]

/-- `Refill(samples, values)` leaves `samples.Values` holding the origin of the whole array of
    `length` integers it is given, and changes nothing else. -/
def refillContract : MethodContract (Reference × Reference × Nat) where
  args := fun (samples, values, length) =>
    [.object (.address samples), .array ⟨.address values, length, .signed32⟩]
  pre := fun (samples, values, length) memory => Samples.Values.Owned memory samples ∧
    WholeArray memory .signed32 values length
  footprint := fun (samples, _, _) => [Samples.Values.entry samples]
  post := fun (samples, values, _) _ final results => results = [] ∧
    Samples.Values.Holds final samples (.address values)

/-- `Refill` meets its contract: one `stfld` of the field's slot. -/
theorem refill_holds : refillContract.Holds Extracted.program refill := by
  rintro ⟨samples, values, length⟩ memory ⟨owned, whole⟩
  obtain ⟨stored, framed, held⟩ := owned.store_whole whole
  refine MethodContract.Holds.intro _ [] ?_ framed ⟨rfl, held⟩
  cil_checked_steps [stored, whole.valid]

#print axioms refill_holds

/-- The inputs of `CountAfterRefill`: the holder counted, the holder refilled, the new array,
    the array the counted holder holds before the call, and the two arrays' lengths. -/
abbrev Holders := Reference × Reference × Reference × Reference × Nat × Nat

/-- `CountAfterRefill(samples, other, values)` leaves `other.Values` holding `values` and
    returns the length of `values` when the two holders are the same instance, and of the
    array `samples.Values` held before the call otherwise. -/
def countContract : MethodContract Holders where
  args := fun (samples, other, values, _, length, _) =>
    [.object (.address samples), .object (.address other),
      .array ⟨.address values, length, .signed32⟩]
  pre := fun (samples, other, values, current, length, currentLength) memory =>
    Samples.Values.Readable memory samples ∧
      Samples.Values.of memory samples = .address current ∧
      WholeArray memory .signed32 current currentLength ∧
      Samples.Values.Owned memory other ∧ WholeArray memory .signed32 values length
  footprint := fun (_, other, _, _, _, _) => [Samples.Values.entry other]
  post := fun (samples, other, values, _, length, currentLength) _ final results =>
    results = [.scalar (.i32 (BitVec.ofNat 32
        (if other = samples then length else currentLength)))] ∧
      Samples.Values.Holds final other (.address values)

/-- `CountAfterRefill` meets its contract given only the contract of `Refill`. -/
theorem count_holds (holds : refillContract.Holds Extracted.program refill) :
    countContract.Holds Extracted.program countAfterRefill := by
  rintro ⟨samples, other, values, current, length, currentLength⟩ memory
    ⟨readable, held, currentWhole, owned, valuesWhole⟩
  cil_contract_steps [holds, refillContract, owned, valuesWhole, valuesWhole.valid]
    with final results refilling
  have framed := refilling.framed
  have post := refilling.post
  dsimp only [refillContract] at framed post
  obtain ⟨rfl, refilled⟩ := post
  obtain ⟨kept, now⟩ := readable.across owned.toReadable.live framed refilled
  by_cases same : other = samples
  · simp only [same, ite_true] at now ⊢
    obtain ⟨formed, located, loaded⟩ :=
      kept.facts now (valuesWhole.after_confined framed) (by decide)
    cil_contract_steps [formed, located, loaded, (valuesWhole.after_confined framed).valid]
    subst same
    refine ⟨framed, _, rfl, ?_, refilled⟩
    simp
  · simp only [same, ite_false, held] at now ⊢
    obtain ⟨formed, located, loaded⟩ :=
      kept.facts now (currentWhole.after_confined framed) (by decide)
    cil_contract_steps [formed, located, loaded, (currentWhole.after_confined framed).valid]
    refine ⟨framed, _, rfl, ?_, refilled⟩
    simp [same]

#print axioms count_holds

/-- `CountAfterRefill` meets its contract, with `Refill` discharged by its own proof. -/
theorem correctness : countContract.Holds Extracted.program countAfterRefill :=
  count_holds refill_holds

#print axioms correctness

end ExampleProof
