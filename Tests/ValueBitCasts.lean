import CIL.Safety.ValueBitCasts
import Examples.Support

namespace Tests.ValueBitCasts
open CIL CIL.Safety

def cells : List (BitVec 8 × Bool) :=
  (List.range 16).map fun i => (BitVec.ofNat 8 (17 * i), i % 2 == 0)

def memory : CIL.Safety.Memory := {
  Examples.empty with
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨16, 1, []⟩, true, [16]⟩ else none
  nextIdentity := 1
  views := [⟨0, 0, 16, true, true⟩]
  cells := fun _ i => ⟨BitVec.ofNat 8 (17 * i), i % 2 == 0⟩ }

example : bitcastValue (.aggregate 16) .vector128 (.snapshot (.aggregate 16) cells) =
    .ok (.snapshot .vector128 cells) := by rfl

example : bitcastValue .vector128 (.aggregate 16) (.snapshot .vector128 cells) =
    .ok (.snapshot (.aggregate 16) cells) := by rfl

example : bitcastValue (.aggregate 16) .vector256 (.snapshot (.aggregate 16) cells) =
    .error .invalidState := by rfl

example : bitcastValue (.aggregate 32) .vector256 (.snapshot (.aggregate 32) cells) =
    .error .invalidState := by rfl

example : loadValue memory (.address ⟨0, 0⟩) 16 = .ok (.snapshot .vector128 cells) := by rfl

example : loadValue memory (.address ⟨0, 0⟩) 8 =
    .error (.memory .uninitialized (.address ⟨0, 0⟩) 8) := by rfl

example : loadLocal memory (.bytes (.aggregate 16) ⟨0, 0⟩) =
    .ok (.scalar (.snapshot (.aggregate 16) cells)) := by rfl

example : (do
    let (_, stored) ← storeLocal memory (.bytes .vector128 ⟨0, 0⟩)
      (.scalar (.snapshot .vector128 cells))
    loadLocal stored (.bytes .vector128 ⟨0, 0⟩)) =
    .ok (.scalar (.snapshot .vector128 cells)) := by rfl

example : (do
    let stored ← storeValue memory (.address ⟨0, 0⟩) (.snapshot .vector128 cells)
    loadValue stored (.address ⟨0, 0⟩) 8) =
    .error (.memory .uninitialized (.address ⟨0, 0⟩) 8) := by rfl

example : loadValue memory (.address ⟨0, 1⟩) 16 =
    .error (.memory .outsideAllocation (.address ⟨0, 1⟩) 16) := by rfl

example : checkedIntrinsic (.vector (.equalsAll 128))
    [.snapshot .vector128 cells, .snapshot .vector128 cells] = .error .invalidState := by rfl

example : checkedValue memory (.scalar (.snapshot .vector256 cells)) = .error .invalidState := by rfl

end Tests.ValueBitCasts
