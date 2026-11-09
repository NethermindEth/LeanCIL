import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields

/-!
# Replacing a vector array held in a class field

`TileArrays.Relane(tiles, lanes)` stores the `Vector128<ulong>[]` `lanes` into `tiles.Lanes`,
whose element width the vector type fixes. Proved: its contract, for a whole live heap array,
with the field's slot as its whole footprint and the array's origin as what the field then
holds.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

bind_method relane relaneBody :=
  "System.Void Examples.TileArrays::Relane(Examples.Tiles,\
System.Runtime.Intrinsics.Vector128`1<System.UInt64>[])"

/-- `Relane(tiles, lanes)` leaves `tiles.Lanes` holding the origin of the whole array of
    `length` vectors it is given, and changes nothing else. -/
def relaneContract : MethodContract (Reference × Reference × Nat) where
  args := fun (tiles, lanes, length) =>
    [.object (.address tiles), .array ⟨.address lanes, length, Tiles.Lanes.elementType⟩]
  pre := fun (tiles, lanes, length) memory => Tiles.Lanes.Owned memory tiles ∧
    WholeArray memory Tiles.Lanes.elementType lanes length
  footprint := fun (tiles, _, _) => [Tiles.Lanes.entry tiles]
  post := fun (tiles, lanes, _) _ final results => results = [] ∧
    Tiles.Lanes.Holds final tiles (.address lanes)

/-- `Relane` meets its contract: one `stfld` of the field's slot. -/
theorem correctness : relaneContract.Holds Extracted.program relane := by
  rintro ⟨tiles, lanes, length⟩ memory ⟨owned, whole⟩
  dsimp only [relaneContract] at *
  obtain ⟨stored, framed, held⟩ := owned.store_whole whole
  refine ⟨CIL.executionBound Extracted.program relane, _, [], ?_, framed, [], rfl, rfl, held⟩
  cil_checked_steps [owned.live.formed, owned.located, stored, whole.valid]

#print axioms correctness

end ExampleProof