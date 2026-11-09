import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields

/-!
# The length of a struct array held in a class field

`TileArrays.PairCount(tiles)` returns `tiles.Pairs.Length`. The field's slot names a whole array
of 16-byte pairs, so `ldlen` reads the length the allocation's size gives. Proved: for a whole
live array of `length` pairs it returns `length` and changes nothing, and for a null field it
throws `NullReferenceException` at the `ldlen`.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

bind_method pairCount pairCountBody := "System.Int32 Examples.TileArrays::PairCount(Examples.Tiles)"

/-- A field holding a whole array of `length` pairs returns `length` and changes nothing. -/
theorem correctness (memory : Memory) (tiles pairs : Reference) (length : Nat)
    (readable : Tiles.Pairs.Readable memory tiles)
    (held : Tiles.Pairs.of memory tiles = .address pairs)
    (whole : WholeArray memory Tiles.Pairs.elementType pairs length) :
    ∃ fuel, invoke Extracted.program fuel pairCount [.object (.address tiles)] memory =
      .ok (memory, [.scalar (.i32 (BitVec.ofNat 32 length))]) := by
  obtain ⟨formed, located, loaded⟩ := readable.facts held whole (by decide)
  refine ⟨CIL.executionBound Extracted.program pairCount, ?_⟩
  cil_checked_steps [formed, located, loaded, whole.valid, leaveFrame]

#print axioms correctness

/-- A field holding null throws `NullReferenceException` at the `ldlen`, pc 2. -/
theorem null_pairs (memory : Memory) (tiles : Reference)
    (readable : Tiles.Pairs.Readable memory tiles)
    (held : Tiles.Pairs.of memory tiles = .null) :
    ∃ fuel, invoke Extracted.program fuel pairCount [.object (.address tiles)] memory =
      .error ⟨pairCount, 2, .thrown "System.NullReferenceException"⟩ := by
  refine ⟨CIL.executionBound Extracted.program pairCount, ?_⟩
  cil_checked_steps [readable.live.formed, readable.located, readable.load_null held rfl]

#print axioms null_pairs

end ExampleProof