import Extracted
import CIL.MethodIdentity
import CIL.Safety.SymbolicExecution
import CIL.Safety.ObjectFields

/-!
# A struct array held in a class field

`Examples.Tiles` holds its `Pairs`, an array of the 16-byte struct `AggregateArrays.Pair`, in a
field whose slot keeps the origin of the whole array; its element width is the struct's layout,
which the extraction checks. `TileArrays.PairsOf(tiles)` returns `tiles.Pairs`. Proved: when the
field holds a whole live array of `length` pairs it returns that array and changes nothing, and
when it holds null it returns the null array.
-/

open CIL.Safety
open Extracted.Classes
namespace ExampleProof

bind_method pairsOf pairsOfBody :=
  "Examples.AggregateArrays/Pair[] Examples.TileArrays::PairsOf(Examples.Tiles)"

/-- A field holding a whole array of `length` pairs returns that array and changes nothing. -/
theorem correctness (memory : Memory) (tiles pairs : Reference) (length : Nat)
    (readable : Tiles.Pairs.Readable memory tiles)
    (held : Tiles.Pairs.of memory tiles = .address pairs)
    (whole : WholeArray memory Tiles.Pairs.elementType pairs length) :
    ∃ fuel, invoke Extracted.program fuel pairsOf [.object (.address tiles)] memory =
      .ok (memory, [.array ⟨.address pairs, length, Tiles.Pairs.elementType⟩]) := by
  obtain ⟨formed, located, loaded⟩ := readable.facts held whole (by decide)
  cil_checked_steps [formed, located, loaded, whole.valid]

#print axioms correctness

/-- A field holding null returns the null array. -/
theorem null_pairs (memory : Memory) (tiles : Reference)
    (readable : Tiles.Pairs.Readable memory tiles)
    (held : Tiles.Pairs.of memory tiles = .null) :
    ∃ fuel, invoke Extracted.program fuel pairsOf [.object (.address tiles)] memory =
      .ok (memory, [.array ⟨.null, 0, Tiles.Pairs.elementType⟩]) := by
  cil_checked_steps [readable.live.formed, readable.located, readable.load_null held rfl]

#print axioms null_pairs

end ExampleProof