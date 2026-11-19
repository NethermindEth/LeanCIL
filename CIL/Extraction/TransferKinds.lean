import CIL.Extraction.CallLayouts

/-! # Transfer kinds of runtime model elements

The memory transfer a runtime model performs for a value type, read through the layout reader of
the checked layouts.
Vectors are admitted only in the integer element family the base's transfer matchers admit.
-/

namespace CIL

/-- How a value of `type` moves through memory under the layout reader `reader`: a primitive as a
    scalar of its width and signedness, an integer-element vector or a struct in the layouts as a
    snapshot of its checked size, and `none` for every other type. -/
def transferKind? (reader : Extraction.CallLayouts) (type : Extraction.TypeExpr) :
    Option TransferKind :=
  match reader.valueShape type with
  | .primitive width signed => some (.scalar width signed)
  | .vector bytes =>
    if Extraction.integerVectorWidth type != some bytes then none
    else match bytes with
      | 16 => some (.snapshot .vector128)
      | 32 => some (.snapshot .vector256)
      | 64 => some (.snapshot .vector512)
      | _ => none
  | .aggregate size => some (.snapshot (.aggregate size))
  | _ => none

end CIL
