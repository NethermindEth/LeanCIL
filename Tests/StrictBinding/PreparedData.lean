import Lean

/-! Constructor data for the closed preparations that strict binding fixture checks share. -/

namespace Tests.StrictBinding

open Lean Elab Term Meta in
/-- The constructor data of a closed image preparation. -/
scoped elab "prepared_data% " value:term : term => do
  let term ← Term.elabTermAndSynthesize value none
  -- The image stores its bytes in 512-bit chunks.
  withOptions (exponentiation.threshold.set · 512) do
    withTransparency .all (reduce (← instantiateMVars term))

end Tests.StrictBinding
