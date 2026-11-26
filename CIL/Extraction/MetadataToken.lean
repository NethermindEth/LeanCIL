/-!
# Metadata tokens

The extraction checker and image auditor use the low three bytes of a token for the row.
-/

namespace CIL.Extraction

/-- The table number of a token: its top byte. -/
def metadataTableOf (token : Nat) : Nat := token / 0x1000000

/-- The row number of a token: its low three bytes. -/
def tokenRow (token : Nat) : Nat := token % 0x1000000

/-- The token of a table and a row already known to fit in 24 bits. -/
def tokenOf (table row : Nat) : Nat := table * 0x1000000 + row

/-- A row must fit below the table byte. Each caller interprets row zero. -/
def checkedTokenOf (table row : Nat) (overflow : Nat → Nat → ε) : Except ε Nat :=
  if row < 0x1000000 then .ok (tokenOf table row) else .error (overflow table row)

end CIL.Extraction
