import CIL.Crypto.Sha1
import Lean

/-!
# Core hash operations

SHA-1 is available without the image audit library. Reference digests cover increasing key
lengths, and repeated evaluations check that hashing cost grows linearly with the byte count.
-/

namespace Tests.Crypto

open CIL.Crypto

run_elab
  if (← Lean.getEnv).contains `StrictBinding.ImageBytes then
    throwError "Core SHA-1 imports the image audit library"

/-- The empty message has the FIPS 180-4 SHA-1 digest. -/
theorem empty_digest : Sha1.ofBytes [] = 0xda39a3ee5e6b4b0d3255bfef95601890afd80709 := by
  decide +kernel

#print axioms empty_digest

/-- The least of three timings for repeated hashing of a fixed byte pattern. -/
def measureHash (bytes : List Nat) (expected : Nat) : IO Nat := do
  let mut best := 1000000000000
  for _ in [:3] do
    let started ← IO.monoNanosNow
    for _ in [:16] do
      unless Sha1.ofBytes bytes == expected do
        throw (IO.userError "SHA-1 differs from the reference digest")
    best := min best ((← IO.monoNanosNow) - started)
  return best

/-- Eightfold input growth stays below quadratic hashing cost. -/
def checkHashCost : IO Unit := do
  let cases := [(64, 0xc6138d514ffa2135bfce0ed0b8fac65669917ec7),
    (512, 0xdbe649daba340bce7a44b809016d914839b99f10),
    (4096, 0xe9dded8c84614e894501965af60c2525794a8c7d)]
  let mut previous := 0
  for (count, expected) in cases do
    let bytes := (List.range count).map (· % 256)
    let elapsed ← measureHash bytes expected
    if previous > 0 && elapsed > previous * 24 + 2000000 then
      throw (IO.userError s!"SHA-1 cost grew too quickly: {previous} -> {elapsed}")
    IO.println s!"PASS SHA-1 {count} bytes: {elapsed} ns"
    previous := elapsed

#eval checkHashCost

end Tests.Crypto
