import CIL

/-!
# Literal display tests

Pins how goals print bit-vector literals: values of `2 ^ 16` or more in hexadecimal, smaller
ones in decimal, and either form elaborating back to the same term.
-/

namespace Tests.LiteralDisplay

open CIL (W32 W64)

-- A spec's mask prints as written, in both the numeral and the `#w` form.
/-- info: fun count => count ||| 0x80000000 : W32 → W32 -/
#guard_msgs in
#check fun count : W32 => count ||| 0x80000000

/-- info: 0x80000000#32 : BitVec 32 -/
#guard_msgs in
#check BitVec.ofNat 32 2147483648

/-- info: 0x9E3779B97F4A7C15#64 : BitVec 64 -/
#guard_msgs in
#check (0x9E3779B97F4A7C15#64 : W64)

-- Counts and indexes below the threshold stay decimal, as does every `Nat`.
/-- info: (5#32, 65535) : BitVec 32 × W32 -/
#guard_msgs in
#check ((5#32, 65535) : BitVec 32 × W32)

/-- info: 0x10000 : W32 -/
#guard_msgs in
#check (65536 : W32)

/-- info: 2147483648 : Nat -/
#guard_msgs in
#check (2147483648 : Nat)

-- The printed form is the same term, so a goal copied from the display elaborates back to it.
example : (0x80000000#32 : W32) = BitVec.ofNat 32 2147483648 := rfl
example : (0x80000000 : W32) = @OfNat.ofNat W32 2147483648 _ := rfl

end Tests.LiteralDisplay
