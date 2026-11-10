import Extracted
import CIL.Verification
import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.LoopScaffold
import CIL.Safety.ObjectFields

/-!
# An instance call in a loop

`Objects.DepositTimes(account, amount, times)` calls `account.Deposit(amount)` through `callvirt`
once per iteration of a counted loop. The loop tactics cross each call through `Deposit`'s
contract and carry the invariant's `Account.Balance.Holds` fact across the counter's store; the
proof supplies the invariant, the measure and the arithmetic.
-/

open CIL.Safety
open CIL (W32 W64)
open Extracted.Classes
namespace ExampleProof

bind_method depositTimes depositTimesBody :=
  "System.Void Examples.Objects::DepositTimes(Examples.Account,System.UInt64,System.UInt32)"
bind_callee deposit depositBody :=
  "System.Void Examples.Account::Deposit(System.UInt64)" from depositTimesBody
bind_call depositSite := deposit from depositTimesBody

/-- `account.Deposit(amount)` adds `amount` to `Balance` and writes nothing else. -/
def depositContract : MethodContract (Reference × W64) where
  args := fun (account, amount) => [.object (.address account), .scalar (.i64 amount)]
  pre := fun (account, _) memory => Account.Balance.Owned memory account
  footprint := fun (account, _) => [Account.Balance.entry account]
  post := fun (account, amount) initial final values => values = [] ∧
    Account.Balance.Holds final account (Account.Balance.of initial account + amount)

/-- `Deposit` meets its contract for every live account and amount. -/
theorem deposit_holds : depositContract.Holds Extracted.program deposit := by
  rintro ⟨account, amount⟩ memory owned
  dsimp only [depositContract] at owned
  obtain ⟨after, written, framed, held⟩ :=
    owned.store (Account.Balance.of memory account + amount)
  refine MethodContract.Holds.intro after [] ?_ framed ⟨rfl, held⟩
  cil_checked_steps [written]

#print axioms deposit_holds

bind_entry entry (memory : Memory) (account : Reference) (amount : W64) (times : W32)
    (wellFormed : memory.WellFormed) :=
  depositTimesBody with [.object (.address account), .scalar (.i64 amount), .scalar (.i32 times)]
    from memory allocating wellFormed
bind_loop loop := depositTimesBody

/-- The calls made so far, held by the frame's only local; the account's balance is the caller
    storage the frame may change. -/
private abbrev State (memory : Memory) (account home : Reference) :=
  FrameState [Account.Balance.entry account] memory [.word32] W32
    (fun _ => [.bytes .word32 home]) fun count => [some (.i32 count)]

/-- The loop test, with the count made and `times` on the stack. -/
bind_cutpoint header (memory : Memory) (account : Reference) (times : W32) (home : Reference)
    (state : State memory account home) :=
  depositTimesBody at loop.latch matching (fun op => op matches .bltu _) with
    entry.frame memory home, [.scalar (.i32 times), .scalar (.i32 state.values)], state.memory

/-- The balance after `count` deposits of `amount` onto `balance`. -/
def deposited (balance amount : W64) (count : W32) : W64 :=
  balance + amount * BitVec.ofNat 64 count.toNat

/-- One more deposit below a 32-bit bound adds `amount` once more. -/
theorem deposited_succ {balance amount : W64} {count bound : W32}
    (below : count.toNat < bound.toNat) :
    deposited balance amount (count + 1) = deposited balance amount count + amount := by
  rw [deposited, deposited, toNat_succ below, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
  simp

#print axioms deposited_succ

/-- `DepositTimes` adds `amount` to the balance `times` times and writes nothing else the caller
    owns. -/
theorem correctness (memory : Memory) (account : Reference) (amount : W64) (times : W32)
    (wellFormed : memory.WellFormed) (owned : Account.Balance.Owned memory account) :
    ∃ fuel final, invoke Extracted.program fuel depositTimes
        [.object (.address account), .scalar (.i64 amount), .scalar (.i32 times)] memory =
      .ok (final, []) ∧
      Account.Balance.Holds final account
        (deposited (Account.Balance.of memory account) amount times) ∧
      Confined [Account.Balance.entry account] memory final := by
  obtain ⟨home, entered, enter⟩ :=
    entry.checked memory account amount times wellFormed
  have old := owned.old
  have enteredHeld := owned.holds.after_below enter.entryMemory.kept old enter.entryMemory.grown
  refine invoke_loop_induction depositTimes.found ?_ enter.setup (header memory account times home)
    (fun state => Account.Balance.Holds state.memory account
        (deposited (Account.Balance.of memory account) amount state.values) ∧
      state.values.toNat ≤ times.toNat)
    (fun state => times.toNat - state.values.toNat) (fun start => ?_) ?_
  · cil_checked_side [owned.live.formed]
  · cil_loop_recurse start 0
    exact ⟨by simpa [deposited] using enteredHeld, Nat.zero_le _⟩
  rintro ⟨count, current, frame⟩ ⟨held, bounded⟩ recurse
  dsimp only at held bounded
  by_cases done : count = times
  · subst done
    cil_loop_finish
  · have below : count.toNat < times.toNat := by
      have : count.toNat ≠ times.toNat := fun same => done (BitVec.eq_of_toNat_eq same)
      omega
    have more : count < times := below
    cil_loop_advance [more]
    have owned := held.1
    cil_loop_call deposit_holds (account, amount) at depositSite
    obtain ⟨rfl, added⟩ := returned
    have held : Account.Balance.Holds called account
        (deposited (Account.Balance.of memory account) amount (count + 1)) := by
      rwa [deposited_succ below, ← held.2]
    cil_loop_recurse recurse (count + 1)
    case invariant => exact ⟨held, by simp only [toNat_succ below]; omega⟩
    case measure => simp only [toNat_succ below]; omega

#print axioms correctness

end ExampleProof
