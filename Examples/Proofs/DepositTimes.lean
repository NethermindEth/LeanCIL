import Extracted
import CIL.Verification
import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.Safety.LoopScaffold
import CIL.Safety.ObjectFraming

/-!
# An instance call in a loop

`Objects.DepositTimes(account, amount, times)` calls `account.Deposit(amount)` through `callvirt`
once per iteration of a counted loop. The loop tactics cross each call through `Deposit`'s
contract with the frame facts they carry; the balance word is held as `Contents` and `Writable`
facts, which the tactics restate at every memory the call and the counter's store produce. The
proof supplies the invariant, the measure and the arithmetic.
-/

open CIL.Safety
open CIL (W32 W64)
namespace ExampleProof

/-- The runtime type of `Examples.Account` instances. -/
def accountType : CIL.Extraction.TypeExpr :=
  .object "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Examples.Account"

bind_method depositTimes depositTimesBody :=
  "System.Void Examples.Objects::DepositTimes(Examples.Account,System.UInt64,System.UInt32)"
bind_callee deposit depositBody :=
  "System.Void Examples.Account::Deposit(System.UInt64)" from depositTimesBody
bind_call depositSite := deposit from depositTimesBody

/-- `Balance` of the live account at `account` is a writable word holding some value, and is
    located at the account's own reference, being its first field. -/
def BalanceWord (memory : Memory) (account : Reference) : Prop :=
  objectFieldAddress memory (.address account) accountType 0 = .ok account ∧
    (∃ balance : W64, read memory account 8 1 = .ok (numberBytes balance.toNat 8)) ∧
    access memory account 8 1 true = .ok ()

/-- `account.Deposit(amount)` adds `amount` to `Balance` and writes no other byte. -/
def depositContract : MethodContract (Reference × W64) where
  args input := [.object (.address input.1), .scalar (.i64 input.2)]
  pre input memory := BalanceWord memory input.1
  footprint input := [(input.1, 8)]
  post input initial final values := values = [] ∧
    ∀ balance : W64, read initial input.1 8 1 = .ok (numberBytes balance.toNat 8) →
      read final input.1 8 1 = .ok (numberBytes (balance + input.2).toNat 8)

/-- Two reads of one word give the same value. -/
theorem word_unique {memory : Memory} {reference : Reference} {left right : W64}
    (leftRead : read memory reference 8 1 = .ok (numberBytes left.toNat 8))
    (rightRead : read memory reference 8 1 = .ok (numberBytes right.toNat 8)) : left = right := by
  have leftLoaded := load_word64_of_read leftRead
  rw [load_word64_of_read rightRead] at leftLoaded
  cases leftLoaded
  rfl

#print axioms word_unique

/-- `Deposit` meets its contract for every live account and amount. -/
theorem deposit_holds : depositContract.Holds Extracted.program deposit := by
  rintro ⟨account, amount⟩ memory ⟨located, ⟨balance, loaded⟩, writable⟩
  dsimp only [depositContract] at *
  obtain ⟨after, written, -, readback⟩ := store_word64 (balance + amount) writable
  have formed := formObject_of_objectFieldAddress located
  have value := load_word64_of_read loaded
  refine ⟨CIL.executionBound Extracted.program deposit, after, [], ?_,
    Confined.write written (by simp [numberBytes]), [], rfl, rfl, ?_⟩
  · cil_checked_steps [formed, located, value, written, accountType]
  · intro old oldLoaded
    rw [← word_unique loaded oldLoaded]
    exact readback

#print axioms deposit_holds

bind_entry entry (memory : Memory) (account : Reference) (amount : W64) (times : W32)
    (wellFormed : memory.WellFormed) :=
  depositTimesBody with [.object (.address account), .scalar (.i64 amount), .scalar (.i32 times)]
    from memory allocating wellFormed
bind_loop loop := depositTimesBody

/-- The calls made so far, held by the frame's only local; the account's balance word is the
    caller storage the frame may change. -/
private abbrev State (memory : Memory) (account home : Reference) :=
  FrameState [(account, 8)] memory [.word32] W32 (fun _ => [.bytes .word32 home])
    fun count => [some (.i32 count)]

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

/-- `DepositTimes` adds `amount` to the balance `times` times and writes no other caller byte. -/
theorem correctness (memory : Memory) (account : Reference) (amount balance : W64)
    (times : W32) (wellFormed : memory.WellFormed)
    (located : objectFieldAddress memory (.address account) accountType 0 = .ok account)
    (loaded : Contents memory account 8 [balance]) (writable : Writable memory account 8 0 1) :
    ∃ fuel final, invoke Extracted.program fuel depositTimes
        [.object (.address account), .scalar (.i64 amount), .scalar (.i32 times)] memory =
      .ok (final, []) ∧
      Contents final account 8 [deposited balance amount times] ∧
      Confined [(account, 8)] memory final := by
  obtain ⟨home, entered, setup, -, entryMemory, entryFrame⟩ :=
    entry.checked memory account amount times wellFormed
  have formed := formObject_of_objectFieldAddress located
  have old := wellFormed.object_below formed
  have contentsEntered := loaded.after_below entryMemory.kept old
  have roomEntered := writable.after_below entryMemory.kept old
  refine invoke_loop_induction depositTimes.found ?_ setup (header memory account times home)
    (fun state => Contents state.memory account 8 [deposited balance amount state.values] ∧
      Writable state.memory account 8 0 1 ∧ state.values.toNat ≤ times.toNat)
    (fun state => times.toNat - state.values.toNat) (fun start => ?_) ?_
  · simp [checkedValue, formed, numericValue, Bind.bind, Except.bind,
      Pure.pure, Except.pure, List.mapM_cons, List.mapM_nil]
  · cil_loop_recurse start 0
    refine ⟨?_, roomEntered, Nat.zero_le _⟩
    simpa [deposited] using contentsEntered
  rintro ⟨count, current, frame⟩ ⟨contents, room, bounded⟩ recurse
  dsimp only at contents room bounded
  have live := formObject_of_confined frame.confined wellFormed formed
  by_cases done : count = times
  · subst done
    cil_loop_finish [live]
  · have below : count.toNat < times.toNat := by
      have : count.toNat ≠ times.toNat := fun same => done (BitVec.eq_of_toNat_eq same)
      omega
    have more : count < times := below
    cil_loop_advance [more, live]
    -- `Deposit`'s precondition at the call, which `cil_loop_call` takes from the context.
    have word : BalanceWord current account := by
      refine ⟨objectFieldAddress_of_confined frame.confined wellFormed located,
        ⟨_, by simpa using contents 0 _ rfl⟩, by simpa using room 0 (by decide)⟩
    cil_loop_call deposit_holds (account, amount) at depositSite [live]
    obtain ⟨rfl, added⟩ := returned
    have contents : Contents called account 8 [deposited balance amount (count + 1)] := by
      rw [Contents.singleton, deposited_succ below]
      exact added _ (Contents.singleton.mp contents)
    cil_loop_recurse recurse (count + 1)
    case invariant => exact ⟨contents, room, by simp only [toNat_succ below]; omega⟩
    case measure => simp only [toNat_succ below]; omega

#print axioms correctness

end ExampleProof
