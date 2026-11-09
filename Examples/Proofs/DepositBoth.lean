import Extracted
import CIL.MethodIdentity
import CIL.Safety.ObjectFields

/-!
# Instance calls through `callvirt`

`Objects.DepositBoth(first, second, amount)` calls the instance method `Account.Deposit` on each
account. C# compiles both calls as `callvirt`, which checks the receiver for null before the
call; `Deposit` is not virtual, so the call has one target. The proof composes both calls through
`depositContract` and decides the aliasing of the second balance across the first call with
`Owned.across`, as `BumpBoth` does for a static method. A null receiver throws
`NullReferenceException` at the `callvirt` in the caller, before `Deposit` runs; a null second
account throws at the second `callvirt` after the first deposit has returned.
-/

open CIL.Safety
open CIL (W64)
open Extracted.Classes
namespace ExampleProof

bind_method depositBoth depositBothBody :=
  "System.Void Examples.Objects::DepositBoth(Examples.Account,Examples.Account,System.UInt64)"
bind_callee deposit depositBody :=
  "System.Void Examples.Account::Deposit(System.UInt64)" from depositBothBody [0]

/-- `account.Deposit(amount)` adds `amount` to `account.Balance` and writes nothing else. -/
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
  cil_checked_steps [owned.facts, written]

#print axioms deposit_holds

/-- `DepositBoth(first, second, amount)` adds `amount` to each account's `Balance`, twice to one
    account passed as both, and writes nothing else. -/
def depositBothContract : MethodContract (Reference × Reference × W64) where
  args := fun (first, second, amount) =>
    [.object (.address first), .object (.address second), .scalar (.i64 amount)]
  pre := fun (first, second, _) memory =>
    Account.Balance.Owned memory first ∧ Account.Balance.Owned memory second
  footprint := fun (first, second, _) =>
    [Account.Balance.entry first, Account.Balance.entry second]
  post := fun (first, second, amount) initial final values => values = [] ∧
    if first = second then
      Account.Balance.Holds final first (Account.Balance.of initial first + amount + amount)
    else
      Account.Balance.Holds final first (Account.Balance.of initial first + amount) ∧
        Account.Balance.Holds final second (Account.Balance.of initial second + amount)

/-- `DepositBoth` meets its contract given only the contract of `Deposit`: each `callvirt` passes
    its null check on a live account and is composed through `depositContract`. -/
theorem depositBoth_holds (holds : depositContract.Holds Extracted.program deposit) :
    depositBothContract.Holds Extracted.program depositBoth := by
  rintro ⟨first, second, amount⟩ memory ⟨firstOwned, secondOwned⟩
  cil_contract_steps [holds, depositContract, firstOwned, firstOwned.facts, secondOwned.facts]
    with middle values firstCall
  obtain ⟨rfl, firstHeld⟩ := firstCall.post
  have firstFramed := firstCall.framed
  have secondHeld := secondOwned.across firstOwned.live firstFramed firstHeld
  cil_contract_steps [holds, depositContract, secondHeld.1, secondHeld.1.facts]
    with final values secondCall
  obtain ⟨rfl, secondFinal⟩ := secondCall.post
  have secondFramed := secondCall.framed
  dsimp only [depositContract] at firstFramed secondFramed
  cil_contract_steps []
  change Confined _ memory final ∧
    depositBothContract.Returns (first, second, amount) memory final []
  refine ⟨(firstFramed.widen (by simp)).trans (secondFramed.widen (by simp)), [], rfl, rfl, ?_⟩
  split
  · rename_i same
    subst same
    simpa [firstHeld.2] using secondFinal
  · rename_i distinct
    have firstFinal := firstHeld.1.across secondHeld.1.live secondFramed secondFinal
    simp only [Ne.symm distinct, ite_false, firstHeld.2] at firstFinal
    simp only [distinct, ite_false, secondHeld.2] at secondFinal
    exact ⟨firstFinal, secondFinal⟩

#print axioms depositBoth_holds

/-- `DepositBoth` meets its contract, with `Deposit` discharged by its own proof. -/
theorem correctness : depositBothContract.Holds Extracted.program depositBoth :=
  depositBoth_holds deposit_holds

#print axioms correctness

/-- A null `first` throws `NullReferenceException` at the first `callvirt`, pc 2 of
    `DepositBoth` itself, whatever `second` is: the receiver check runs in the caller, so
    `Deposit` is never entered, unlike a null account passed to a static method. -/
theorem first_null_throws (memory : Memory) (second : Reference) (amount : W64)
    (secondLive : LiveObject memory second) :
    ∃ fuel, invoke Extracted.program fuel depositBoth
        [.object .null, .object (.address second), .scalar (.i64 amount)] memory =
      .error ⟨depositBoth, 2, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps [secondLive.formed]

#print axioms first_null_throws

/-- A null `second` throws `NullReferenceException` at the second `callvirt`, pc 5, only after
    `Deposit` has run on a live `first`: the invocation of `Deposit` that `DepositBoth` makes at
    pc 2 returns with `amount` added to the first balance and no other byte written, and the run
    then faults at pc 5. Memory after a throw is not observable, so the deposit is stated on
    that call rather than on the faulting result. -/
theorem second_null_throws (memory : Memory) (first : Reference) (amount : W64)
    (owned : Account.Balance.Owned memory first) :
    ∃ fuel middle,
      invoke Extracted.program fuel deposit [.object (.address first), .scalar (.i64 amount)]
          memory = .ok (middle, []) ∧
        Confined [Account.Balance.entry first] memory middle ∧
        Account.Balance.Holds middle first (Account.Balance.of memory first + amount) ∧
        invoke Extracted.program (fuel + 6) depositBoth
            [.object (.address first), .object .null, .scalar (.i64 amount)] memory =
          .error ⟨depositBoth, 5, .thrown "System.NullReferenceException"⟩ := by
  obtain ⟨middle, values, deposited⟩ := deposit_holds.result (first, amount) owned
  obtain ⟨rfl, held⟩ := deposited.post
  obtain ⟨childFuel, invoked⟩ := deposited.invoked
  refine ⟨childFuel, middle, invoked, deposited.framed, held, ?_⟩
  -- The caller reaches the call with three of its six units of fuel spent.
  have called := invoke_mono _ childFuel 3 _ _ _ (.ok (middle, [])) trivial invoked
  cil_checked_steps [owned.live.formed, called]

#print axioms second_null_throws

end ExampleProof
