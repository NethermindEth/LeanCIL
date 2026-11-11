import Extracted
import CIL.MethodIdentity
import CIL.Safety.ObjectFields
import CIL.Safety.OutcomeContract

/-!
# Two calls on class instances

`Objects.BumpBoth(first, second, amount)` calls the static `Bump(account, amount)` on each
account. Both may be the same instance, so the proof composes the calls through `bumpContract`
and decides the aliasing of the second balance across the first call with `Owned.across`.
-/

open CIL.Safety
open CIL (W64)
open Extracted.Classes
namespace ExampleProof

bind_method bumpBoth bumpBothBody :=
  "System.Void Examples.Objects::BumpBoth(Examples.Account,Examples.Account,System.UInt64)"
bind_callee bump bumpBody :=
  "System.Void Examples.Objects::Bump(Examples.Account,System.UInt64)" from bumpBothBody [0]

/-- `Bump(account, amount)` adds `amount` to `account.Balance` and writes nothing else. -/
def bumpContract : MethodContract (Reference × W64) where
  args := fun (account, amount) => [.object (.address account), .scalar (.i64 amount)]
  pre := fun (account, _) memory => Account.Balance.Owned memory account
  footprint := fun (account, _) => [Account.Balance.entry account]
  post := fun (account, amount) initial final values => values = [] ∧
    Account.Balance.Holds final account (Account.Balance.of initial account + amount)

/-- `Bump` meets its contract for every live account and amount. -/
theorem bump_holds : bumpContract.Holds Extracted.program bump := by
  rintro ⟨account, amount⟩ memory owned
  dsimp only [bumpContract] at owned
  obtain ⟨after, written, framed, held⟩ :=
    owned.store (Account.Balance.of memory account + amount)
  refine MethodContract.Holds.intro after [] ?_ framed ⟨rfl, held⟩
  cil_checked_steps [written]

#print axioms bump_holds

/-- `BumpBoth(first, second, amount)` adds `amount` to each account's `Balance`, twice to one
    account passed as both, and writes nothing else. -/
def bumpBothContract : MethodContract (Reference × Reference × W64) where
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

/-- `BumpBoth` meets its contract given only the contract of `Bump`: each call is composed
    through `bumpContract`, and the second balance is framed across the first call. -/
theorem bumpBoth_holds (holds : bumpContract.Holds Extracted.program bump) :
    bumpBothContract.Holds Extracted.program bumpBoth := by
  rintro ⟨first, second, amount⟩ memory ⟨firstOwned, secondOwned⟩
  cil_contract_steps [holds, bumpContract, firstOwned]
    with middle values firstCall
  obtain ⟨rfl, firstHeld⟩ := firstCall.post
  have firstFramed := firstCall.framed
  have secondHeld := secondOwned.across firstOwned.live firstFramed firstHeld
  cil_contract_steps [holds, bumpContract, secondHeld.1]
    with final values secondCall
  obtain ⟨rfl, secondFinal⟩ := secondCall.post
  have secondFramed := secondCall.framed
  dsimp only [bumpContract] at firstFramed secondFramed
  cil_contract_steps []
  refine MethodContract.Holds.returns
    ((firstFramed.widen (by simp)).trans (secondFramed.widen (by simp))) ⟨rfl, ?_⟩
  split
  · rename_i same
    subst same
    simpa [firstHeld.2] using secondFinal
  · rename_i distinct
    have firstFinal := firstHeld.1.across secondHeld.1.live secondFramed secondFinal
    simp only [Ne.symm distinct, ite_false, firstHeld.2] at firstFinal
    simp only [distinct, ite_false, secondHeld.2] at secondFinal
    exact ⟨firstFinal, secondFinal⟩

#print axioms bumpBoth_holds

/-- `BumpBoth` meets its contract, with `Bump` discharged by its own proof. -/
theorem correctness : bumpBothContract.Holds Extracted.program bumpBoth :=
  bumpBoth_holds bump_holds

#print axioms correctness

/-- `Bump` on a null account throws `NullReferenceException` at its field load. -/
theorem bump_null_throws (memory : Memory) (amount : W64) :
    ∃ fuel, invoke Extracted.program fuel bump [.object .null, .scalar (.i64 amount)] memory =
      .error ⟨bump, 2, .thrown "System.NullReferenceException"⟩ := by
  cil_checked_steps

#print axioms bump_null_throws

/-- `Bump` with a possibly null account: a null account throws `NullReferenceException`, and a
    live one meets `bumpContract`. -/
def bumpOutcome : OutcomeContract (ManagedReference × W64) where
  args := fun (account, amount) => [.object account, .scalar (.i64 amount)]
  pre := fun (account, _) memory => match account with
    | .null => True
    | .address account => Account.Balance.Owned memory account
  footprint := fun (account, _) => match account with
    | .null => []
    | .address account => [Account.Balance.entry account]
  post := fun (account, amount) initial final values => values = [] ∧ match account with
    | .null => True
    | .address account =>
      Account.Balance.Holds final account (Account.Balance.of initial account + amount)
  raises := fun (account, _) _ => match account with
    | .null => some "System.NullReferenceException"
    | .address _ => none

/-- `Bump` meets its outcome contract: the runtime exception for null, the update otherwise. -/
theorem bump_outcome : bumpOutcome.Holds Extracted.program bump := by
  rintro ⟨account, amount⟩ memory permitted
  cases account with
  | null =>
    obtain ⟨fuel, thrown⟩ := bump_null_throws memory amount
    exact ⟨fuel, _, thrown, rfl⟩
  | address account => exact WP.adequate.mp (bump_holds (account, amount) memory permitted)

#print axioms bump_outcome
end ExampleProof
