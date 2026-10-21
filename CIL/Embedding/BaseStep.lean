import CIL.Embedding.Basic
import CIL.NativeEvaluation

/-!
Relabeling the targets of a value-only instruction relabels the pc it resumes at.
These are the instructions the checked interpreter executes through `CIL.step`.
-/

namespace CIL.Embedding

open CIL

theorem option_bind_some {x : Option α} {f : α → Option β} {y : β} (h : x >>= f = some y) :
    ∃ a, x = some a ∧ f a = some y := Option.bind_eq_some_iff.mp h

/-- Relabeling `op` maps its successor when the fallthrough pc is mapped consistently. -/
def BaseRelabel (op : Op) : Prop :=
  ∀ (r : Nat → Nat) (pc q : Nat) (values : List Value) (profile : FeatureProfile) (target : Nat)
    (result : List Value) (memory : Memory), (op.continues = true → r (pc + 1) = q + 1) →
    step op false pc [] 0 values (fun _ => none) profile = some (.next target result memory) →
    step (op.relabel r) false q [] 0 values (fun _ => none) profile = some (.next (r target) result memory)

/-- A value-only instruction computes its output independently of the program counter. -/
def Fallthrough (op : Op) (evaluate : List Value → FeatureProfile → Option (List Value)) : Prop :=
  ∀ pc stack profile, step op false pc [] 0 stack (fun _ => none) profile = do
    return .next (pc + 1) (← evaluate stack profile) (fun _ => none)

theorem base_relabel_fallthrough {op : Op} {evaluate}
    (equation : Fallthrough op evaluate) (relabel : ∀ r, op.relabel r = op)
    (continues : op.continues = true) : BaseRelabel op := by
  intro r pc q values profile target result memory next h
  rw [equation] at h
  rw [relabel, equation]
  obtain ⟨output, evaluated, h⟩ := option_bind_some h
  simp only [pure, Option.some.injEq, Action.next.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rw [evaluated, next continues]
  rfl

def unaryValues (op : Op) (stack : List Value) (_ : FeatureProfile) : Option (List Value) := do
  match stack with
  | value :: rest => return (← unary op value) :: rest
  | [] => none

def binaryValues (op : Op) (stack : List Value) (_ : FeatureProfile) : Option (List Value) := do
  match stack with
  | b :: a :: rest => return (← binary op a b) :: rest
  | _ => none

def comparisonValues (compare32 : W32 → W32 → Bool) (compare64 : W64 → W64 → Bool)
    (stack : List Value) : Option (Bool × List Value) :=
  match stack with
  | .i32 b :: .i32 a :: rest => some (compare32 a b, rest)
  | .i64 b :: .i64 a :: rest => some (compare64 a b, rest)
  | _ => none

def truthValues (negate : Bool) (stack : List Value) : Option (Bool × List Value) := do
  match stack with
  | value :: rest => return ((← truth value) != negate, rest)
  | [] => none

/-- A conditional branch observes values independently of either destination. -/
def Branching (op : Nat → Op) (evaluate : List Value → Option (Bool × List Value)) : Prop :=
  ∀ target pc stack profile, step (op target) false pc [] 0 stack (fun _ => none) profile = do
    let (taken, rest) ← evaluate stack
    return .next (if taken then target else pc + 1) rest (fun _ => none)

theorem base_relabel_branching {op : Nat → Op} {evaluate}
    (equation : Branching op evaluate) (relabel : ∀ r t, (op t).relabel r = op (r t))
    (continues : ∀ t, (op t).continues = true) (t : Nat) : BaseRelabel (op t) := by
  intro r pc q values profile target result memory next h
  rw [equation] at h
  rw [relabel, equation]
  obtain ⟨⟨taken, rest⟩, evaluated, h⟩ := option_bind_some h
  simp only [pure, Option.some.injEq, Action.next.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rw [evaluated]
  cases taken <;> simp only [Bool.false_eq_true, ↓reduceIte, next (continues t)] <;> rfl

set_option hygiene false in
macro "base_relabel_comparison " compare32:term ", " compare64:term : tactic => `(tactic| (
  apply base_relabel_branching (evaluate := comparisonValues $compare32 $compare64)
  · intro target pc stack profile
    cases stack with
    | nil => rfl
    | cons b rest =>
      cases rest with
      | nil => cases b <;> rfl
      | cons a rest =>
        cases b <;> first | rfl | (cases a <;>
          simp only [comparisonValues, bind, Option.bind, pure, decide_eq_true_eq] <;>
          first | rfl | (simp only [ite_not]; rfl))
  · intro r t; rfl
  · intro t; rfl))

set_option hygiene false in
macro "base_relabel_unary" : tactic => `(tactic| (
  apply base_relabel_fallthrough (evaluate := unaryValues _)
  · intro pc stack profile
    cases stack with
    | nil => rfl
    | cons value rest =>
      change (unary _ value >>= _) = ((unary _ value >>= _) >>= _)
      cases unary _ value <;> rfl
  · intro r; rfl
  · rfl))

set_option hygiene false in
macro "base_relabel_binary" : tactic => `(tactic| (
  apply base_relabel_fallthrough (evaluate := binaryValues _)
  · intro pc stack profile
    cases stack with
    | nil => rfl
    | cons b rest =>
      cases rest with
      | nil => rfl
      | cons a rest =>
        change (binary _ a b >>= _) = ((binary _ a b >>= _) >>= _)
        cases binary _ a b <;> rfl
  · intro r; rfl
  · rfl))

set_option hygiene false in
macro "base_relabel_truth " negate:term : tactic => `(tactic| (
  apply base_relabel_branching (evaluate := truthValues $negate)
  · intro target pc stack profile
    cases stack with
    | nil => rfl
    | cons value rest =>
      change (truth value >>= _) = ((truth value >>= _) >>= _)
      cases truth value with
      | none => rfl
      | some taken => cases taken <;> rfl
  · intro r t; rfl
  · intro t; rfl))

theorem base_relabel_nop : BaseRelabel (.nop) :=
  base_relabel_fallthrough (evaluate := fun stack _ => some stack)
    (fun _ _ _ => rfl) (fun _ => rfl) rfl
theorem base_relabel_neg : BaseRelabel (.neg) := by base_relabel_unary
theorem base_relabel_gt : BaseRelabel (.gt) := by base_relabel_binary
theorem base_relabel_bgt (t : Nat) : BaseRelabel (.bgt t) := by
  base_relabel_comparison (fun a b => decide (a.toInt > b.toInt)), (fun a b => decide (a.toInt > b.toInt))
theorem base_relabel_ble (t : Nat) : BaseRelabel (.ble t) := by
  base_relabel_comparison (fun a b => decide (a.toInt ≤ b.toInt)), (fun a b => decide (a.toInt ≤ b.toInt))
theorem base_relabel_bleu (t : Nat) : BaseRelabel (.bleu t) := by
  base_relabel_comparison (fun a b => decide (a ≤ b)), (fun a b => decide (a ≤ b))
theorem base_relabel_convI1 : BaseRelabel (.convI1) := by base_relabel_unary
theorem base_relabel_convI2 : BaseRelabel (.convI2) := by base_relabel_unary
theorem base_relabel_convU2 : BaseRelabel (.convU2) := by base_relabel_unary
theorem base_relabel_convI8 : BaseRelabel (.convI8) := by base_relabel_unary
theorem base_relabel_convI4 : BaseRelabel (.convI4) := by base_relabel_unary
theorem base_relabel_convU1 : BaseRelabel (.convU1) := by base_relabel_unary
theorem base_relabel_convU4 : BaseRelabel (.convU4) := by base_relabel_unary
theorem base_relabel_convU8 : BaseRelabel (.convU8) := by base_relabel_unary
theorem base_relabel_convU : BaseRelabel (.convU) := by base_relabel_unary
theorem base_relabel_bnot : BaseRelabel (.bnot) := by base_relabel_unary
theorem base_relabel_add : BaseRelabel (.add) := by base_relabel_binary
theorem base_relabel_sub : BaseRelabel (.sub) := by base_relabel_binary
theorem base_relabel_mul : BaseRelabel (.mul) := by base_relabel_binary
theorem base_relabel_band : BaseRelabel (.band) := by base_relabel_binary
theorem base_relabel_bor : BaseRelabel (.bor) := by base_relabel_binary
theorem base_relabel_bxor : BaseRelabel (.bxor) := by base_relabel_binary
theorem base_relabel_shl : BaseRelabel (.shl) := by base_relabel_binary
theorem base_relabel_shr : BaseRelabel (.shr) := by base_relabel_binary
theorem base_relabel_shrUn : BaseRelabel (.shrUn) := by base_relabel_binary
theorem base_relabel_lt : BaseRelabel (.lt) := by base_relabel_binary
theorem base_relabel_ltu : BaseRelabel (.ltu) := by base_relabel_binary
theorem base_relabel_gtu : BaseRelabel (.gtu) := by base_relabel_binary
theorem base_relabel_eq : BaseRelabel (.eq) := by base_relabel_binary
theorem base_relabel_brzero (t : Nat) : BaseRelabel (.brzero t) := by base_relabel_truth true
theorem base_relabel_brnonzero (t : Nat) : BaseRelabel (.brnonzero t) := by base_relabel_truth false
theorem base_relabel_switch (ts : List Nat) : BaseRelabel (.switch ts) := by
  intro r pc q values profile target result memory next h
  cases values with
  | nil => cases h
  | cons value rest =>
    cases value <;> try (solve | cases h)
    case i32 index =>
      change some (Action.next (ts[index.toNat]?.getD (pc + 1)) rest (fun _ => none)) = _ at h
      simp only [Option.some.injEq, Action.next.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      change some (Action.next ((ts.map r)[index.toNat]?.getD (q + 1)) rest (fun _ => none)) = _
      rw [List.getElem?_map, ← next rfl]
      cases ts[index.toNat]? <;> rfl
theorem base_relabel_bltu (t : Nat) : BaseRelabel (.bltu t) := by
  base_relabel_comparison (fun a b => decide (a < b)), (fun a b => decide (a < b))
theorem base_relabel_bgeu (t : Nat) : BaseRelabel (.bgeu t) := by
  base_relabel_comparison (fun a b => decide (¬a < b)), (fun a b => decide (¬a < b))
theorem base_relabel_bgtu (t : Nat) : BaseRelabel (.bgtu t) := by
  base_relabel_comparison (fun a b => decide (b < a)), (fun a b => decide (b < a))
theorem base_relabel_bge (t : Nat) : BaseRelabel (.bge t) := by
  base_relabel_comparison (fun a b => decide (b.toInt ≤ a.toInt)), (fun a b => decide (b.toInt ≤ a.toInt))
theorem base_relabel_blt (t : Nat) : BaseRelabel (.blt t) := by
  base_relabel_comparison (fun a b => decide (a.toInt < b.toInt)), (fun a b => decide (a.toInt < b.toInt))
theorem base_relabel_beq (t : Nat) : BaseRelabel (.beq t) := by
  base_relabel_comparison (fun a b => decide (a = b)), (fun a b => decide (a = b))
theorem base_relabel_bne (t : Nat) : BaseRelabel (.bne t) := by
  base_relabel_comparison (fun a b => decide (a ≠ b)), (fun a b => decide (a ≠ b))
theorem base_relabel_branch (t : Nat) : BaseRelabel (.branch t) := by
  intro r pc q values profile target result memory next h
  change some (Action.next t values (fun _ => none)) = _ at h
  cases h
  rfl
theorem base_relabel_feature (id : Feature) : BaseRelabel (.feature id) :=
  base_relabel_fallthrough
    (evaluate := fun stack profile => some (.i32 (if profile.evaluate id then 1 else 0) :: stack))
    (fun _ _ _ => rfl) (fun _ => rfl) rfl

theorem widenNativeOperand_relabel (r : Nat → Nat) (op : Op) :
    widenNativeOperand (op.relabel r) = widenNativeOperand op := by
  cases op <;> rfl

theorem nativePureBinary_relabel (r : Nat → Nat) (op : Op) :
    nativePureBinary (op.relabel r) = nativePureBinary op := by
  cases op <;> rfl

theorem base_relabel_of_nativePure (op : Op) (pure : nativePureBinary op = true) : BaseRelabel op := by
  cases op <;> simp only [nativePureBinary, Bool.false_eq_true] at pure
  all_goals first
    | exact base_relabel_add | exact base_relabel_sub | exact base_relabel_mul
    | exact base_relabel_band | exact base_relabel_bor | exact base_relabel_bxor
    | exact base_relabel_lt | exact base_relabel_ltu | exact base_relabel_gt
    | exact base_relabel_gtu | exact base_relabel_eq | exact base_relabel_bgt _
    | exact base_relabel_ble _ | exact base_relabel_bge _ | exact base_relabel_blt _
    | exact base_relabel_beq _

end CIL.Embedding
