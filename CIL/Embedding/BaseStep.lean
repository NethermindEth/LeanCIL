import CIL.Embedding.Basic
import CIL.NativeEvaluation

/-!
# Relabeling value-only steps

Relabeling the targets of a value-only instruction relabels the pc it resumes at.
These are the instructions the checked interpreter executes through `CIL.step`.
-/

namespace CIL.Embedding

open CIL

/-- A successful `Option` bind succeeded at both steps. -/
theorem option_bind_some {x : Option α} {f : α → Option β} {y : β} (h : x >>= f = some y) :
    ∃ a, x = some a ∧ f a = some y := Option.bind_eq_some_iff.mp h

/-- Relabeling `op` maps its successor when the fallthrough pc is mapped consistently. -/
def BaseRelabel (op : Instruction) : Prop :=
  ∀ (r : Nat → Nat) (pc q : Nat) (values : List Value) (profile : FeatureProfile) (target : Nat)
    (result : List Value) (memory : Memory), (op.continues = true → r (pc + 1) = q + 1) →
    step op false pc [] 0 values (fun _ => none) profile = some (.next target result memory) →
    step (op.relabel r) false q [] 0 values (fun _ => none) profile =
      some (.next (r target) result memory)

/-- A value-only instruction computes its output independently of the program counter. -/
def Fallthrough (op : Instruction) (evaluate : List Value → FeatureProfile → Option (List Value)) :
    Prop :=
  ∀ pc stack profile, step op false pc [] 0 stack (fun _ => none) profile = do
    return .next (pc + 1) (← evaluate stack profile) (fun _ => none)

/-- A falling-through value-only instruction that relabeling leaves unchanged satisfies
    `BaseRelabel`. -/
theorem base_relabel_fallthrough {op : Instruction} {evaluate}
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

/-- The stack after a one-operand instruction. -/
def unaryValues (op : Instruction) (stack : List Value) (_ : FeatureProfile) :
    Option (List Value) := do
  match stack with
  | value :: rest => return (← unary op value) :: rest
  | [] => none

/-- The stack after a two-operand instruction; `a` was pushed first. -/
def binaryValues (op : Instruction) (stack : List Value) (_ : FeatureProfile) :
    Option (List Value) := do
  match stack with
  | b :: a :: rest => return (← binary op a b) :: rest
  | _ => none

/-- Whether a compare-branch is taken on two same-width integers, and the remaining stack. -/
def comparisonValues (compare32 : W32 → W32 → Bool) (compare64 : W64 → W64 → Bool)
    (stack : List Value) : Option (Bool × List Value) :=
  match stack with
  | .i32 b :: .i32 a :: rest => some (compare32 a b, rest)
  | .i64 b :: .i64 a :: rest => some (compare64 a b, rest)
  | _ => none

/-- Whether `brtrue` (or, with `negate`, `brfalse`) is taken, and the remaining stack. -/
def truthValues (negate : Bool) (stack : List Value) : Option (Bool × List Value) := do
  match stack with
  | value :: rest => return ((← truth value) != negate, rest)
  | [] => none

/-- A conditional branch observes values independently of either destination. -/
def Branching (op : Nat → Instruction) (evaluate : List Value → Option (Bool × List Value)) :
    Prop :=
  ∀ target pc stack profile, step (op target) false pc [] 0 stack (fun _ => none) profile = do
    let (taken, rest) ← evaluate stack
    return .next (if taken then target else pc + 1) rest (fun _ => none)

/-- A conditional branch family whose relabeling maps its target satisfies `BaseRelabel`. -/
theorem base_relabel_branching {op : Nat → Instruction} {evaluate}
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
/-- Proves `BaseRelabel` for a compare-branch with the given 32- and 64-bit comparisons. -/
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
/-- Proves `BaseRelabel` for a one-operand instruction evaluated by `unary`. -/
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
/-- Proves `BaseRelabel` for a two-operand instruction evaluated by `binary`. -/
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
/-- Proves `BaseRelabel` for `brfalse` (`negate` true) or `brtrue` (`negate` false). -/
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
theorem base_relabel_cgt : BaseRelabel (.cgt) := by base_relabel_binary
theorem base_relabel_bgt (t : Nat) : BaseRelabel (.bgt t) := by
  base_relabel_comparison (fun a b => decide (b.toInt < a.toInt)),
    (fun a b => decide (b.toInt < a.toInt))
theorem base_relabel_ble (t : Nat) : BaseRelabel (.ble t) := by
  base_relabel_comparison (fun a b => decide (a.toInt ≤ b.toInt)),
    (fun a b => decide (a.toInt ≤ b.toInt))
theorem base_relabel_ble_un (t : Nat) : BaseRelabel (.ble_un t) := by
  base_relabel_comparison (fun a b => decide (a ≤ b)), (fun a b => decide (a ≤ b))
theorem base_relabel_conv_i1 : BaseRelabel (.conv_i1) := by base_relabel_unary
theorem base_relabel_conv_i2 : BaseRelabel (.conv_i2) := by base_relabel_unary
theorem base_relabel_conv_u2 : BaseRelabel (.conv_u2) := by base_relabel_unary
theorem base_relabel_conv_i8 : BaseRelabel (.conv_i8) := by base_relabel_unary
theorem base_relabel_conv_i4 : BaseRelabel (.conv_i4) := by base_relabel_unary
theorem base_relabel_conv_u1 : BaseRelabel (.conv_u1) := by base_relabel_unary
theorem base_relabel_conv_u4 : BaseRelabel (.conv_u4) := by base_relabel_unary
theorem base_relabel_conv_u8 : BaseRelabel (.conv_u8) := by base_relabel_unary
theorem base_relabel_conv_u : BaseRelabel (.conv_u) := by base_relabel_unary
/-- Relabeling `conv_i` maps its successor when the fallthrough pc is mapped consistently. -/
theorem base_relabel_conv_i : BaseRelabel (.conv_i) := by base_relabel_unary
#print axioms base_relabel_conv_i
theorem base_relabel_not : BaseRelabel (.not) := by base_relabel_unary
theorem base_relabel_add : BaseRelabel (.add) := by base_relabel_binary
theorem base_relabel_sub : BaseRelabel (.sub) := by base_relabel_binary
theorem base_relabel_mul : BaseRelabel (.mul) := by base_relabel_binary
theorem base_relabel_and : BaseRelabel (.and) := by base_relabel_binary
theorem base_relabel_or : BaseRelabel (.or) := by base_relabel_binary
theorem base_relabel_xor : BaseRelabel (.xor) := by base_relabel_binary
theorem base_relabel_shl : BaseRelabel (.shl) := by base_relabel_binary
theorem base_relabel_shr : BaseRelabel (.shr) := by base_relabel_binary
theorem base_relabel_shr_un : BaseRelabel (.shr_un) := by base_relabel_binary
theorem base_relabel_clt : BaseRelabel (.clt) := by base_relabel_binary
theorem base_relabel_clt_un : BaseRelabel (.clt_un) := by base_relabel_binary
theorem base_relabel_cgt_un : BaseRelabel (.cgt_un) := by base_relabel_binary
theorem base_relabel_ceq : BaseRelabel (.ceq) := by base_relabel_binary
theorem base_relabel_brfalse (t : Nat) : BaseRelabel (.brfalse t) := by base_relabel_truth true
theorem base_relabel_brtrue (t : Nat) : BaseRelabel (.brtrue t) := by base_relabel_truth false
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
theorem base_relabel_blt_un (t : Nat) : BaseRelabel (.blt_un t) := by
  base_relabel_comparison (fun a b => decide (a < b)), (fun a b => decide (a < b))
theorem base_relabel_bge_un (t : Nat) : BaseRelabel (.bge_un t) := by
  base_relabel_comparison (fun a b => decide (b ≤ a)), (fun a b => decide (b ≤ a))
theorem base_relabel_bgt_un (t : Nat) : BaseRelabel (.bgt_un t) := by
  base_relabel_comparison (fun a b => decide (b < a)), (fun a b => decide (b < a))
theorem base_relabel_bge (t : Nat) : BaseRelabel (.bge t) := by
  base_relabel_comparison (fun a b => decide (b.toInt ≤ a.toInt)),
    (fun a b => decide (b.toInt ≤ a.toInt))
theorem base_relabel_blt (t : Nat) : BaseRelabel (.blt t) := by
  base_relabel_comparison (fun a b => decide (a.toInt < b.toInt)),
    (fun a b => decide (a.toInt < b.toInt))
theorem base_relabel_beq (t : Nat) : BaseRelabel (.beq t) := by
  base_relabel_comparison (fun a b => decide (a = b)), (fun a b => decide (a = b))
theorem base_relabel_bne_un (t : Nat) : BaseRelabel (.bne_un t) := by
  base_relabel_comparison (fun a b => decide (a ≠ b)), (fun a b => decide (a ≠ b))
theorem base_relabel_br (t : Nat) : BaseRelabel (.br t) := by
  intro r pc q values profile target result memory next h
  change some (Action.next t values (fun _ => none)) = _ at h
  cases h
  rfl
theorem base_relabel_feature (id : Feature) : BaseRelabel (.feature id) :=
  base_relabel_fallthrough
    (evaluate := fun stack profile => some (.i32 (if profile.evaluate id then 1 else 0) :: stack))
    (fun _ _ _ => rfl) (fun _ => rfl) rfl

theorem widenNativeOperand_relabel (r : Nat → Nat) (op : Instruction) :
    widenNativeOperand (op.relabel r) = widenNativeOperand op := by
  cases op <;> rfl

theorem nativePureBinary_relabel (r : Nat → Nat) (op : Instruction) :
    nativePureBinary (op.relabel r) = nativePureBinary op := by
  cases op <;> rfl

/-- Relabeling keeps the flags of a division or remainder. -/
theorem divideKind?_relabel (r : Nat → Nat) (op : Instruction) :
    (op.relabel r).divideKind? = op.divideKind? := by
  cases op <;> rfl

#print axioms divideKind?_relabel

/-- Relabeling keeps the flags of overflow-checked arithmetic. -/
theorem checkedKind?_relabel (r : Nat → Nat) (op : Instruction) :
    (op.relabel r).checkedKind? = op.checkedKind? := by
  cases op <;> rfl

#print axioms checkedKind?_relabel

/-- Every value-only instruction a native-width wrapper may carry satisfies `BaseRelabel`. -/
theorem base_relabel_of_nativePure (op : Instruction) (pure : nativePureBinary op = true) :
    BaseRelabel op := by
  cases op <;> simp only [nativePureBinary, Bool.false_eq_true] at pure
  all_goals first
    | exact base_relabel_add | exact base_relabel_sub | exact base_relabel_mul
    | exact base_relabel_and | exact base_relabel_or | exact base_relabel_xor
    | exact base_relabel_clt | exact base_relabel_clt_un | exact base_relabel_cgt
    | exact base_relabel_cgt_un | exact base_relabel_ceq | exact base_relabel_bgt _
    | exact base_relabel_ble _ | exact base_relabel_bge _ | exact base_relabel_blt _
    | exact base_relabel_beq _

end CIL.Embedding
