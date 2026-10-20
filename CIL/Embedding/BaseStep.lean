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

set_option hygiene false in
macro "base_relabel_close" : tactic => `(tactic| (
  (try (obtain ⟨_, hv, h⟩ := option_bind_some h; rw [hv]))
  simp only [pure, Option.some.injEq, Action.next.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  subst h1 h2 h3
  first
  | rfl
  | (rw [← next]; rfl)
  | (split <;> simp_all)
  | (rw [← next]; simp only [List.getElem?_map]; cases (‹List Nat›[‹W32›.toNat]?) <;> rfl)))

set_option hygiene false in
/-- Splits the stack shape of one concrete instruction; contradictory arms close by constructor mismatch. -/
macro "base_relabel_tac" : tactic => `(tactic| (
  intro r pc q values profile target result memory next h
  simp only [Op.continues, forall_const] at next
  unfold step at h ⊢
  dsimp only [Op.relabel] at h ⊢
  first
  | base_relabel_close
  | (split at h <;> (try contradiction) <;> (try (revert h; injections; subst_vars; intro h)) <;>
      (try contradiction) <;> (try dsimp only at h ⊢) <;> base_relabel_close)))

-- Sequential elaboration shares the generated match splitter across the cases below.
set_option Elab.async false

theorem base_relabel_nop : BaseRelabel (.nop) := by base_relabel_tac
theorem base_relabel_neg : BaseRelabel (.neg) := by base_relabel_tac
theorem base_relabel_gt : BaseRelabel (.gt) := by base_relabel_tac
theorem base_relabel_bgt (t : Nat) : BaseRelabel (.bgt t) := by base_relabel_tac
theorem base_relabel_ble (t : Nat) : BaseRelabel (.ble t) := by base_relabel_tac
theorem base_relabel_bleu (t : Nat) : BaseRelabel (.bleu t) := by base_relabel_tac
theorem base_relabel_convI1 : BaseRelabel (.convI1) := by base_relabel_tac
theorem base_relabel_convI2 : BaseRelabel (.convI2) := by base_relabel_tac
theorem base_relabel_convU2 : BaseRelabel (.convU2) := by base_relabel_tac
theorem base_relabel_convI8 : BaseRelabel (.convI8) := by base_relabel_tac
theorem base_relabel_convI4 : BaseRelabel (.convI4) := by base_relabel_tac
theorem base_relabel_convU1 : BaseRelabel (.convU1) := by base_relabel_tac
theorem base_relabel_convU4 : BaseRelabel (.convU4) := by base_relabel_tac
theorem base_relabel_convU8 : BaseRelabel (.convU8) := by base_relabel_tac
theorem base_relabel_convU : BaseRelabel (.convU) := by base_relabel_tac
theorem base_relabel_bnot : BaseRelabel (.bnot) := by base_relabel_tac
theorem base_relabel_add : BaseRelabel (.add) := by base_relabel_tac
theorem base_relabel_sub : BaseRelabel (.sub) := by base_relabel_tac
theorem base_relabel_mul : BaseRelabel (.mul) := by base_relabel_tac
theorem base_relabel_band : BaseRelabel (.band) := by base_relabel_tac
theorem base_relabel_bor : BaseRelabel (.bor) := by base_relabel_tac
theorem base_relabel_bxor : BaseRelabel (.bxor) := by base_relabel_tac
theorem base_relabel_shl : BaseRelabel (.shl) := by base_relabel_tac
theorem base_relabel_shr : BaseRelabel (.shr) := by base_relabel_tac
theorem base_relabel_shrUn : BaseRelabel (.shrUn) := by base_relabel_tac
theorem base_relabel_lt : BaseRelabel (.lt) := by base_relabel_tac
theorem base_relabel_ltu : BaseRelabel (.ltu) := by base_relabel_tac
theorem base_relabel_gtu : BaseRelabel (.gtu) := by base_relabel_tac
theorem base_relabel_eq : BaseRelabel (.eq) := by base_relabel_tac
theorem base_relabel_brzero (t : Nat) : BaseRelabel (.brzero t) := by base_relabel_tac
theorem base_relabel_brnonzero (t : Nat) : BaseRelabel (.brnonzero t) := by base_relabel_tac
theorem base_relabel_switch (ts : List Nat) : BaseRelabel (.switch ts) := by base_relabel_tac
theorem base_relabel_bltu (t : Nat) : BaseRelabel (.bltu t) := by base_relabel_tac
theorem base_relabel_bgeu (t : Nat) : BaseRelabel (.bgeu t) := by base_relabel_tac
theorem base_relabel_bgtu (t : Nat) : BaseRelabel (.bgtu t) := by base_relabel_tac
theorem base_relabel_bge (t : Nat) : BaseRelabel (.bge t) := by base_relabel_tac
theorem base_relabel_blt (t : Nat) : BaseRelabel (.blt t) := by base_relabel_tac
theorem base_relabel_beq (t : Nat) : BaseRelabel (.beq t) := by base_relabel_tac
theorem base_relabel_bne (t : Nat) : BaseRelabel (.bne t) := by base_relabel_tac
theorem base_relabel_branch (t : Nat) : BaseRelabel (.branch t) := by base_relabel_tac
theorem base_relabel_feature (id : Feature) : BaseRelabel (.feature id) := by base_relabel_tac

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
