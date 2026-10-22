import CIL.Safety.Embedding.Simulation

namespace CIL.Embedding

open CIL

def suffixRename (lower start pc : Nat) : Nat :=
  if pc < lower then 0 else pc - lower + start

theorem _root_.CIL.Op.relabel_congr {left right : Nat → Nat} (op : Op)
    (same : ∀ target ∈ op.targets, left target = right target) :
    op.relabel left = op.relabel right := by
  induction op <;> simp_all [Op.relabel, Op.targets]

theorem BodyRefines.of_relocated_suffix {expected actual : Method} {lower start : Nat}
    (metadata : actual = { expected with code := actual.code, staticSites := actual.staticSites })
    (descriptors : actual.staticSites.map Prod.snd = expected.staticSites.map Prod.snd)
    (entry : lower = 0 → start = 0)
    (dead : ∀ pc op, pc < lower → expected.code[pc]? = some op → op.live = false)
    (suffix : actual.code.drop start =
      (expected.code.drop lower).map (Op.relabel (fun pc => pc - lower + start)))
    (targets : ∀ op ∈ expected.code.drop lower, ∀ target ∈ op.targets, lower ≤ target)
    (statics : ∀ pc, lower ≤ pc → staticAt actual (pc - lower + start) = staticAt expected pc) :
    BodyRefines expected actual (suffixRename lower start) := by
  refine ⟨congrArg Method.profile metadata, congrArg Method.returnsValue metadata,
    congrArg Method.locals metadata, congrArg Method.localKinds metadata,
    congrArg Method.vectorArgs metadata, congrArg Method.parameterHomes metadata, descriptors, ?_, ?_⟩
  · by_cases zero : lower = 0
    · simp [suffixRename, zero, entry zero]
    · simp [suffixRename, show 0 < lower by omega]
  · intro pc op found live
    have after : lower ≤ pc := by
      by_cases before : pc < lower
      · rw [dead pc op before found] at live
        cases live
      · omega
    have fetched : (expected.code.drop lower)[pc - lower]? = some op := by
      simpa only [List.getElem?_drop, Nat.add_sub_cancel' after] using found
    have member := List.mem_of_getElem? fetched
    have relabeled : op.relabel (fun pc => pc - lower + start) =
        op.relabel (suffixRename lower start) :=
      op.relabel_congr fun target inside => by
        simp [suffixRename, Nat.not_lt.mpr (targets op member target inside)]
    have code := congrArg (fun code => code[pc - lower]?) suffix
    rw [List.getElem?_drop, List.getElem?_map, fetched, Option.map_some,
      Nat.add_comm start (pc - lower), relabeled] at code
    refine ⟨?_, ?_, fun _ => ?_⟩
    · simpa only [suffixRename, if_neg (Nat.not_lt.mpr after)] using code
    · simpa only [suffixRename, if_neg (Nat.not_lt.mpr after)] using statics pc after
    · simp only [suffixRename, if_neg (Nat.not_lt.mpr after),
        if_neg (show ¬pc + 1 < lower by omega)]
      omega

end CIL.Embedding
