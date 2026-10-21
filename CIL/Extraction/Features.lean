import CIL.Extraction.Generics
import CIL.Extraction.FeatureEffects
import CIL.Extraction.Folds

namespace CIL.Extraction

/-- Feature facts use stack order (top first). `none` includes every runtime value;
    `some` describes exactly a 32-bit evaluation-stack word. -/
structure FeatureState where
  stack : List (Option W32)
  locals : List (Option W32)
  deriving DecidableEq, Repr

abbrev FeatureCertificate := List (Option FeatureState)

def factWeakens (source target : Option W32) : Bool := target.isNone || source == target

def factsWeaken (source target : List (Option W32)) : Bool :=
  source.length == target.length && (source.zip target).all fun (a, b) => factWeakens a b

def FeatureState.weakens (source target : FeatureState) : Bool :=
  factsWeaken source.stack target.stack && factsWeaken source.locals target.locals

private def runtimeIdentity := "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
private def intrinsicIdentity := "System.Runtime.Intrinsics, Version=10.0.0.0, Culture=neutral, PublicKeyToken=cc7b13ffcd2ddd51"

private def featureNames : List (String × Feature) := [
  ("Arm.AdvSimd", .advSimd), ("Arm.ArmBase/Arm64", .armBase64),
  ("X86.Sse2", .sse2), ("X86.Ssse3", .ssse3), ("X86.Sse41", .sse41),
  ("X86.Sse42", .sse42), ("X86.Avx", .avx), ("X86.Avx2", .avx2),
  ("X86.Avx512F", .avx512F), ("X86.Avx512F/VL", .avx512FVL),
  ("X86.Avx512DQ", .avx512DQ), ("X86.Avx512DQ/VL", .avx512DQVL),
  ("X86.Bmi1", .bmi1), ("X86.Bmi2/X64", .bmi2), ("X86.X86Base/X64", .x86Base64),
  ("Vector128", .vector128Accelerated), ("Vector256", .vector256Accelerated)]

/-- Identify getters from raw member and assembly identity, never an emitter-supplied flag. -/
def featureGetter (site : CallSite) : Option Feature := do
  let .external identity := site.target | none
  if site.parameterCount != 0 || site.hasThis || !site.returnsValue || !site.typeArguments.isEmpty then none
  else (featureNames.find? fun (name, feature) =>
    identity == intrinsicIdentity ++ "::System.Boolean System.Runtime.Intrinsics." ++ name ++ "::" ++
      (if feature == .vector128Accelerated || feature == .vector256Accelerated then "get_IsHardwareAccelerated"
        else "get_IsSupported") ++
      "()").map Prod.snd

private def localIndex (i : RawInstruction) : Option Nat :=
  match i.opcode, i.operand with
  | 6, .none | 10, .none => some 0
  | 7, .none | 11, .none => some 1
  | 8, .none | 12, .none => some 2
  | 9, .none | 13, .none => some 3
  | 17, .local n | 18, .local n | 19, .local n
  | 65036, .local n | 65037, .local n | 65038, .local n => some n
  | _, _ => none

private def addressed (raw : RawMethod) (index : Nat) : Bool := raw.code.any fun i =>
  (i.opcode == 18 || i.opcode == 65037) && localIndex i == some index

private def eligibleFact (raw : RawMethod) (index : Nat) (fact : Option W32) : Bool :=
  if fact.isNone then true else if addressed raw index then false else
  match raw.locals[index]? with
  | some (.atom scope name) => scope == runtimeIdentity &&
      (name == "System.Int32" || name == "System.UInt32" ||
        name == "System.Boolean" && (fact == some 0 || fact == some 1))
  | _ => false

private def wellShaped (raw : RawMethod) (state : FeatureState) : Bool :=
  state.locals.length == raw.locals.length && state.stack.length <= raw.maxStack &&
  (state.locals.zipIdx).all fun (fact, index) => eligibleFact raw index fact

private def constant32 (i : RawInstruction) : Option W32 :=
  match i.opcode, i.operand with
  | 21, .none => some (BitVec.ofInt 32 (-1))
  | 31, .integer n | 32, .integer n => some (BitVec.ofInt 32 n)
  | n, .none => if 22 <= n && n <= 30 then some (BitVec.ofNat 32 (n - 22)) else none
  | _, _ => none

/-- Fixed CLI stack effects; unknown values are never interpreted as false.
    Variable call and return effects are handled from raw signatures below. -/
private def stackEffect : Nat → Option (Nat × Nat)
  | 0 | 1 | 39 | 43 | 56 | 220 | 65042 | 65043 | 65044 | 65046 | 65049 | 65050 | 65054 => some (0, 0)
  | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 14 | 15 | 17 | 18 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 | 32 | 33 | 34 | 35 | 114 | 126 | 127 | 208 | 65024 | 65030 | 65033 | 65034 | 65036 | 65037 | 65052 => some (0, 1)
  | 10 | 11 | 12 | 13 | 16 | 19 | 38 | 44 | 45 | 57 | 58 | 69 | 122 | 128 | 65035 | 65038 | 65041 | 65045 => some (1, 0)
  | 46 | 47 | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 59 | 60 | 61 | 62 | 63 | 64 | 65 | 66 | 67 | 68 | 81 | 82 | 83 | 84 | 85 | 86 | 87 | 112 | 125 | 129 | 223 => some (2, 0)
  | 70 | 71 | 72 | 73 | 74 | 75 | 76 | 77 | 78 | 79 | 80 | 101 | 102 | 103 | 104 | 105 | 106 | 107 | 108 | 109 | 110 | 113 | 116 | 117 | 118 | 121 | 123 | 124 | 130 | 131 | 132 | 133 | 134 | 135 | 136 | 137 | 138 | 139 | 140 | 141 | 142 | 165 | 179 | 180 | 181 | 182 | 183 | 184 | 185 | 186 | 194 | 195 | 198 | 209 | 210 | 211 | 212 | 213 | 224 | 65031 | 65039 | 65053 => some (1, 1)
  | 88 | 89 | 90 | 91 | 92 | 93 | 94 | 95 | 96 | 97 | 98 | 99 | 100 | 143 | 144 | 145 | 146 | 147 | 148 | 149 | 150 | 151 | 152 | 153 | 154 | 163 | 214 | 215 | 216 | 217 | 218 | 219 | 65025 | 65026 | 65027 | 65028 | 65029 => some (2, 1)
  | 155 | 156 | 157 | 158 | 159 | 160 | 161 | 162 | 164 | 65047 | 65048 => some (3, 0)
  | _ => none

private def forget (state : FeatureState) (pops pushes : Nat) : Option FeatureState :=
  if pops <= state.stack.length then
    some { state with stack := List.replicate pushes none ++ state.stack.drop pops }
  else none

/-- Recompute a transfer from raw CLI encodings and metadata, independently of the
    extractor's worklist and its claimed incoming/outgoing facts. -/
def featureTransfer (raw : RawMethod) (profile : FeatureProfile)
    (i : RawInstruction) (state : FeatureState) : Option FeatureState := do
  if let some word := constant32 i then return { state with stack := some word :: state.stack }
  if i.opcode ∈ [6, 7, 8, 9, 17, 65036] then
    let index ← localIndex i
    let value ← state.locals[index]?
    return { state with stack := value :: state.stack }
  if i.opcode ∈ [10, 11, 12, 13, 19, 65038] then
    let index ← localIndex i
    let value :: stack := state.stack | none
    if index >= state.locals.length then none else
      return { stack, locals := state.locals.set index (if eligibleFact raw index value then value else none) }
  if i.opcode == 37 then
    let value :: stack := state.stack | none
    return { state with stack := value :: value :: stack }
  if i.opcode ∈ [95, 96, 97, 65025] then
    let right :: left :: stack := state.stack | none
    let value := do
      let a ← left
      let b ← right
      return if i.opcode == 95 then a &&& b else if i.opcode == 96 then a ||| b
        else if i.opcode == 97 then a ^^^ b else if a == b then 1 else 0
    return { state with stack := value :: stack }
  if i.opcode == 40 || i.opcode == 115 then
    let .call site := i.operand | none
    let next ← forget state (site.parameterCount + if i.opcode == 40 && site.hasThis then 1 else 0) 0
    if let some feature := featureGetter site then
      if i.opcode != 40 then none else
        return { next with stack := some (if profile.evaluate feature then 1 else 0) :: next.stack }
    return { next with stack := if i.opcode == 115 || site.returnsValue then none :: next.stack else next.stack }
  if i.opcode == 42 then forget state (if raw.returnType == .void then 0 else 1) 0
  else
    let (pops, pushes) ← stackEffect i.opcode
    forget state pops pushes

/-- A decided type test replaces the raw comparison result by its exact word. -/
def featureTransferAt (raw : RawMethod) (profile : FeatureProfile) (role : Option FoldRole)
    (i : RawInstruction) (state : FeatureState) : Option FeatureState :=
  match role with
  | some (.result value) => match state.stack with
    | _ :: _ :: stack => some { state with stack := some (if value then 1 else 0) :: stack }
    | _ => none
  | _ => featureTransfer raw profile i state

/-- Every switch destination is retained, even for a constant selector. Only
    true/false branches may prune an edge, and only for a known word. -/
def featureSuccessors (pc : Nat) (i : RawInstruction) (state : FeatureState) : Option (List Nat) :=
  if i.opcode == 42 || i.opcode == 122 || i.opcode == 65050 || i.opcode == 220 || i.opcode == 65041 then some []
  else if i.opcode == 43 || i.opcode == 56 then
    match i.operand with | .target target => some [target] | _ => none
  else if i.opcode == 69 then
    match i.operand with | .targets targets => some ((pc + 1) :: targets) | _ => none
  else if (44 <= i.opcode && i.opcode <= 55) || (57 <= i.opcode && i.opcode <= 68) then do
    let .target target := i.operand | none
    if i.opcode ∈ [44, 45, 57, 58] then
      match state.stack with
      | some value :: _ =>
        return [if (value != 0) == (i.opcode == 45 || i.opcode == 58) then target else pc + 1]
      | _ => return [target, pc + 1]
    else return [target, pc + 1]
  else some [pc + 1]

private def rawFeatureEffect (i : RawInstruction) : Option (Nat × Nat) := do
  if i.opcode == 40 || i.opcode == 115 then
    let .call site := i.operand | none
    return (site.parameterCount + if i.opcode == 40 && site.hasThis then 1 else 0,
      if i.opcode == 115 || site.returnsValue then 1 else 0)
  else stackEffect i.opcode

private def fallbackFeatureEffect (i : RawInstruction) (emitted : Op) : Bool :=
  let returnsValue := match i.operand with | .call site => site.returnsValue | _ => false
  let properCall := match emitted with
    | .call .. => i.opcode == 40
    | .newAggregate .. | .newVector256 .. => i.opcode == 115
    | _ => true
  properCall && match rawFeatureEffect i, emittedFeatureEffect emitted returnsValue with
    | some rawEffect, some emittedEffect => rawEffect == emittedEffect
    | _, _ => false

/-- Bind every control-flow operation and every operation that propagates a known
    feature fact to the actual emitted instruction. Unknown operations may not
    emit an unsupported hole on a reachable path. -/
def featureOpMatches (raw : RawMethod) (i : RawInstruction) (emitted : Op) : Bool := Id.run do
  -- These terminal/transfer encodings have no admitted emitted counterpart.
  if i.opcode ∈ [39, 122, 220, 65041, 65050] then return false
  if let some word := constant32 i then
    return match emitted with | .const32 actual => word == actual | _ => false
  if let .call site := i.operand then
    if let some feature := featureGetter site then
      return match emitted with | .feature actual => i.opcode == 40 && feature == actual | _ => false
  if i.opcode ∈ [6, 7, 8, 9, 17, 65036, 10, 11, 12, 13, 19, 65038] then
    let some index := localIndex i | return false
    let narrow := match raw.locals[index]? with
      | some (.atom _ "System.Boolean") => some NarrowKind.unsigned8 | _ => none
    return match emitted with
      | .local actual actualNarrow => i.opcode ∈ [6, 7, 8, 9, 17, 65036] && actual == index &&
          (!eligibleFact raw index (some 0) || actualNarrow == narrow)
      | .setLocal actual actualNarrow => i.opcode ∈ [10, 11, 12, 13, 19, 65038] && actual == index &&
          (!eligibleFact raw index (some 0) || actualNarrow == narrow)
      | _ => false
  if i.opcode ∈ [18, 65037] then
    return match localIndex i, emitted with
      | some index, .localAddr actual => index == actual
      | _, _ => false
  -- Argument homes are appended after all raw locals. Their precise mapping is
  -- independently checked by ParameterHomesValid; they cannot alias tracked locals.
  if i.opcode ∈ [15, 65034] then
    return match emitted with | .localAddr index => raw.locals.length <= index | _ => false
  if i.opcode ∈ [16, 65035] then
    return match emitted with | .setLocal index none => raw.locals.length <= index | _ => false
  let emitted := match emitted with
    | .nativeBinary operation => if i.opcode ∈ [95, 96, 97, 65025] ||
        (46 <= i.opcode && i.opcode <= 55) || (59 <= i.opcode && i.opcode <= 68) then operation else emitted
    | _ => emitted
  return match i.opcode, i.operand, emitted with
    | 37, _, .dup | 95, _, .band | 96, _, .bor | 97, _, .bxor | 65025, _, .eq => true
    | 43, .target x, .branch y | 56, .target x, .branch y
    | 44, .target x, .brzero y | 57, .target x, .brzero y
    | 45, .target x, .brnonzero y | 58, .target x, .brnonzero y
    | 46, .target x, .beq y | 59, .target x, .beq y
    | 47, .target x, .bge y | 60, .target x, .bge y
    | 48, .target x, .bgt y | 61, .target x, .bgt y
    | 49, .target x, .ble y | 62, .target x, .ble y
    | 50, .target x, .blt y | 63, .target x, .blt y
    | 51, .target x, .bne y | 64, .target x, .bne y
    | 52, .target x, .bgeu y | 65, .target x, .bgeu y
    | 53, .target x, .bgtu y | 66, .target x, .bgtu y
    | 54, .target x, .bleu y | 67, .target x, .bleu y
    | 55, .target x, .bltu y | 68, .target x, .bltu y => x == y
    | 69, .targets x, .switch y => x == y
    | 42, _, .ret _ => true
    | _, _, .unsupported _ | _, _, .throw _ | _, _, .feature _ | _, _, .branch _ | _, _, .switch _
    | _, _, .brzero _ | _, _, .brnonzero _ => false
    | opcode, _, _ => !(opcode ∈ [37, 95, 96, 97, 65025, 42] || (43 <= opcode && opcode <= 69)) &&
        fallbackFeatureEffect i emitted

/-- Fold operands emit nothing, a type comparison emits its decided word and a folded
    `throw` raises its constructed type. Outside a decided test, type handles and
    `System.Type` calls have no admitted translation. -/
def featureOpMatchesAt (raw : RawMethod) (role : Option FoldRole)
    (i : RawInstruction) (emitted : Op) : Bool :=
  match role, emitted with
  | some .head, .nop | some .interior, .nop => true
  | some (.result value), .const32 word => word == if value then 1 else 0
  | some (.raise name), .throw exception => name == exception
  | some _, _ => false
  | none, _ => !typeTestInstruction i && featureOpMatches raw i emitted

private def checkFeatureSite (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureCertificate) (roles : List (Option FoldRole)) :
    (RawInstruction × Option FoldRole) × Nat → Option FeatureState → Op → Bool
  | _, none, .unsupported _ => true
  | ((i, role), pc), some state, emitted =>
    wellShaped raw state && featureOpMatchesAt raw role i emitted &&
      match featureTransferAt raw profile role i state, featureSuccessors pc i state with
      | some after, some successors =>
        -- Roles are contiguous, so only a non-fallthrough edge can enter a fold's interior.
        successors.all (fun target => target == pc + 1 || foldEntry roles target) &&
        successors.all fun target =>
          match certificate[target]? with
          | some (some incoming) => after.weakens incoming
          | _ => false
      | _, _ => false
  | _, none, _ => false

/-- No optional sites: entry, every raw PC, the entire parameter-reachability mask,
    every successor, and all unsupported holes are covered. -/
def FeatureFlowValid (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureCertificate) (reachable : List Bool) (code : List Op) : Prop :=
  certificate.length = raw.code.length ∧ code.length = raw.code.length ∧
  reachable = certificate.map Option.isSome ∧
  certificate[0]? = some (some { stack := [], locals := List.replicate raw.locals.length none }) ∧
  all3 (checkFeatureSite raw profile certificate (foldRoles raw.code))
    (raw.code.zip (foldRoles raw.code)).zipIdx certificate code = true

instance (raw : RawMethod) (profile : FeatureProfile) (certificate : FeatureCertificate)
    (reachable : List Bool) (code : List Op) : Decidable (FeatureFlowValid raw profile certificate reachable code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A feature fact denotes an exact word, while unknown admits any value. -/
def FactRepresents (fact : Option W32) (value : Value) : Prop :=
  match fact with | none => True | some word => value = .i32 word

theorem factWeakens_preserves {source target : Option W32} {value : Value}
    (weakens : factWeakens source target = true) (represents : FactRepresents source value) :
    FactRepresents target value := by
  cases target with
  | none => trivial
  | some word =>
    simp [factWeakens] at weakens
    simpa [← weakens] using represents

inductive FactsRepresent : List (Option W32) → List Value → Prop where
  | nil : FactsRepresent [] []
  | cons {fact value rest values} : FactRepresents fact value →
      FactsRepresent rest values → FactsRepresent (fact :: rest) (value :: values)

/-- Weakening at a join preserves every concrete stack/local valuation. -/
theorem factsWeaken_preserves {source target : List (Option W32)} {values : List Value}
    (weakens : factsWeaken source target = true)
    (represents : FactsRepresent source values) :
    FactsRepresent target values := by
  induction represents generalizing target with
  | nil =>
    cases target with
    | nil => exact .nil
    | cons x xs => simp [factsWeaken] at weakens
  | @cons fact value rest values head tail ih =>
    cases target with
    | nil => simp [factsWeaken] at weakens
    | cons next remaining =>
      simp only [factsWeaken, List.length_cons, Nat.add_right_cancel_iff,
        List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at weakens
      exact .cons (factWeakens_preserves weakens.2.1 head)
        (ih (by simpa [factsWeaken] using And.intro weakens.1 weakens.2.2))

/-- Abstract execution edges are computed from raw instructions and incoming
    facts, rather than copied from the extractor's claimed reachable mask. -/
def FeatureEdge (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureCertificate) (pc target : Nat) : Prop :=
  ∃ i role state after successors,
    (raw.code.zip (foldRoles raw.code))[pc]? = some (i, role) ∧
    certificate[pc]? = some (some state) ∧
    featureTransferAt raw profile role i state = some after ∧
    featureSuccessors pc i state = some successors ∧ target ∈ successors

/-- Validation establishes closure under every independently recomputed edge,
    including backedges and every switch destination. -/
theorem FeatureFlowValid.edge_closed {raw : RawMethod} {profile : FeatureProfile}
    {certificate : FeatureCertificate} {reachable : List Bool} {code : List Op}
    (valid : FeatureFlowValid raw profile certificate reachable code)
    {pc target : Nat} (edge : FeatureEdge raw profile certificate pc target) :
    ∃ incoming, certificate[target]? = some (some incoming) := by
  obtain ⟨i, role, state, after, successors, hi, hs, ht, hn, member⟩ := edge
  have zipped := (List.getElem?_eq_some_iff.mp hi).1
  have bound : pc < code.length := by
    rw [valid.2.1]; exact Nat.lt_of_lt_of_le zipped (by simp [List.length_zip, Nat.min_le_left])
  have indexed : (raw.code.zip (foldRoles raw.code)).zipIdx[pc]? = some ((i, role), pc) := by
    simp [List.getElem?_zipIdx, hi]
  have checked := all3_at valid.2.2.2.2 indexed hs (List.getElem?_eq_getElem bound)
  simp only [checkFeatureSite, ht, hn, Bool.and_eq_true] at checked
  have successor := List.all_eq_true.mp checked.2.2 target member
  cases hnext : certificate[target]? with
  | none => simp [hnext] at successor
  | some next => cases next with
    | none => simp [hnext] at successor
    | some incoming => exact ⟨incoming, rfl⟩

inductive FeaturePath (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureCertificate) : Nat → Prop where
  | entry : FeaturePath raw profile certificate 0
  | next {pc target} : FeaturePath raw profile certificate pc →
      FeatureEdge raw profile certificate pc target → FeaturePath raw profile certificate target

/-- Arbitrarily many steps through the validated graph remain in the emitted
    reachable mask; this includes cyclic paths without a bound on iterations. -/
theorem FeatureFlowValid.path_reachable {raw : RawMethod} {profile : FeatureProfile}
    {certificate : FeatureCertificate} {reachable : List Bool} {code : List Op}
    (valid : FeatureFlowValid raw profile certificate reachable code)
    {pc : Nat} (path : FeaturePath raw profile certificate pc) : reachable[pc]? = some true := by
  have present : ∃ incoming, certificate[pc]? = some (some incoming) := by
    cases path with
    | entry => exact ⟨_, valid.2.2.2.1⟩
    | next _ edge => exact valid.edge_closed edge
  obtain ⟨incoming, found⟩ := present
  rw [valid.2.2.1, List.getElem?_map, found]
  rfl

#print axioms factWeakens_preserves
#print axioms factsWeaken_preserves
#print axioms FeatureFlowValid.edge_closed
#print axioms FeatureFlowValid.path_reachable

end CIL.Extraction


