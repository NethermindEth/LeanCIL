import CIL.Extraction.Generics
import CIL.Extraction.FeatureEffects
import CIL.Extraction.Folds
import CIL.Extraction.FlowIndex
import CIL.Extraction.FeatureLocals
import CIL.Semantics
import Lean.Elab.Tactic.BuiltinTactic

/-!
# Feature flow

Hardware feature tests such as `Avx2.IsSupported` are constants under a fixed profile, and
the extractor prunes the branches they decide. `FeatureFlowValid` checks that pruning: an
abstract interpretation tracks known 32-bit words on the stack and in eligible locals, its
transfer function and successor edges are recomputed here from the raw body, and the
extractor's per-pc certificate must be closed under them. Only pcs the certificate reaches
may be live; every other emitted instruction must be an `.unsupported` hole.

The same pass binds each raw instruction to its emitted counterpart, exactly for control
flow, locals and feature tests, and by stack effect for everything else.

A parameterless static Boolean call pushes the word `constantReturn` reads from the callee's own
certificate, which the whole-program obligation validates alongside the caller's. Known words
only decide which pcs are live, and every pc they rule out is emitted as an `.unsupported` hole
that has no step. A wrong claim, cyclic or not, therefore sends execution into a hole that faults:
it cannot make a successful outcome provable, only unreachable.
-/

namespace CIL.Extraction

/-- Feature facts use stack order (top first), with the local facts held as `Locals`. `none`
    includes every runtime value; `some` describes exactly a 32-bit evaluation-stack word. -/
structure FeatureFacts (Locals : Type) where
  stack : List (Option W32)
  locals : Locals
  deriving DecidableEq, Repr

/-- A certificate state. Its `locals` hold only the known local facts, as (local index, word)
    pairs in strictly increasing index order; a local without an entry has no known fact. -/
abbrev FeatureState := FeatureFacts (List (Nat × W32))

/-- The claimed state at each raw pc; `none` marks a pc the certificate claims unreachable. -/
abbrev FeatureCertificate := List (Option FeatureState)

/-- The specification's state, with one fact per local. -/
abbrev FeatureListState := FeatureFacts (List (Option W32))

/-- The specification's certificate: one fact per local in every claimed state. -/
abbrev FeatureListCertificate := List (Option FeatureListState)

/-- How a state holds the facts of a method's locals, with the method's eligibility rule. -/
structure LocalFacts (Locals : Type) where
  /-- Whether a local may hold a fact; unknown is admitted everywhere. -/
  eligible : Nat → Option W32 → Bool
  /-- The fact of a local, or `none` for an index outside the method's locals. -/
  load : Locals → Nat → Option (Option W32)
  /-- Record a fact for a local, or `none` for an index outside the method's locals. -/
  store : Locals → Nat → Option W32 → Option Locals
  /-- The facts cover the method's locals and each known fact is eligible. -/
  fits : Locals → Bool
  /-- Every fact of the second argument is unknown or the same as in the first. -/
  weakens : Locals → Locals → Bool

/-- One fact per local over `count` locals: the specification's form. -/
def LocalFacts.list (count : Nat) (eligible : Nat → Option W32 → Bool) :
    LocalFacts (List (Option W32)) where
  eligible := eligible
  load locals index := locals[index]?
  store locals index fact :=
    if index >= locals.length then none else some (locals.set index fact)
  fits locals :=
    locals.length == count && (locals.zipIdx).all fun (fact, index) => eligible index fact
  weakens := factsWeaken

/-- Known facts over `count` locals; reads, stores and weakening walk the known entries only. -/
def LocalFacts.known (count : Nat) (eligible : Nat → Option W32 → Bool) :
    LocalFacts (List (Nat × W32)) where
  eligible := eligible
  load locals index := if index < count then some (locals.lookup index) else none
  store locals index fact := if index < count then some (storeKnown index fact locals) else none
  fits locals :=
    knownBelow count 0 locals && locals.all fun entry => eligible entry.1 (some entry.2)
  weakens source target := target.isSublist source

/-- Stack and locals of `target` both weaken those of `source`. -/
def FeatureFacts.weakens {Locals : Type} (facts : LocalFacts Locals)
    (source target : FeatureFacts Locals) : Bool :=
  factsWeaken source.stack target.stack && facts.weakens source.locals target.locals

/-- The specification state a certificate state stands for over `count` locals. -/
def FeatureState.expand (count : Nat) (state : FeatureState) : FeatureListState :=
  { stack := state.stack, locals := expandKnown count state.locals }

/-- The admitted feature classes, by name under `System.Runtime.Intrinsics`.
    .NET 10 reports `AdvSimd.Arm64` exactly when it reports `AdvSimd`, `Avx512Vbmi.VL` exactly
    when it reports `Avx512Vbmi`, and each `Aes.X64` or `Aes.Arm64` exactly when it reports that
    architecture's `Aes` (docs/RUNTIME-PROFILES.md). -/
private def featureNames : List (String × Feature) := [
  ("Arm.AdvSimd", .advSimd), ("Arm.AdvSimd/Arm64", .advSimd), ("Arm.ArmBase/Arm64", .armBase64),
  ("X86.Sse2", .sse2), ("X86.Ssse3", .ssse3), ("X86.Sse41", .sse41),
  ("X86.Sse42", .sse42), ("X86.Avx", .avx), ("X86.Avx2", .avx2),
  ("X86.Avx512F", .avx512F), ("X86.Avx512F/VL", .avx512FVL),
  ("X86.Avx512DQ", .avx512DQ), ("X86.Avx512DQ/VL", .avx512DQVL),
  ("X86.Avx512Vbmi", .avx512Vbmi), ("X86.Avx512Vbmi/VL", .avx512Vbmi),
  ("X86.Aes", .aes), ("X86.Aes/X64", .aes), ("Arm.Aes", .armAes), ("Arm.Aes/Arm64", .armAes),
  ("X86.Bmi1", .bmi1), ("X86.Bmi2/X64", .bmi2), ("X86.X86Base/X64", .x86Base64),
  ("Vector128", .vector128Accelerated), ("Vector256", .vector256Accelerated)]

/-- The exact assembly, return type and namespace shared by feature getters. -/
private def featurePrefix := intrinsicsScope ++ "::System.Boolean System.Runtime.Intrinsics."

/-- The class and member portion of each admitted feature getter. -/
private def featureSuffix (name : String) (feature : Feature) : String :=
  name ++ "::" ++
    (if feature == .vector128Accelerated || feature == .vector256Accelerated then
      "get_IsHardwareAccelerated" else "get_IsSupported") ++ "()"

/-- Literal identities avoid rebuilding common assembly and namespace prefixes per lookup. -/
private def featureIdentities : List (List UInt8) := by
  run_tac do
    let expression ← Lean.Elab.Term.elabTerm
      (← `(featureNames.map fun (name, feature) =>
        (featureSuffix name feature).toByteArray.data.toList)) none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← Lean.instantiateMVars expression
    let values ← unsafe Lean.Meta.evalExpr (List (List UInt8))
      (← Lean.Meta.inferType expression) expression
    Lean.Elab.Tactic.closeMainGoal `featureIdentities (Lean.toExpr values)

set_option maxRecDepth 4096 in
/-- The kernel checks every materialized identity against the original feature names. -/
private theorem featureIdentities_eq : featureIdentities =
    featureNames.map (fun (name, feature) =>
      (featureSuffix name feature).toByteArray.data.toList) := by rfl
#print axioms featureIdentities_eq

/-- Remove an exact byte prefix, rejecting mismatches and truncated identities. -/
private def stripFeaturePrefix : List UInt8 → List UInt8 → Option (List UInt8)
  | [], bytes => some bytes
  | first :: expected, actual :: bytes =>
    if first == actual then stripFeaturePrefix expected bytes else none
  | _, _ => none

/-- Successful prefix removal retains exactly the remaining bytes. -/
private theorem stripFeaturePrefix_eq (expected bytes suffix : List UInt8) :
    stripFeaturePrefix expected bytes = some suffix ↔ bytes = expected ++ suffix := by
  induction expected generalizing bytes with
  | nil => simp [stripFeaturePrefix]
  | cons first expected ih =>
    cases bytes with
    | nil => simp [stripFeaturePrefix]
    | cons actual bytes =>
      by_cases equal : first = actual
      · subst actual
        simp [stripFeaturePrefix, ih]
      · simp [stripFeaturePrefix, equal, beq_iff_eq, Ne.symm equal]
#print axioms stripFeaturePrefix_eq

/-- The class and member bytes under the exact feature-getter prefix. -/
private def featureSignature (identity : String) : Option (List UInt8) :=
  stripFeaturePrefix featurePrefix.toByteArray.data.toList identity.toByteArray.data.toList

/-- Platform query names whose exact signatures must bind emitted constants. -/
def platformQuery (site : CallSite) : Bool :=
  match site.declaringType with
  | .atom _ owner =>
    (site.name == "get_Size" && owner ∈ ["System.IntPtr", "System.UIntPtr"]) ||
      (site.name == "get_Is64BitProcess" && owner == "System.Environment")
  | _ => false

/-- Exact process-width getters under the supported 64-bit runtime profiles. -/
def platformConstant (site : CallSite) : Option W32 := do
  let .atom scope owner := site.declaringType | none
  if !platformQuery site || scope != runtimeScope || site.parameterCount != 0 ||
      !site.parameterTypes.isEmpty || site.hasThis || !site.returnsValue ||
      site.ownerArgumentCount != 0 || !site.typeArguments.isEmpty then none
  else
    let result := if site.name == "get_Size" then "System.Int32" else "System.Boolean"
    if site.returnType != .atom runtimeScope result ||
        site.target != .external (runtimeScope ++ "::" ++ result ++ " " ++ owner ++
          "::" ++ site.name ++ "()") then none
    else some (if site.name == "get_Size" then 8 else 1)

/-- `ldsfld` of the System.Runtime `BitConverter` static Boolean, whose only such field is
    `IsLittleEndian`; the raw operand omits field names, so the extractor checks the member.
    Valid profiles are little-endian, so the load is the constant 1. -/
def platformField (instruction : RawInstruction) : Option W32 :=
  if instruction.opcode == 126 && instruction.operand ==
      .field (.atom runtimeScope "System.BitConverter") 0 (.atom runtimeScope "System.Boolean") true
  then some 1 else none

/-- Classify reference-free storage against a table whose `LayoutsValid` is checked separately.
    Aggregate identity lookup does not revalidate fields or confer memory access authority. -/
def referenceFreeStorage (layouts : Array RawLayout) : TypeExpr → Bool
  | type@(.atom ..) | type@(.enum _ (.atom ..)) =>
    match typeStorage [] type with | some (.field _) => true | _ => false
  | .aggregate identity index => (layouts[index]?).any (·.identity == identity)
  | type => (integerVectorWidth type).isSome

/-- Reserve the runtime query name even when malformed metadata prevents exact recognition. -/
def referenceContentQuery (site : CallSite) : Bool :=
  site.name == "IsReferenceOrContainsReferences" &&
    (match site.declaringType with
    | .atom _ owner => owner == "System.Runtime.CompilerServices.RuntimeHelpers"
    | _ => false)

/-- Bind a false reference-content answer to an exact helper and independently admitted type. -/
def referenceContentConstant (layouts : Array RawLayout) (site : CallSite) : Option W32 := do
  let [type] := site.typeArguments | none
  if !referenceContentQuery site ||
      site.declaringType != .atom runtimeScope "System.Runtime.CompilerServices.RuntimeHelpers" ||
      site.parameterCount != 0 || !site.parameterTypes.isEmpty || site.hasThis ||
      !site.returnsValue || site.ownerArgumentCount != 0 ||
      site.returnType != .atom runtimeScope "System.Boolean" ||
      site.target != .external (runtimeScope ++
        "::System.Boolean System.Runtime.CompilerServices.RuntimeHelpers::" ++
        "IsReferenceOrContainsReferences()") || !referenceFreeStorage layouts type then none
  else some 0

/-- Identify getters from raw member and assembly identity, never an emitter-supplied flag. -/
def featureGetter (site : CallSite) : Option Feature := do
  let .external identity := site.target | none
  if site.parameterCount != 0 || site.hasThis || !site.returnsValue ||
      !site.typeArguments.isEmpty then none
  else
    let signature := featureSignature identity
    ((featureIdentities.zip (featureNames.map Prod.snd)).find?
      fun (expected, _) => signature == some expected).map Prod.snd

/-- UTF-8 byte equality is exact string equality, including non-ASCII metadata. -/
private theorem featureBytes_eq (identity suffix : String) :
    (featureSignature identity == some suffix.toByteArray.data.toList) =
      (identity == featurePrefix ++ suffix) := by
  apply Bool.eq_iff_iff.mpr
  simp only [featureSignature, beq_iff_eq, stripFeaturePrefix_eq]
  rw [← ByteArray.toList_data_append, ← String.toByteArray_append, Array.toList_inj]
  constructor
  · intro equal
    exact String.toByteArray_inj.mp (ByteArray.ext equal)
  · intro equal
    cases equal
    rfl
#print axioms featureBytes_eq
/-- Literal lookup preserves the admitted getters for every raw call site. -/
theorem featureGetter_eq_original (site : CallSite) : featureGetter site = (do
    let .external identity := site.target | none
    if site.parameterCount != 0 || site.hasThis || !site.returnsValue ||
        !site.typeArguments.isEmpty then none
    else (featureNames.find? fun (name, feature) =>
      identity == intrinsicsScope ++ "::System.Boolean System.Runtime.Intrinsics." ++ name ++
        "::" ++ (if feature == .vector128Accelerated || feature == .vector256Accelerated then
          "get_IsHardwareAccelerated" else "get_IsSupported") ++ "()").map Prod.snd) := by
  simp only [featureGetter, featureIdentities_eq, List.zip_map', List.find?_map,
    Function.comp_def, featureBytes_eq, Option.map_map, featurePrefix, featureSuffix,
    String.append_assoc]
#print axioms featureGetter_eq_original

/-- A certificate state fits the method: its local facts fit the method's locals and the stack
    holds at most `maxStack` entries. -/
private def wellShaped {Locals : Type} (raw : RawMethod) (facts : LocalFacts Locals)
    (state : FeatureFacts Locals) : Bool :=
  facts.fits state.locals && state.stack.length <= raw.maxStack

/-- The word an `ldc.i4` instruction pushes, in any of its forms. -/
private def constant32 (instruction : RawInstruction) : Option W32 :=
  match instruction.opcode, instruction.operand with
  | 21, .none => some (BitVec.ofInt 32 (-1))
  | 31, .integer n | 32, .integer n => some (BitVec.ofInt 32 n)
  | n, .none => if 22 <= n && n <= 30 then some (BitVec.ofNat 32 (n - 22)) else none
  | _, _ => none

/-- The word a static, parameterless Boolean method returns, read from its own feature
    certificate: every reachable `ret` sees the same 0 or 1 on top of the stack, and at least one
    `ret` is reachable. Any other method, or a certificate without a reachable `ret`, has none. -/
def constantReturn (closed : RawMethod) (certificate : FeatureCertificate) : Option W32 :=
  if closed.hasThis || !closed.parameters.isEmpty ||
      closed.returnType != .atom runtimeScope "System.Boolean" then none else
  match (closed.code.zip certificate).filterMap returned with
  | some word :: rest =>
    if (word == 0 || word == 1) && rest.all (· == some word) then some word else none
  | _ => none
where
  /-- The fact a reachable `ret` returns; every other pc contributes nothing. -/
  returned : RawInstruction × Option FeatureState → Option (Option W32)
    | (⟨_, 42, _⟩, some state) => some state.stack.head?.join
    | _ => none

/-- The word an emitted parameterless call pushes when `constants` knows its callee's return.
    `constants` reads each callee's own certificate, which its own obligation validates. -/
def calleeConstant (constants : Nat → Option W32) : Instruction → Option W32
  | .call index 0 => constants index
  | _ => none

/-- Fixed CLI stack effects; unknown values are never interpreted as false.
    Variable call and return effects are handled from raw signatures below. -/
def rawStackEffect : Nat → Option (Nat × Nat)
  | 0 | 1 | 39 | 43 | 56 | 220 | 65042 | 65043 | 65044 | 65046 | 65049 | 65050
  | 65054 => some (0, 0)
  | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 14 | 15 | 17 | 18 | 20 | 21 | 22 | 23 | 24 | 25 | 26
  | 27 | 28 | 29 | 30 | 31 | 32 | 33 | 34 | 35 | 114 | 126 | 127 | 208 | 65024 | 65030
  | 65033 | 65034 | 65036 | 65037 | 65052 => some (0, 1)
  | 10 | 11 | 12 | 13 | 16 | 19 | 38 | 44 | 45 | 57 | 58 | 69 | 122 | 128 | 65035 | 65038
  | 65041 | 65045 => some (1, 0)
  | 46 | 47 | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 59 | 60 | 61 | 62 | 63 | 64 | 65 | 66
  | 67 | 68 | 81 | 82 | 83 | 84 | 85 | 86 | 87 | 112 | 125 | 129 | 223 => some (2, 0)
  | 70 | 71 | 72 | 73 | 74 | 75 | 76 | 77 | 78 | 79 | 80 | 101 | 102 | 103 | 104 | 105 | 106
  | 107 | 108 | 109 | 110 | 113 | 116 | 117 | 118 | 121 | 123 | 124 | 130 | 131 | 132 | 133
  | 134 | 135 | 136 | 137 | 138 | 139 | 140 | 141 | 142 | 165 | 179 | 180 | 181 | 182 | 183
  | 184 | 185 | 186 | 194 | 195 | 198 | 209 | 210 | 211 | 212 | 213 | 224 | 65031 | 65039
  | 65053 => some (1, 1)
  | 88 | 89 | 90 | 91 | 92 | 93 | 94 | 95 | 96 | 97 | 98 | 99 | 100 | 143 | 144 | 145 | 146
  | 147 | 148 | 149 | 150 | 151 | 152 | 153 | 154 | 163 | 214 | 215 | 216 | 217 | 218 | 219
  | 65025 | 65026 | 65027 | 65028 | 65029 => some (2, 1)
  | 155 | 156 | 157 | 158 | 159 | 160 | 161 | 162 | 164 | 65047 | 65048 => some (3, 0)
  | _ => none

/-- Pops `pops` facts and pushes `pushes` unknowns; fails on stack underflow. -/
private def forget (stack : List (Option W32)) (pops pushes : Nat) : Option (List (Option W32)) :=
  if pops <= stack.length then some (List.replicate pushes none ++ stack.drop pops) else none

/-- Short and long compare branches share the CLI's ten-operation ordering. -/
def comparisonBranchIndex (opcode : Nat) : Option Nat :=
  if 46 <= opcode && opcode <= 55 then some (opcode - 46)
  else if 59 <= opcode && opcode <= 68 then some (opcode - 59) else none

/-- Known int32 comparisons use the value evaluator, including signedness and operand order. -/
def constantComparison (opcode : Nat) (left right : W32) : Option W32 := do
  let index ← match opcode with
    | 65025 => some 0 | 65026 => some 2 | 65027 => some 7
    | 65028 => some 4 | 65029 => some 9
    | _ => comparisonBranchIndex opcode
  let (operation, negate) ← match index with
    | 0 => some (Instruction.ceq, false) | 5 => some (.ceq, true)
    | 1 => some (.clt, true) | 2 => some (.cgt, false)
    | 3 => some (.cgt, true) | 4 => some (.clt, false)
    | 6 => some (.clt_un, true) | 7 => some (.cgt_un, false)
    | 8 => some (.cgt_un, true) | 9 => some (.clt_un, false)
    | _ => none
  let .i32 value ← binary operation (.i32 left) (.i32 right) | none
  return if negate then (if value == 0 then 1 else 0) else value

/-- The stack effect of an instruction that neither pushes a constant word nor accesses a local,
    recomputed from raw CLI encodings and metadata. -/
private def featureStackTransfer (layouts : Array RawLayout) (raw : RawMethod)
    (profile : FeatureProfile) (instruction : RawInstruction) (stack : List (Option W32)) :
    Option (List (Option W32)) := do
  -- `dup`, then bitwise operations and comparisons over known words.
  if instruction.opcode == 37 then
    let value :: rest := stack | none
    return value :: value :: rest
  if instruction.opcode ∈ [95, 96, 97] ||
      (65025 <= instruction.opcode && instruction.opcode <= 65029) then
    let right :: left :: rest := stack | none
    let value := do
      let a ← left
      let b ← right
      if instruction.opcode == 95 then some (a &&& b)
        else if instruction.opcode == 96 then some (a ||| b)
        else if instruction.opcode == 97 then some (a ^^^ b)
        else constantComparison instruction.opcode a b
    return value :: rest
  -- `call` and `newobj`; a feature getter pushes the profile's answer.
  if instruction.opcode == 41 then
    let .indirectCall result parameters false false 0 := instruction.operand | none
    forget stack (parameters.length + 1) (if result == .void then 0 else 1)
  else
  if instruction.opcode == 40 || instruction.opcode == 111 || instruction.opcode == 115 then
    let .call site := instruction.operand | none
    let next ← forget stack
      (site.parameterCount + if instruction.opcode != 115 && site.hasThis then 1 else 0) 0
    if let some constant := referenceContentConstant layouts site <|> platformConstant site then
      if instruction.opcode != 40 then none else
        return some constant :: next
    if let some feature := featureGetter site then
      if instruction.opcode != 40 then none else
        return some (if profile.evaluate feature then 1 else 0) :: next
    return if instruction.opcode == 115 || site.returnsValue then none :: next else next
  -- `ret`, then every other opcode by its fixed stack effect.
  if instruction.opcode == 42 then forget stack (if raw.returnType == .void then 0 else 1) 0
  else
    let (pops, pushes) ← rawStackEffect instruction.opcode
    forget stack pops pushes

/-- Recompute a transfer from raw CLI encodings and metadata, independently of the
    extractor's worklist and its claimed incoming/outgoing facts. -/
private def featureTransferWith {Locals : Type} (layouts : Array RawLayout) (raw : RawMethod)
    (facts : LocalFacts Locals)
    (profile : FeatureProfile)
    (instruction : RawInstruction) (state : FeatureFacts Locals) :
    Option (FeatureFacts Locals) := do
  if let some word := constant32 instruction <|> platformField instruction then
    return { state with stack := some word :: state.stack }
  -- `ldloc` and `stloc`; a store keeps its fact only in an eligible local.
  if instruction.opcode ∈ [6, 7, 8, 9, 17, 65036] then
    let index ← localIndex instruction
    let value ← facts.load state.locals index
    return { state with stack := value :: state.stack }
  if instruction.opcode ∈ [10, 11, 12, 13, 19, 65038] then
    let index ← localIndex instruction
    let value :: stack := state.stack | none
    let locals ← facts.store state.locals index
      (if facts.eligible index value then value else none)
    return { stack, locals }
  let stack ← featureStackTransfer layouts raw profile instruction state.stack
  return { state with stack }

/-- The known facts of a method's locals under the raw local-eligibility rule. -/
def knownLocals (raw : RawMethod) : LocalFacts (List (Nat × W32)) :=
  LocalFacts.known raw.locals.length (featureLocalEligible raw)

/-- Recompute the transfer of a certificate state using the raw local-eligibility rule. -/
def featureTransfer (layouts : Array RawLayout) (raw : RawMethod) :=
  featureTransferWith layouts raw (knownLocals raw)

/-- A decided type test replaces the raw comparison result by its exact word, and a
    parameterless static call pushes `constant`, the word its emitted callee is known to return. -/
private def featureTransferAtWith {Locals : Type} (layouts : Array RawLayout) (raw : RawMethod)
    (facts : LocalFacts Locals)
    (profile : FeatureProfile) (constant : Option W32) (role : Option FoldRole)
    (instruction : RawInstruction) (state : FeatureFacts Locals) :
    Option (FeatureFacts Locals) :=
  match role with
  | some .tailCall => match instruction.operand with
    | .indirectCall _ parameters false false 0 =>
      if state.stack.length == parameters.length + 1 then
        featureTransferWith layouts raw facts profile instruction state else none
    | .call site =>
      if state.stack.length == site.parameterCount + (if site.hasThis then 1 else 0) then
        featureTransferWith layouts raw facts profile instruction state else none
    | _ => none
  | some (.result value) => match state.stack with
    | _ :: _ :: stack => some { state with stack := some (if value then 1 else 0) :: stack }
    | _ => none
  | _ => match instruction with
    | ⟨_, 40, .call site⟩ =>
      match site.parameterCount == 0 && !site.hasThis && site.returnsValue, constant with
      | true, some word => some { state with stack := some word :: state.stack }
      | _, _ => featureTransferWith layouts raw facts profile instruction state
    | _ => featureTransferWith layouts raw facts profile instruction state

/-- The folded transfer of a certificate state, stated independently of any local-eligibility
    index. -/
def featureTransferAt (layouts : Array RawLayout) (raw : RawMethod) :=
  featureTransferAtWith layouts raw (knownLocals raw)

/-- The taken target or the next instruction for a decided conditional branch. -/
private def selectedSuccessor (pc target : Nat) (taken : Bool) : List Nat :=
  [if taken then target else pc + 1]

/-- Known integer conditions and closed type tests select an edge; unknowns retain both. -/
def featureSuccessors (role : Option FoldRole) (pc : Nat)
    (instruction : RawInstruction) (stack : List (Option W32)) :
    Option (List Nat) :=
  if let some (.typeBranch taken) := role then
    match instruction.operand with
    | .target target => some (selectedSuccessor pc target taken)
    | _ => none
  -- `ret`, `throw`, `rethrow`, `endfinally` and `endfilter` leave the method or handler.
  else if instruction.opcode == 42 || instruction.opcode == 122 || instruction.opcode == 65050 ||
      instruction.opcode == 220 || instruction.opcode == 65041 then some []
  -- `br`, then `switch`.
  else if instruction.opcode == 43 || instruction.opcode == 56 then
    match instruction.operand with | .target target => some [target] | _ => none
  else if instruction.opcode == 69 then
    match instruction.operand with
    | .targets targets => match stack with
      | some selector :: _ => some [targets[selector.toNat]?.getD (pc + 1)]
      | _ => some ((pc + 1) :: targets)
    | _ => none
  -- Conditional branches use the incoming facts before their operands are popped.
  else if (44 <= instruction.opcode && instruction.opcode <= 55) ||
      (57 <= instruction.opcode && instruction.opcode <= 68) then do
    let .target target := instruction.operand | none
    if instruction.opcode ∈ [44, 45, 57, 58] then
      match stack with
      | some value :: _ =>
        return selectedSuccessor pc target
          ((value != 0) == (instruction.opcode == 45 || instruction.opcode == 58))
      | _ => return [target, pc + 1]
    else match stack with
      | some right :: some left :: _ =>
        match constantComparison instruction.opcode left right with
        | some value => return selectedSuccessor pc target (value != 0)
        | none => return [target, pc + 1]
      | _ => return [target, pc + 1]
  else some [pc + 1]

/-- The raw stack effect, with calls taken from their signature. -/
private def rawFeatureEffect (instruction : RawInstruction) : Option (Nat × Nat) := do
  if instruction.opcode == 41 then
    let .indirectCall result parameters false false 0 := instruction.operand | none
    return (parameters.length + 1, if result == .void then 0 else 1)
  if instruction.opcode == 40 || instruction.opcode == 111 || instruction.opcode == 115 then
    let .call site := instruction.operand | none
    return (site.parameterCount + if instruction.opcode != 115 && site.hasThis then 1 else 0,
      if instruction.opcode == 115 || site.returnsValue then 1 else 0)
  else rawStackEffect instruction.opcode

/-- Raw and emitted instructions have the same known stack effect, and an emitted call
    or construction comes from the matching raw opcode. -/
private def fallbackFeatureEffect (instruction : RawInstruction) (emitted : Instruction) : Bool :=
  let returnsValue := match instruction.operand with
    | .call site => site.returnsValue
    | .indirectCall result .. => result != .void
    | _ => false
  let properCall := match emitted with
    | .call .. => instruction.opcode == 40 || instruction.opcode == 111
    | .callInstance .. | .callVirtual .. => instruction.opcode == 111
    | .newAggregate .. | .newObject .. => instruction.opcode == 115
    | .castclass _ | .isinst _ =>
      (typeTestSource emitted).any fun (opcode, _) => opcode == instruction.opcode
    | _ => true
  properCall && match rawFeatureEffect instruction, emittedFeatureEffect emitted returnsValue with
    | some rawEffect, some emittedEffect => rawEffect == emittedEffect
    | _, _ => false

/-- Bind every control-flow operation and every operation that propagates a known
    feature fact to the actual emitted instruction. Unknown operations may not
    emit an unsupported hole on a reachable path. -/
def featureOpMatches (layouts : Array RawLayout) (raw : RawMethod)
    (instruction : RawInstruction) (emitted : Instruction) : Bool :=
    Id.run do
  -- These terminal/transfer encodings have no admitted emitted counterpart.
  if instruction.opcode ∈ [39, 122, 220, 65041, 65044, 65050] then return false
  if (match emitted with
    | .tailCall .. | .managed (.call _ _ true) => true | _ => false) then return false
  if instruction.opcode == 65039 then
    return match instruction.operand, emitted with
      | .none, .stackAlloc flag => flag == raw.initLocals
      | _, _ => false
  if let .stackAlloc _ := emitted then return false
  if let some word := constant32 instruction <|> platformField instruction then
    return match emitted with | .ldc_i4 actual => word == actual | _ => false
  -- Any other static load is never a constant.
  if instruction.opcode == 126 && (match emitted with | .ldc_i4 _ => true | _ => false) then
    return false
  if let .call site := instruction.operand then
    if referenceContentQuery site then
      return match referenceContentConstant layouts site, emitted with
        | some expected, .ldc_i4 actual => instruction.opcode == 40 && expected == actual
        | _, _ => false
    if platformQuery site then
      return match platformConstant site, emitted with
        | some expected, .ldc_i4 actual => instruction.opcode == 40 && expected == actual
        | _, _ => false
    if let some feature := featureGetter site then
      return match emitted with
        | .feature actual => instruction.opcode == 40 && feature == actual
        | _ => false
  if instruction.opcode ∈ [6, 7, 8, 9, 17, 65036, 10, 11, 12, 13, 19, 65038] then
    let some index := localIndex instruction | return false
    return match emitted with
      | .ldloc actual => instruction.opcode ∈ [6, 7, 8, 9, 17, 65036] && actual == index
      | .stloc actual => instruction.opcode ∈ [10, 11, 12, 13, 19, 65038] && actual == index
      | _ => false
  if instruction.opcode ∈ [18, 65037] then
    return match localIndex instruction, emitted with
      | some index, .ldloca actual => index == actual
      | _, _ => false
  -- Argument homes are appended after all raw locals. Their precise mapping is
  -- independently checked by ParameterHomesValid; they cannot alias tracked locals.
  if instruction.opcode ∈ [15, 65034] then
    return match emitted with
      | .ldloca index => raw.locals.length <= index
      | _ => false
  if instruction.opcode ∈ [16, 65035] then
    return match emitted with | .stloc index => raw.locals.length <= index | _ => false
  -- A span address on the stack is already the view it names, so copying the span emits nothing.
  if instruction.opcode == 113 then
    if let .type type := instruction.operand then
      if spanLocal type then return match emitted with | .nop => true | _ => false
  return match instruction.opcode, instruction.operand, emitted with
    -- Stack duplication, bitwise operations and exact comparison signedness.
    | 37, _, .dup | 95, _, .and | 96, _, .or | 97, _, .xor | 65025, _, .ceq => true
    | 65026, _, .cgt | 65027, _, .cgt_un | 65028, _, .clt | 65029, _, .clt_un => true
    -- Branches, short and long forms, must keep their target.
    | 43, .target x, .br y | 56, .target x, .br y
    | 44, .target x, .brfalse y | 57, .target x, .brfalse y
    | 45, .target x, .brtrue y | 58, .target x, .brtrue y
    | 46, .target x, .beq y | 59, .target x, .beq y
    | 47, .target x, .bge y | 60, .target x, .bge y
    | 48, .target x, .bgt y | 61, .target x, .bgt y
    | 49, .target x, .ble y | 62, .target x, .ble y
    | 50, .target x, .blt y | 63, .target x, .blt y
    | 51, .target x, .bne_un y | 64, .target x, .bne_un y
    | 52, .target x, .bge_un y | 65, .target x, .bge_un y
    | 53, .target x, .bgt_un y | 66, .target x, .bgt_un y
    | 54, .target x, .ble_un y | 67, .target x, .ble_un y
    | 55, .target x, .blt_un y | 68, .target x, .blt_un y => x == y
    | 69, .targets x, .switch y => x == y
    | 42, _, .ret => true
    -- No other raw instruction may emit control flow, a feature test or a hole.
    | _, _, .unsupported _ | _, _, .throw _ | _, _, .feature _ | _, _, .br _ | _, _, .switch _
    | _, _, .brfalse _ | _, _, .brtrue _ => false
    | opcode, _, _ => !(opcode ∈ [37, 95, 96, 97, 42] ||
        (65025 <= opcode && opcode <= 65029) || (43 <= opcode && opcode <= 69)) &&
        fallbackFeatureEffect instruction emitted

/-- A decided typeof branch preserves its raw target or falls through without a stack effect. -/
def typeBranchMatches (instruction : RawInstruction) (taken : Bool) (emitted : Instruction) :
    Bool :=
  match instruction.operand, emitted with
  | .target target, .br actual => taken && actual == target
  | .target _, .nop => !taken
  | _, _ => false

/-- Fold operands emit nothing, a type comparison emits its decided word or branch and a folded
    `throw` raises its constructed type. Outside a decided test, type handles and
    `System.Type` calls have no admitted translation. -/
def featureOpMatchesAt (layouts : Array RawLayout) (raw : RawMethod)
    (role : Option FoldRole)
    (instruction : RawInstruction) (emitted : Instruction) : Bool :=
  match role, emitted with
  | some .head, .nop | some .interior, .nop => true
  | some (.result value), .ldc_i4 bits => bits == if value then 1 else 0
  | some (.typeBranch taken), _ => typeBranchMatches instruction taken emitted
  | some (.raise name), .throw exception => name == exception
  | some (.spanConstructor index constructor), .initializeSpanLocal actual operation =>
    index == actual && spanConstructorMatches constructor operation
  | some .tailCall, .tailCall target count => match instruction.operand with
    | .call site => site.returnType == raw.returnType &&
      featureOpMatches layouts raw instruction (.call target count)
    | _ => false
  | some .tailCall, .managed (.call signature catalog true) =>
    signature.result == callableType raw.returnType &&
      featureOpMatches layouts raw instruction
        (.managed (.call signature catalog false))
  | some .argument, _ => featureOpMatches layouts raw instruction emitted
  | some _, _ => false
  | none, _ => !typeTestInstruction instruction &&
      featureOpMatches layouts raw instruction emitted

/-- One pc of the certificate: an unreachable pc must emit a hole; a reachable one must
    be well shaped, match its emitted instruction, and flow into a weaker state at every
    recomputed successor. -/
private def checkFeatureSiteWith {Locals : Type} (layouts : Array RawLayout)
    (constants : Nat → Option W32) (raw : RawMethod)
    (facts : LocalFacts Locals)
    (profile : FeatureProfile)
    (certificate : Nat → Option (Option (FeatureFacts Locals)))
    (roles : Nat → Option (Option FoldRole)) :
    (RawInstruction × Option FoldRole) × Nat → Option (FeatureFacts Locals) → Instruction → Bool
  | _, none, .unsupported _ => true
  | ((instruction, role), pc), some state, emitted =>
    wellShaped raw facts state &&
      featureOpMatchesAt layouts raw role instruction emitted &&
      match featureTransferAtWith layouts raw facts profile (calleeConstant constants emitted)
          role instruction state,
          featureSuccessors role pc instruction state.stack with
      | some after, some successors =>
        -- Even an unselected encoded target must be a valid entry, not a fold's interior.
        let validTarget := fun target =>
          let role := roles target
          role.isSome && foldEntry role
        (match instruction.operand with
        | .target target => validTarget target
        | .targets targets => targets.all validTarget
        | _ => true) &&
        successors.all fun target =>
          match certificate target with
          | some (some incoming) => FeatureFacts.weakens facts after incoming
          | _ => false
      | _, _ => false
  | _, none, _ => false

/-- No optional sites: entry, every raw PC, the entire parameter-reachability mask,
    every successor, and all unsupported holes are covered. The entry state has no known fact.
    `constants` gives, by emitted method index, the word a parameterless call to that method
    pushes. -/
def FeatureFlowValid (layouts : Array RawLayout) (constants : Nat → Option W32)
    (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureCertificate) (reachable : List Bool) (code : List Instruction) : Prop :=
  certificate.length = raw.code.length ∧ code.length = raw.code.length ∧
  reachable = certificate.map Option.isSome ∧
  certificate[0]? = some (some { stack := [], locals := [] }) ∧
  (let facts := LocalFacts.known raw.locals.length (FeatureLocalIndex.ofRaw raw).eligible
   all3Flow (fun lookup => checkFeatureSiteWith layouts constants raw facts profile lookup
      (FlowIndex.ofList (foldRoles raw.locals raw.code)).get?)
    (.ofList certificate) 0
    (raw.code.zip (foldRoles raw.locals raw.code)).zipIdx certificate code) = true

instance (layouts : Array RawLayout) (constants : Nat → Option W32) (raw : RawMethod)
    (profile : FeatureProfile) (certificate : FeatureCertificate)
    (reachable : List Bool) (code : List Instruction) :
    Decidable (FeatureFlowValid layouts constants raw profile certificate reachable code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The specification of the feature check over full per-local lists: the entry state has no
    known fact, and every site is checked against the complete certificate and fold-role lists
    with the raw local-eligibility rule. -/
def FeatureListValid (layouts : Array RawLayout) (constants : Nat → Option W32)
    (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureListCertificate) (reachable : List Bool) (code : List Instruction) :
    Prop :=
  certificate.length = raw.code.length ∧ code.length = raw.code.length ∧
  reachable = certificate.map Option.isSome ∧
  certificate[0]? = some (some
    { stack := [], locals := List.replicate raw.locals.length none }) ∧
  all3 (checkFeatureSiteWith layouts constants raw
      (LocalFacts.list raw.locals.length (featureLocalEligible raw)) profile
      (fun target => certificate[target]?)
      (fun target => (foldRoles raw.locals raw.code)[target]?))
    (raw.code.zip (foldRoles raw.locals raw.code)).zipIdx certificate code = true

/-- Streaming validation has exactly the same entry, mask, shape and successor checks
    as indexing the complete certificate and fold-role lists at every site. -/
private theorem FeatureFlowValid_iff_indexed (layouts : Array RawLayout)
    (constants : Nat → Option W32) (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureCertificate) (reachable : List Bool) (code : List Instruction) :
    FeatureFlowValid layouts constants raw profile certificate reachable code ↔
      certificate.length = raw.code.length ∧ code.length = raw.code.length ∧
      reachable = certificate.map Option.isSome ∧
      certificate[0]? = some (some { stack := [], locals := [] }) ∧
      all3 (checkFeatureSiteWith layouts constants raw (knownLocals raw) profile
          (fun target => certificate[target]?)
          (fun target => (foldRoles raw.locals raw.code)[target]?))
        (raw.code.zip (foldRoles raw.locals raw.code)).zipIdx certificate code = true := by
  unfold FeatureFlowValid
  have eligible : (FeatureLocalIndex.ofRaw raw).eligible = featureLocalEligible raw := by
    funext index fact
    exact FeatureLocalIndex.eligible_eq raw index fact
  rw [eligible]
  rw [all3Flow_eq _ _ _ _ _ _ List.drop_zero.symm]
  have roles : (FlowIndex.ofList (foldRoles raw.locals raw.code)).get? =
      (fun target => (foldRoles raw.locals raw.code)[target]?) := by
    funext target
    exact FlowIndex.get?_ofList _ _
  rw [roles]
  rfl

#print axioms FeatureFlowValid_iff_indexed

/-- Expanding a known-fact state commutes with the transfer, which keeps its locals known. -/
private theorem featureTransferWith_expand (layouts : Array RawLayout) (raw : RawMethod)
    (count : Nat) (eligible : Nat → Option W32 → Bool) (profile : FeatureProfile)
    (instruction : RawInstruction) (state : FeatureState)
    (known : knownBelow count 0 state.locals = true) :
    featureTransferWith layouts raw (LocalFacts.list count eligible) profile instruction
        (state.expand count) =
      (featureTransferWith layouts raw (LocalFacts.known count eligible) profile instruction
        state).map (FeatureState.expand count) ∧
    ∀ after, featureTransferWith layouts raw (LocalFacts.known count eligible) profile
      instruction state = some after → knownBelow count 0 after.locals = true := by
  obtain ⟨stack, locals⟩ := state
  simp only at known
  unfold featureTransferWith
  split
  · constructor
    · rfl
    · intro after found
      cases found
      exact known
  split
  · simp only [FeatureState.expand, LocalFacts.list, LocalFacts.known, expandKnown_getElem?]
    cases localIndex instruction with
    | none => simp
    | some index => by_cases inside : index < count <;> simp [inside, known, FeatureState.expand]
  split
  · simp only [FeatureState.expand, LocalFacts.list, LocalFacts.known, expandKnown_length]
    cases localIndex instruction with
    | none => simp
    | some index =>
      cases stack with
      | nil => simp
      | cons value rest =>
        by_cases inside : index < count
        · have stored := storeKnown_spec (index := index)
            (fact := if eligible index value = true then value else none) known (Nat.zero_le _)
            inside
          simp [inside, show ¬ count ≤ index by omega, expandKnown_storeKnown known inside,
            FeatureState.expand]
          exact ⟨rfl, stored.1⟩
        · simp [inside]
  · simp only [FeatureState.expand]
    cases featureStackTransfer layouts raw profile instruction stack <;>
      simp [known, FeatureState.expand]

#print axioms featureTransferWith_expand

/-- The folded transfer commutes with expansion in the same way. -/
private theorem featureTransferAtWith_expand (layouts : Array RawLayout) (raw : RawMethod)
    (count : Nat) (eligible : Nat → Option W32 → Bool) (profile : FeatureProfile)
    (constant : Option W32) (role : Option FoldRole) (instruction : RawInstruction)
    (state : FeatureState) (known : knownBelow count 0 state.locals = true) :
    featureTransferAtWith layouts raw (LocalFacts.list count eligible) profile constant role
        instruction (state.expand count) =
      (featureTransferAtWith layouts raw (LocalFacts.known count eligible) profile constant role
        instruction state).map (FeatureState.expand count) ∧
    ∀ after, featureTransferAtWith layouts raw (LocalFacts.known count eligible) profile constant
      role instruction state = some after → knownBelow count 0 after.locals = true := by
  have base :=
    featureTransferWith_expand layouts raw count eligible profile instruction state known
  obtain ⟨stack, locals⟩ := state
  simp only at known
  unfold featureTransferAtWith
  split
  · split
    · split <;> split <;> simp_all [FeatureState.expand]
    · split <;> split <;> simp_all [FeatureState.expand]
    · simp
  · split <;> simp_all [FeatureState.expand]
  · split
    · split <;> simp_all [FeatureState.expand]
    · exact base

#print axioms featureTransferAtWith_expand

/-- Expansion keeps the stack. -/
private theorem FeatureState.expand_stack (count : Nat) (state : FeatureState) :
    (state.expand count).stack = state.stack := rfl

#print axioms FeatureState.expand_stack

/-- Weakening of known-fact states is weakening of their expansions. -/
private theorem weakens_expand {count : Nat} {eligible : Nat → Option W32 → Bool}
    {source target : FeatureState} (sourceKnown : knownBelow count 0 source.locals = true)
    (targetKnown : knownBelow count 0 target.locals = true) :
    FeatureFacts.weakens (LocalFacts.list count eligible) (source.expand count)
        (target.expand count) =
      FeatureFacts.weakens (LocalFacts.known count eligible) source target := by
  simp only [FeatureFacts.weakens, FeatureState.expand, LocalFacts.list, LocalFacts.known,
    isSublist_eq_factsWeaken sourceKnown targetKnown]

#print axioms weakens_expand

/-- A known-fact state is well shaped exactly when its list is increasing and in range and its
    expansion is well shaped. -/
private theorem wellShaped_expand {raw : RawMethod} {count : Nat}
    {eligible : Nat → Option W32 → Bool} (unknown : ∀ index, eligible index none = true)
    (state : FeatureState) :
    wellShaped raw (LocalFacts.known count eligible) state =
      (knownBelow count 0 state.locals &&
        wellShaped raw (LocalFacts.list count eligible) (state.expand count)) := by
  simp only [wellShaped, LocalFacts.known, LocalFacts.list, FeatureState.expand,
    expandKnown_length, beq_self_eq_true, Bool.true_and]
  cases known : knownBelow count 0 state.locals
  · simp
  · simp only [Bool.true_and]
    rw [expandKnown_all unknown known]
    rfl

#print axioms wellShaped_expand

/-- Unknown facts are eligible in every local. -/
private theorem featureLocalEligible_none (raw : RawMethod) (index : Nat) :
    featureLocalEligible raw index none = true := by
  simp [featureLocalEligible]

#print axioms featureLocalEligible_none

/-- Every state a certificate claims holds known facts of the method's locals. -/
private def AllKnown (raw : RawMethod) (certificate : FeatureCertificate) : Prop :=
  ∀ state, some state ∈ certificate → knownBelow raw.locals.length 0 state.locals = true

/-- The certificate of full per-local lists a known-fact certificate stands for. -/
private def expandCertificate (raw : RawMethod) (certificate : FeatureCertificate) :
    FeatureListCertificate :=
  certificate.map (Option.map (FeatureState.expand raw.locals.length))

/-- On a certificate of known-fact states, each site check agrees with the list check of the
    expanded certificate. -/
private theorem checkFeatureSiteWith_known_eq_list (layouts : Array RawLayout)
    (constants : Nat → Option W32) (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureCertificate) (roles : Nat → Option (Option FoldRole))
    (allKnown : AllKnown raw certificate)
    (site : (RawInstruction × Option FoldRole) × Nat) (state : Option FeatureState)
    (emitted : Instruction) (member : state ∈ certificate) :
    checkFeatureSiteWith layouts constants raw (knownLocals raw) profile
        (fun target => certificate[target]?) roles site state emitted =
      checkFeatureSiteWith layouts constants raw
        (LocalFacts.list raw.locals.length (featureLocalEligible raw)) profile
        (fun target => (expandCertificate raw certificate)[target]?) roles site
        (state.map (FeatureState.expand raw.locals.length)) emitted := by
  cases state with
  | none => cases emitted <;> rfl
  | some state =>
    have known := allKnown state member
    obtain ⟨⟨instruction, role⟩, pc⟩ := site
    have transfer := featureTransferAtWith_expand layouts raw raw.locals.length
      (featureLocalEligible raw) profile (calleeConstant constants emitted) role instruction state
      known
    simp only [checkFeatureSiteWith, knownLocals, Option.map_some,
      wellShaped_expand (featureLocalEligible_none raw), known, Bool.true_and, transfer.1,
      FeatureState.expand_stack]
    cases transferred : featureTransferAtWith layouts raw
        (LocalFacts.known raw.locals.length (featureLocalEligible raw)) profile
        (calleeConstant constants emitted) role instruction state with
    | none => rfl
    | some after =>
      have afterKnown := transfer.2 after transferred
      cases featureSuccessors role pc instruction state.stack with
      | none => rfl
      | some successors =>
        simp only [Option.map_some]
        congr 2
        apply List.all_congr rfl
        intro target
        simp only [expandCertificate, List.getElem?_map]
        cases found : certificate[target]? with
        | none => rfl
        | some incoming =>
          cases incoming with
          | none => rfl
          | some incoming =>
            exact (weakens_expand afterKnown
              (allKnown incoming (List.mem_of_getElem? found))).symm

#print axioms checkFeatureSiteWith_known_eq_list

@[simp] private theorem expandKnown_nil (count : Nat) :
    expandKnown count [] = List.replicate count none := by
  apply List.ext_getElem?
  intro index
  simp [expandKnown_getElem?, List.getElem?_replicate]

#print axioms expandKnown_nil

/-- The check accepts a certificate exactly when its states hold known facts and its expansion
    satisfies the list specification. -/
private theorem FeatureFlowValid_iff_expand (layouts : Array RawLayout)
    (constants : Nat → Option W32) (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureCertificate) (reachable : List Bool) (code : List Instruction) :
    FeatureFlowValid layouts constants raw profile certificate reachable code ↔
      AllKnown raw certificate ∧ FeatureListValid layouts constants raw profile
        (expandCertificate raw certificate) reachable code := by
  rw [FeatureFlowValid_iff_indexed]
  unfold FeatureListValid
  have sitesEqual (allKnown : AllKnown raw certificate) := all3_map
    (Option.map (FeatureState.expand raw.locals.length))
    (raw.code.zip (foldRoles raw.locals raw.code)).zipIdx certificate code
    fun site state emitted member => checkFeatureSiteWith_known_eq_list layouts constants raw
      profile certificate (fun target => (foldRoles raw.locals raw.code)[target]?) allKnown site
      state emitted member
  constructor
  · rintro ⟨length, codeLength, mask, entry, sites⟩
    have allKnown : AllKnown raw certificate := by
      intro state member
      obtain ⟨⟨⟨instruction, role⟩, pc⟩, emitted, checked⟩ := all3_mem sites member
      simp only [checkFeatureSiteWith, knownLocals, Bool.and_eq_true,
        wellShaped_expand (featureLocalEligible_none raw)] at checked
      exact checked.1.1.1
    refine ⟨allKnown, by simp [expandCertificate, length], codeLength, ?_, ?_, ?_⟩
    · simp [expandCertificate, mask, Function.comp_def]
    · simp [expandCertificate, entry, FeatureState.expand]
    · rw [sitesEqual allKnown] at sites
      exact sites
  · rintro ⟨allKnown, length, codeLength, mask, entry, sites⟩
    refine ⟨by simpa [expandCertificate] using length, codeLength, ?_, ?_, ?_⟩
    · simpa [expandCertificate, Function.comp_def] using mask
    · simp only [expandCertificate, List.getElem?_map] at entry
      cases found : certificate[0]? with
      | none => simp [found] at entry
      | some first =>
        cases first with
        | none => simp [found] at entry
        | some state =>
          simp only [found, Option.map_some, Option.some.injEq, FeatureState.expand,
            FeatureFacts.mk.injEq] at entry
          have empty : state.locals = [] := expandKnown_inj
            (allKnown state (List.mem_of_getElem? found)) rfl (by rw [entry.2, expandKnown_nil])
          obtain ⟨stack, locals⟩ := state
          simp only at entry empty
          rw [entry.1, empty]
    · rw [sitesEqual allKnown]
      exact sites

#print axioms FeatureFlowValid_iff_expand

/-- A certificate the check accepts expands to one the list specification accepts. -/
theorem FeatureFlowValid.expand {layouts : Array RawLayout} {constants : Nat → Option W32}
    {raw : RawMethod} {profile : FeatureProfile} {certificate : FeatureCertificate}
    {reachable : List Bool} {code : List Instruction}
    (valid : FeatureFlowValid layouts constants raw profile certificate reachable code) :
    FeatureListValid layouts constants raw profile
      (certificate.map (Option.map (FeatureState.expand raw.locals.length))) reachable code :=
  ((FeatureFlowValid_iff_expand layouts constants raw profile certificate reachable code).mp
    valid).2

#print axioms FeatureFlowValid.expand

/-- The known facts of a specification state. -/
private def FeatureListState.compress (state : FeatureListState) : FeatureState :=
  { stack := state.stack, locals := compressKnown 0 state.locals }

/-- Every state a certificate the list specification accepts holds one fact per local. -/
private theorem FeatureListValid.lengths {layouts : Array RawLayout}
    {constants : Nat → Option W32} {raw : RawMethod} {profile : FeatureProfile}
    {certificate : FeatureListCertificate} {reachable : List Bool} {code : List Instruction}
    (valid : FeatureListValid layouts constants raw profile certificate reachable code)
    {state : FeatureListState} (member : some state ∈ certificate) :
    state.locals.length = raw.locals.length := by
  obtain ⟨⟨⟨instruction, role⟩, pc⟩, emitted, checked⟩ := all3_mem valid.2.2.2.2 member
  simp only [checkFeatureSiteWith, wellShaped, LocalFacts.list, Bool.and_eq_true,
    beq_iff_eq] at checked
  exact checked.1.1.1.1

#print axioms FeatureListValid.lengths

/-- Known-fact certificates with the same expansion are equal. -/
private theorem expandCertificate_inj {raw : RawMethod} :
    ∀ {first second : FeatureCertificate}, AllKnown raw first → AllKnown raw second →
      expandCertificate raw first = expandCertificate raw second → first = second
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, expanded | _ :: _, [], _, _, expanded => by
    simp [expandCertificate] at expanded
  | head :: rest, other :: others, firstKnown, secondKnown, expanded => by
    simp only [expandCertificate, List.map_cons, List.cons.injEq] at expanded
    have tail := expandCertificate_inj (raw := raw) (first := rest) (second := others)
      (fun state member => firstKnown state (List.mem_cons_of_mem _ member))
      (fun state member => secondKnown state (List.mem_cons_of_mem _ member)) expanded.2
    rw [tail]
    congr 1
    cases head with
    | none => cases other <;> simp_all
    | some state =>
      cases other with
      | none => simp at expanded
      | some next =>
        simp only [Option.map_some, Option.some.injEq, FeatureState.expand,
          FeatureFacts.mk.injEq] at expanded
        have locals := expandKnown_inj (firstKnown state (List.mem_cons_self ..))
          (secondKnown next (List.mem_cons_self ..)) expanded.1.2
        obtain ⟨firstStack, _⟩ := state
        obtain ⟨secondStack, _⟩ := next
        simp only at locals expanded
        rw [expanded.1.1, locals]

#print axioms expandCertificate_inj

/-- Every certificate the list specification accepts is the expansion of exactly one certificate
    the check accepts. -/
theorem FeatureListValid.known {layouts : Array RawLayout} {constants : Nat → Option W32}
    {raw : RawMethod} {profile : FeatureProfile} {certificate : FeatureListCertificate}
    {reachable : List Bool} {code : List Instruction}
    (valid : FeatureListValid layouts constants raw profile certificate reachable code) :
    ∃ known : FeatureCertificate,
      (FeatureFlowValid layouts constants raw profile known reachable code ∧
        known.map (Option.map (FeatureState.expand raw.locals.length)) = certificate) ∧
      ∀ other : FeatureCertificate,
        FeatureFlowValid layouts constants raw profile other reachable code →
        other.map (Option.map (FeatureState.expand raw.locals.length)) = certificate →
        other = known := by
  let known := certificate.map (Option.map FeatureListState.compress)
  have expanded : expandCertificate raw known = certificate := by
    simp only [expandCertificate, known, List.map_map]
    conv => rhs; rw [← List.map_id certificate]
    apply List.map_congr_left
    intro entry member
    cases entry with
    | none => rfl
    | some state =>
      have length := valid.lengths member
      simp only [Function.comp_apply, Option.map_some, id, FeatureState.expand,
        FeatureListState.compress]
      rw [← length, expandKnown_compressKnown]
  have allKnown : AllKnown raw known := by
    intro state member
    simp only [known, List.mem_map] at member
    obtain ⟨entry, inside, compressed⟩ := member
    cases entry with
    | none => simp at compressed
    | some listed =>
      simp only [Option.map_some, Option.some.injEq] at compressed
      subst compressed
      have length := valid.lengths inside
      simp only [FeatureListState.compress]
      rw [← length]
      exact compressKnown_known listed.locals
  have accepted : FeatureFlowValid layouts constants raw profile known reachable code :=
    (FeatureFlowValid_iff_expand layouts constants raw profile known reachable code).mpr
      ⟨allKnown, expanded ▸ valid⟩
  refine ⟨known, ⟨accepted, expanded⟩, fun other otherValid otherExpanded => ?_⟩
  have otherKnown :=
    ((FeatureFlowValid_iff_expand layouts constants raw profile other reachable code).mp
      otherValid).1
  exact expandCertificate_inj otherKnown allKnown (otherExpanded.trans expanded.symm)

#print axioms FeatureListValid.known

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

/-- Pointwise `FactRepresents` over lists of equal length. -/
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

/-- Abstract execution edges are computed from raw instructions, incoming facts and the
    emitted call targets, rather than copied from the extractor's claimed reachable mask. -/
def FeatureEdge (layouts : Array RawLayout) (constants : Nat → Option W32) (raw : RawMethod)
    (profile : FeatureProfile) (certificate : FeatureCertificate) (code : List Instruction)
    (pc target : Nat) : Prop :=
  ∃ instruction role state emitted after successors,
    (raw.code.zip (foldRoles raw.locals raw.code))[pc]? = some (instruction, role) ∧
    certificate[pc]? = some (some state) ∧ code[pc]? = some emitted ∧
    featureTransferAt layouts raw profile (calleeConstant constants emitted) role instruction
      state = some after ∧
    featureSuccessors role pc instruction state.stack = some successors ∧ target ∈ successors

/-- Validation establishes closure under every independently recomputed edge,
    including backedges and every possible switch destination. -/
theorem FeatureFlowValid.edge_closed {layouts : Array RawLayout}
    {constants : Nat → Option W32} {raw : RawMethod} {profile : FeatureProfile}
    {certificate : FeatureCertificate} {reachable : List Bool} {code : List Instruction}
    (valid : FeatureFlowValid layouts constants raw profile certificate reachable code)
    {pc target : Nat}
    (edge : FeatureEdge layouts constants raw profile certificate code pc target) :
    ∃ incoming, certificate[target]? = some (some incoming) := by
  obtain ⟨instruction, role, state, emitted, after, successors, rawAt, stateAt, codeAt,
    transferred, successorsAt, member⟩ := edge
  have indexed : (raw.code.zip (foldRoles raw.locals raw.code)).zipIdx[pc]? =
      some ((instruction, role), pc) := by
    simp [List.getElem?_zipIdx, rawAt]
  have sites := valid.2.2.2.2
  have eligible : (FeatureLocalIndex.ofRaw raw).eligible = featureLocalEligible raw := by
    funext index fact
    exact FeatureLocalIndex.eligible_eq raw index fact
  change all3Flow _ _ _ _ _ _ = true at sites
  rw [eligible] at sites
  rw [all3Flow_eq _ _ _ _ _ _ List.drop_zero.symm] at sites
  have checked := all3_at sites indexed stateAt codeAt
  unfold featureTransferAt knownLocals at transferred
  simp only [checkFeatureSiteWith,
    transferred, successorsAt, Bool.and_eq_true] at checked
  have successor := List.all_eq_true.mp checked.2.2 target member
  cases hnext : certificate[target]? with
  | none => simp [hnext] at successor
  | some next => cases next with
    | none => simp [hnext] at successor
    | some incoming => exact ⟨incoming, rfl⟩

/-- The pcs reachable from entry along recomputed feature edges. -/
inductive FeaturePath (layouts : Array RawLayout) (constants : Nat → Option W32)
    (raw : RawMethod) (profile : FeatureProfile) (certificate : FeatureCertificate)
    (code : List Instruction) : Nat → Prop where
  | entry : FeaturePath layouts constants raw profile certificate code 0
  | next {pc target} : FeaturePath layouts constants raw profile certificate code pc →
      FeatureEdge layouts constants raw profile certificate code pc target →
        FeaturePath layouts constants raw profile certificate code target

/-- Arbitrarily many steps through the validated graph remain in the emitted
    reachable mask; this includes cyclic paths without a bound on iterations. -/
theorem FeatureFlowValid.path_reachable {layouts : Array RawLayout}
    {constants : Nat → Option W32} {raw : RawMethod} {profile : FeatureProfile}
    {certificate : FeatureCertificate} {reachable : List Bool} {code : List Instruction}
    (valid : FeatureFlowValid layouts constants raw profile certificate reachable code)
    {pc : Nat} (path : FeaturePath layouts constants raw profile certificate code pc) :
    reachable[pc]? = some true := by
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
