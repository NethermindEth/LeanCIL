import CIL.Extraction.Generics
import CIL.Extraction.Constrained
import CIL.Extraction.FeatureEffects
import CIL.Extraction.Folds
import CIL.Extraction.FlowIndex
import CIL.Extraction.FeatureLocals
import CIL.Extraction.IndirectAccess
import CIL.Semantics
import CIL.Extraction.RuntimeModels
import CIL.Extraction.ExceptionRegions

/-!
# Feature flow

Hardware feature tests such as `Avx2.IsSupported` are constants under a fixed profile, and
the extractor prunes the branches they decide. `FeatureFlowValid` checks that pruning: an
abstract interpretation tracks known 32-bit words on the stack and in eligible locals, its
transfer function and successor edges are recomputed here from the raw body, and the
extractor's per-pc certificate must be closed under them. Only pcs the certificate reaches
may be live; every other emitted instruction must be a hole (`.unadmitted`).

The same pass binds each raw instruction to its emitted counterpart, exactly for control
flow, locals and feature tests, and by stack effect for everything else. A fold site whose role
fixes the decoded instruction (`fixedRoleSite`) skips that comparison, which
`FeatureFlowValid.instruction_checked` recovers from the decoded code equation.

A parameterless static Boolean call pushes the word `constantReturn` reads from the callee's own
certificate, which the whole-program obligation validates alongside the caller's. Known words
only decide which pcs are live, and every pc they rule out is emitted as a hole, whose step
faults. A wrong claim, cyclic or not, therefore sends execution into a hole that faults:
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

/-- The bound getter model supplies the same fact to reachability and execution. -/
def platformGetterModel (site : CallSite) : Option RuntimeModel := do
  let name := site.method.name
  guard (name == name!"get_IsSupported" || name == name!"get_IsHardwareAccelerated" ||
    name == name!"get_Size" || name == name!"get_Is64BitProcess")
  let entry ← runtimeModels.entry? .call site.method
  let row ← entry.select? site.method
  guard (row.operand.bindsSite site)
  row.resolve (LayoutEnvironment.callLayouts {}) site.method

/-- `ldsfld` of the System.Runtime `BitConverter` static Boolean `IsLittleEndian`. Valid
    profiles are little-endian, so the load is the constant 1. -/
def platformField (instruction : RawInstruction) : Option W32 :=
  if instruction.opcode == 126 && instruction.operand == .field littleEndianField.owner
      littleEndianField.index littleEndianField.type littleEndianField.name true
  then some 1 else none

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
      closed.returnType != .primitive .boolean then none else
  match (closed.code.zip certificate).filterMap returned with
  | some word :: rest =>
    if (word == 0 || word == 1) && rest.all (· == some word) then some word else none
  | _ => none
where
  /-- The fact a reachable `ret` returns; every other pc contributes nothing. -/
  returned : RawInstruction × Option FeatureState → Option (Option W32)
    | (⟨_, 42, _⟩, some state) => some state.stack.head?.join
    | _ => none

/-- The word an emitted parameterless call, not a tail call, pushes when `constants` knows the
    return of the callee that `link`, the link of its pc, names. `constants` reads each callee's
    own certificate, which its own obligation validates. -/
def calleeConstant (constants : Nat → Option W32) (link : Option Link) :
    Instruction → Option W32
  | .call method prefixes => match link with
    | some (.direct index) =>
      if method.argumentCount = 0 && !prefixes.tail then constants index else none
    | _ => none
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
    if let some constant := referenceContentFact layouts site then
      if instruction.opcode != 40 then none else
        return some constant :: next
    if let some model := platformGetterModel site then
      guard (instruction.opcode == 40)
      match model with
      | .feature feature => return some (if profile.evaluate feature then 1 else 0) :: next
      | .constant word => return some word :: next
      | _ => return none :: next
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
    -- `leave` empties the stack; `endfinally` has no successor in the method's flow.
    | ⟨_, 221, .target _⟩ | ⟨_, 222, .target _⟩ => some { state with stack := [] }
    | ⟨_, 220, .none⟩ => some state
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
  -- `br` and `leave`, then `switch`.
  else if instruction.opcode == 43 || instruction.opcode == 56 ||
      leaveOpcode instruction.opcode then
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
    | .callvirt .. => instruction.opcode == 111
    | .newobj _ => instruction.opcode == 115
    | .castclass _ | .isinst _ =>
      (typeTestSource emitted).any fun (opcode, _) => opcode == instruction.opcode
    | _ => true
  properCall && match rawFeatureEffect instruction, emittedFeatureEffect emitted returnsValue with
    | some rawEffect, some emittedEffect => rawEffect == emittedEffect
    | _, _ => false

/-- Bind every control-flow operation and every operation that propagates a known
    feature fact to the actual emitted instruction. Unknown operations may not
    emit a hole on a reachable path. -/
def featureOpMatches (layouts : Array RawLayout) (raw : RawMethod)
    (instruction : RawInstruction) (emitted : Instruction) : Bool :=
    Id.run do
  -- These terminal/transfer encodings have no admitted emitted counterpart.
  if instruction.opcode ∈ [39, 65041, 65044, 65050] then return false
  if (match emitted with
    | .call _ prefixes => prefixes.tail | .calli _ true => true | _ => false) then
    return false
  if instruction.opcode == 65039 then
    return match instruction.operand, emitted with
      | .none, .localloc => true
      | _, _ => false
  if let .localloc := emitted then return false
  if let some word := constant32 instruction <|> platformField instruction then
    return match emitted with | .ldc_i4 actual => word == actual | _ => false
  -- Any other static load is never a constant.
  if instruction.opcode == 126 && (match emitted with | .ldc_i4 _ => true | _ => false) then
    return false
  if let .call site := instruction.operand then
    if (referenceContentFact layouts site).isSome || (platformGetterModel site).isSome then
      return match emitted with
        | .call method prefixes => instruction.opcode == 40 && method == site.method &&
            !prefixes.tail && prefixes.constrained.isNone
        | _ => false
    if emitted matches .ldc_i4 _ then return false
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
  -- An argument's address and store name the argument itself; ParameterHomesValid checks that
  -- it has a home, so neither can alias a tracked local.
  if instruction.opcode ∈ [15, 65034] then
    return match argumentOperation instruction, emitted with
      | some (.address index), .ldarga actual => index == actual
      | _, _ => false
  if instruction.opcode ∈ [16, 65035] then
    return match argumentOperation instruction, emitted with
      | some (.store index), .starg actual => index == actual
      | _, _ => false
  -- A span load forwards its view and retains the raw span operand.
  if instruction.opcode == 0x71 then
    if let .type type := instruction.operand then
      if spanLocal type then
        return match emitted with | .ldobj operand => operand == type | _ => false
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
    -- `leave` keeps its target; `endfinally` has no operand.
    | 221, .target x, .leave y | 222, .target x, .leave y => x == y
    | 220, .none, .endfinally => true
    | 42, _, .ret => true
    | 20, .none, .ldnull | 122, .none, .throw none => true
    -- No other raw instruction may emit control flow, a feature test or a hole.
    | _, _, .ldnull | _, _, .unadmitted _ | _, _, .throw _ | _, _, .br _ | _, _, .switch _
    | _, _, .brfalse _ | _, _, .brtrue _ | _, _, .leave _ | _, _, .endfinally => false
    | opcode, _, _ => !(opcode ∈ [20, 37, 42, 95, 96, 97, 122, 220, 221, 222] ||
        (65025 <= opcode && opcode <= 65029) || (43 <= opcode && opcode <= 69)) &&
        fallbackFeatureEffect instruction emitted

/-- A closed type comparison retains its decoded loads, calls and comparison. A null operand in a
    folded exception sequence pushes its object reference, and the throw raises the constructed type. -/
def featureOpMatchesAt (layouts : Array RawLayout) (raw : RawMethod)
    (role : Option FoldRole)
    (instruction : RawInstruction) (emitted : Instruction)
    (previous : Option RawInstruction := none) : Bool :=
  match role, emitted with
  | some .head, .nop | some .interior, .nop => instruction.opcode != 20
  | some .head, .ldnull | some .interior, .ldnull =>
    instruction.opcode == 20 && instruction.operand == .none
  | some .typeHead, _ | some .typeOperand, _ | some (.result _), _ | some (.typeBranch _), _ =>
    valueEncodingMatches previous instruction emitted
  | some (.raise raised), .throw folded => some raised == folded
  | some .tailCall, .call method prefixes => match instruction.operand with
    | .call site => prefixes.tail && site.returnType == raw.returnType &&
      featureOpMatches layouts raw instruction (.call method { prefixes with tail := false })
    | _ => false
  | some .tailCall, .calli signature true =>
    signature.result == callableType raw.returnType &&
      featureOpMatches layouts raw instruction
        (.calli signature false)
  | some .argument, _ => valueEncodingMatches previous instruction emitted &&
      featureOpMatches layouts raw instruction emitted
  | some _, _ => false
  | none, _ => !typeTestInstruction instruction &&
      featureOpMatches layouts raw instruction emitted

/-- A fixed fold role accepts exactly its decoded instruction, including the branch target
    and the exception kind. -/
theorem fixedRole_matches (layouts : Array RawLayout) (method : RawMethod)
    (role : FoldRole) (previous : Option RawInstruction) (raw : RawInstruction)
    (emitted : Instruction)
    (fixed : match role with
      | .head | .interior | .typeHead | .typeOperand | .result _ | .typeBranch _ | .raise _ => True | _ => False) :
    featureOpMatchesAt layouts method (some role) raw emitted previous = true ↔
      Instruction.ofRole? role previous raw = some emitted := by
  cases role with
  | typeHead | typeOperand | result | typeBranch =>
    exact valueEncodingMatches_iff
  | argument | tailCall | blocked => exact fixed.elim
  | head | interior =>
    by_cases null : raw.opcode = 20 <;> by_cases valid : raw.operand = .none <;>
      cases emitted <;> simp [featureOpMatchesAt, Instruction.ofRole?, null, valid]
  | raise =>
    cases emitted <;> first | exact Iff.rfl | simp [featureOpMatchesAt, Instruction.ofRole?]

#print axioms fixedRole_matches

/-- A live fold site whose role fixes its instruction and whose operand the method's bindings
    do not decode, holding no hole: the decoder emits the role's instruction there. -/
def fixedRoleSite (instruction : RawInstruction) (role : Option FoldRole)
    (emitted : Instruction) : Bool :=
  (match role with
    | some .head | some .interior | some .typeHead | some .typeOperand | some (.result _)
    | some (.typeBranch _) | some (.raise _) => true
    | _ => false) &&
    !(boundSite instruction && !foldOwnsSite role) && !(emitted matches .unadmitted _)

/-- An accepted fold argument has the value and index of its encoded push or return. -/
theorem argument_of_featureOpMatchesAt {layouts : Array RawLayout} {method : RawMethod}
    {raw : RawInstruction} {emitted : Instruction} {previous : Option RawInstruction}
    (checked : featureOpMatchesAt layouts method (some .argument) raw emitted previous = true) :
    Instruction.ofRole? .argument previous raw = some emitted := by
  exact valueEncodingMatches_sound (Bool.and_eq_true_iff.mp checked).1

#print axioms argument_of_featureOpMatchesAt

/-- A live managed tail call has the method named by its raw operand, exactly the tail prefix,
    and a linked callee with that operand's token and type arguments. -/
theorem ManagedCallsValid.tailCall_target {types : List DispatchType}
    {methods : List SpecializedMethod} {imports : List ImportSlot}
    {modelled : CallOpcode × MethodRef → Bool}
    {raw : RawMethod} {reachable : List Bool} {body : Method} {layouts : Array RawLayout}
    (calls : ManagedCallsValid methods imports modelled (lowerConstrainedRaw types raw)
      reachable body)
    (constrained : ConstrainedCallsValid types methods raw reachable body)
    {pc target token prefixOffset callOffset : Nat} {site : CallSite} {op : Instruction}
    (rawAt : raw.code[pc]? = some ⟨callOffset, 40, .call site⟩)
    (tailAt : rawBefore (raw.code[·]?) pc = some ⟨prefixOffset, 0xFE14, .none⟩)
    (found : body.code[pc]? = some op) (live : reachable[pc]? = some true)
    (feature : featureOpMatchesAt layouts raw (some .tailCall) ⟨callOffset, 40, .call site⟩
      op (rawBefore (raw.code[·]?) pc) = true)
    (managed : site.target = .managed token) (linked : body.linkAt pc = some (.direct target)) :
    Instruction.ofRole? .tailCall (rawBefore (raw.code[·]?) pc) ⟨callOffset, 40, .call site⟩ =
      some op ∧ ∃ callee, methods[target]? = some callee ∧ callee.closed.token = token ∧
        callee.arguments = site.typeArguments := by
  have previous : raw.code[pc - 1]? = some ⟨prefixOffset, 0xFE14, .none⟩ := by
    unfold rawBefore at tailAt
    split at tailAt <;> simp_all
  have lowered : (lowerConstrainedRaw types raw).code[pc]? = some ⟨callOffset, 40, .call site⟩ := by
    rw [lowerConstrainedRaw_eq_original]
    split
    · exact rawAt
    · simp [List.getElem?_map, List.getElem?_zipIdx, rawAt, previous]
  have shape : ∃ method prefixes, op = .call method prefixes ∧ prefixes.tail = true := by
    cases op <;> first | contradiction | skip
    case call method prefixes =>
      exact ⟨_, _, rfl, (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp feature).1).1⟩
    case calli =>
      have fits := calls.linkFits found rfl
      rw [linked] at fits
      contradiction
  obtain ⟨method, prefixes, rfl, tail⟩ := shape
  have window := List.all_eq_true.mp
    ((ConstrainedCallsValid_iff_original _ _ _ _ _).mp constrained).2.2 pc
    (List.mem_range.mpr (List.getElem?_eq_some_iff.mp rawAt).1)
  have noReceiver : prefixes.constrained = none := by
    simpa [constrainedSiteValid, constrainedSiteCheck, constrainedSiteCheckWith,
      constrainedSiteWindow, live, rawAt, previous, found, typeTestSource] using window
  obtain ⟨operand, callee⟩ := calls.direct_operand found live lowered rfl managed linked
  have name : method = site.method := by simpa [callOperandMatches, noReceiver] using operand
  refine ⟨?_, callee⟩
  rw [tailAt, name]
  obtain ⟨flag, receiver⟩ := prefixes
  change flag = true at tail
  change receiver = none at noReceiver
  subst flag receiver
  rfl

#print axioms ManagedCallsValid.tailCall_target

/-- The feature check reads a raw instruction together with its predecessor and closed role. -/
private structure FeatureSite where
  pc : Nat
  previous : Option RawInstruction
  instruction : RawInstruction
  role : Option FoldRole

/-- Pair each raw site with the modifier immediately before it, including across dead sites. -/
private def featureSites (pc : Nat) (previous : Option RawInstruction) :
    List RawInstruction → List (Option FoldRole) → List FeatureSite
  | instruction :: code, role :: roles =>
    ⟨pc, previous, instruction, role⟩ :: featureSites (pc + 1) (some instruction) code roles
  | _, _ => []

/-- The streamed site at a pc has exactly the raw predecessor specified by that pc. -/
private theorem featureSites_at {code : List RawInstruction} {roles : List (Option FoldRole)}
    {pc : Nat} {instruction : RawInstruction} {role : Option FoldRole}
    (rawAt : code[pc]? = some instruction) (roleAt : roles[pc]? = some role) :
    (featureSites 0 none code roles)[pc]? =
      some ⟨pc, rawBefore (code[·]?) pc, instruction, role⟩ := by
  have walk (start : Nat) (previous : Option RawInstruction) :
      (featureSites start previous code roles)[pc]? =
        some ⟨start + pc, (if pc == 0 then previous else code[pc - 1]?), instruction, role⟩ := by
    induction pc generalizing start previous code roles with
    | zero =>
      cases code <;> cases roles <;> simp_all [featureSites]
    | succ index ih =>
      cases code with
      | nil => simp at rawAt
      | cons head tail =>
        cases roles with
        | nil => simp at roleAt
        | cons first rest =>
          have checked := ih (by simpa using rawAt) (by simpa using roleAt)
            (start + 1) (some head)
          cases index <;> simpa [featureSites, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using checked
  simpa [rawBefore] using walk 0 none

#print axioms featureSites_at

/-- The stack facts a handler starts with: the caught object for a catch, nothing for a
    finally. -/
def _root_.CIL.ExceptionClause.entryFacts (clause : ExceptionClause) : List (Option W32) :=
  match clause.kind with
  | .catch _ => [none]
  | .finally => []

/-- Some exception clause of `raw` has its handler start at `pc`. -/
def handlerStartsAt (raw : RawMethod) (pc : Nat) : Bool :=
  raw.handlers.any (·.handlerStart == pc)

/-- A reachable `stack` at `pc` fits the exception clauses of `raw`: a handler starting there
    is a fold entry entered with its entry facts, a protected range starting there has an empty
    stack, and a folded `throw`, which raises no object for a catch to test, lies in no protected
    range. `featureLocalEligible` keeps every local of a method with clauses unknown. -/
def clauseSiteFits (raw : RawMethod) (pc : Nat) (role : Option FoldRole)
    (stack : List (Option W32)) : Bool :=
  raw.handlers.all fun clause =>
    (clause.handlerStart != pc || foldEntry (some role) && stack == clause.entryFacts) &&
      (clause.tryStart != pc || stack.isEmpty) &&
      (!clause.protects pc || !(role matches some (.raise _)))

/-- One pc of the certificate: an unreachable pc must emit a hole and start no handler; a
    reachable one must be well shaped, fit the exception clauses (`clauseSiteFits`), match its
    emitted instruction unless its fold role fixes the instruction the decoder emits
    (`fixedRoleSite`), and flow into a weaker state at every recomputed successor. -/
private def checkFeatureSiteWith {Locals : Type} (layouts : Array RawLayout)
    (constants : Nat → Option W32) (linkAt : Nat → Option Link) (raw : RawMethod)
    (facts : LocalFacts Locals)
    (profile : FeatureProfile)
    (certificate : Nat → Option (Option (FeatureFacts Locals)))
    (roles : Nat → Option (Option FoldRole)) :
    FeatureSite → Option (FeatureFacts Locals) → Instruction → Bool
  | site, none, .unadmitted _ => !handlerStartsAt raw site.pc
  | ⟨pc, previous, instruction, role⟩, some state, emitted =>
    wellShaped raw facts state && clauseSiteFits raw pc role state.stack &&
      (fixedRoleSite instruction role emitted ||
        featureOpMatchesAt layouts raw role instruction emitted previous) &&
      match featureTransferAtWith layouts raw facts profile
          (calleeConstant constants (linkAt pc) emitted)
          role instruction state,
          featureSuccessors role pc instruction state.stack with
      | some after, some successors =>
        -- Even an unselected encoded target must be a valid entry, not a fold's interior.
        let validTarget := fun target => foldEntry (roles target)
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
    every successor, and all holes are covered. The entry state has no known fact.
    `constants` gives, by emitted method index, the word a parameterless call to that method
    pushes. -/
def FeatureFlowValid (layouts : Array RawLayout) (constants : Nat → Option W32)
    (linkAt : Nat → Option Link) (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureCertificate) (reachable : List Bool) (code : List Instruction) : Prop :=
  certificate.length = raw.code.length ∧ code.length = raw.code.length ∧
  reachable = certificate.map Option.isSome ∧
  certificate[0]? = some (some { stack := [], locals := [] }) ∧
  (let facts := LocalFacts.known raw.locals.length (FeatureLocalIndex.ofRaw raw).eligible
   all3Flow (fun lookup => checkFeatureSiteWith layouts constants linkAt raw facts profile lookup
      (FlowIndex.ofList (foldRoles raw.code)).get?)
    (.ofList certificate) 0
    (featureSites 0 none raw.code (foldRoles raw.code)) certificate code) = true

instance (layouts : Array RawLayout) (constants : Nat → Option W32)
    (linkAt : Nat → Option Link) (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureCertificate) (reachable : List Bool) (code : List Instruction) :
    Decidable (FeatureFlowValid layouts constants linkAt raw profile certificate reachable code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The specification of the feature check over full per-local lists: the entry state has no
    known fact, and every site is checked against the complete certificate and fold-role lists
    with the raw local-eligibility rule. -/
def FeatureListValid (layouts : Array RawLayout) (constants : Nat → Option W32)
    (linkAt : Nat → Option Link) (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureListCertificate) (reachable : List Bool) (code : List Instruction) :
    Prop :=
  certificate.length = raw.code.length ∧ code.length = raw.code.length ∧
  reachable = certificate.map Option.isSome ∧
  certificate[0]? = some (some
    { stack := [], locals := List.replicate raw.locals.length none }) ∧
  all3 (checkFeatureSiteWith layouts constants linkAt raw
      (LocalFacts.list raw.locals.length (featureLocalEligible raw)) profile
      (fun target => certificate[target]?)
      (fun target => (foldRoles raw.code)[target]?))
    (featureSites 0 none raw.code (foldRoles raw.code)) certificate code = true

/-- Streaming validation has exactly the same entry, mask, shape and successor checks
    as indexing the complete certificate and fold-role lists at every site. -/
private theorem FeatureFlowValid_iff_indexed (layouts : Array RawLayout)
    (constants : Nat → Option W32) (linkAt : Nat → Option Link) (raw : RawMethod)
    (profile : FeatureProfile)
    (certificate : FeatureCertificate) (reachable : List Bool) (code : List Instruction) :
    FeatureFlowValid layouts constants linkAt raw profile certificate reachable code ↔
      certificate.length = raw.code.length ∧ code.length = raw.code.length ∧
      reachable = certificate.map Option.isSome ∧
      certificate[0]? = some (some { stack := [], locals := [] }) ∧
      all3 (checkFeatureSiteWith layouts constants linkAt raw (knownLocals raw) profile
          (fun target => certificate[target]?)
          (fun target => (foldRoles raw.code)[target]?))
        (featureSites 0 none raw.code (foldRoles raw.code)) certificate code = true := by
  unfold FeatureFlowValid
  have eligible : (FeatureLocalIndex.ofRaw raw).eligible = featureLocalEligible raw := by
    funext index fact
    exact FeatureLocalIndex.eligible_eq raw index fact
  rw [eligible]
  rw [all3Flow_eq _ _ _ _ _ _ List.drop_zero.symm]
  have roles : (FlowIndex.ofList (foldRoles raw.code)).get? =
      (fun target => (foldRoles raw.code)[target]?) := by
    funext target
    exact FlowIndex.get?_ofList _ _
  rw [roles]
  rfl

#print axioms FeatureFlowValid_iff_indexed

/-- At a live instruction of code decoded from the raw body, the emitted instruction matches its
    role after the actual predecessor. -/
theorem FeatureFlowValid.instruction_checked {layouts : Array RawLayout} {raw : RawMethod}
    {constants : Nat → Option W32} {linkAt : Nat → Option Link} {profile : FeatureProfile}
    {certificate : FeatureCertificate} {reachable : List Bool} {code : List Instruction}
    (valid : FeatureFlowValid layouts constants linkAt raw profile certificate reachable code)
    {live : Nat → Bool} {decodeSite : SiteDecoder}
    (codeDecodes : code = Instruction.ofRawCode none raw.code
      (Instruction.withSiteDecoder (foldRoles raw.code).toArray live decodeSite))
    {pc : Nat} {instruction : RawInstruction} {role : Option FoldRole}
    {state : FeatureState} {emitted : Instruction}
    (rawAt : raw.code[pc]? = some instruction)
    (roleAt : (foldRoles raw.code)[pc]? = some role)
    (stateAt : certificate[pc]? = some (some state)) (codeAt : code[pc]? = some emitted) :
    featureOpMatchesAt layouts raw role instruction emitted
      (rawBefore (raw.code[·]?) pc) = true := by
  have pairAt := featureSites_at rawAt roleAt
  have sites := ((FeatureFlowValid_iff_indexed _ _ _ _ _ _ _ _).mp valid).2.2.2.2
  have checked := all3_at sites pairAt stateAt codeAt
  simp only [checkFeatureSiteWith, Bool.and_eq_true, Bool.or_eq_true] at checked
  rcases checked.1.2 with fixed | matched
  · simp only [fixedRoleSite, Bool.and_eq_true, Bool.not_eq_true'] at fixed
    obtain ⟨⟨isFixed, direct⟩, present⟩ := fixed
    have notHole : ∀ opcode, emitted ≠ .unadmitted opcode := by
      intro opcode hole
      subst hole
      simp at present
    rw [codeDecodes] at codeAt
    cases role with
    | none => simp at isFixed
    | some role =>
      cases role <;> first
        | (simp at isFixed; done)
        | exact (fixedRole_matches layouts raw _ _ instruction emitted trivial).mpr
            (Instruction.withSiteDecoder_role rawAt roleAt codeAt direct (by simp) notHole)
  · exact matched

#print axioms FeatureFlowValid.instruction_checked

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
    all_goals first
      | exact base
      | (split <;> simp_all [FeatureState.expand])
      | simp_all [FeatureState.expand]

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
    (constants : Nat → Option W32) (linkAt : Nat → Option Link) (raw : RawMethod)
    (profile : FeatureProfile)
    (certificate : FeatureCertificate) (roles : Nat → Option (Option FoldRole))
    (allKnown : AllKnown raw certificate)
    (site : FeatureSite) (state : Option FeatureState)
    (emitted : Instruction) (member : state ∈ certificate) :
    checkFeatureSiteWith layouts constants linkAt raw (knownLocals raw) profile
        (fun target => certificate[target]?) roles site state emitted =
      checkFeatureSiteWith layouts constants linkAt raw
        (LocalFacts.list raw.locals.length (featureLocalEligible raw)) profile
        (fun target => (expandCertificate raw certificate)[target]?) roles site
        (state.map (FeatureState.expand raw.locals.length)) emitted := by
  cases state with
  | none => cases emitted <;> rfl
  | some state =>
    have known := allKnown state member
    obtain ⟨pc, previous, instruction, role⟩ := site
    have transfer := featureTransferAtWith_expand layouts raw raw.locals.length
      (featureLocalEligible raw) profile (calleeConstant constants (linkAt pc) emitted) role
      instruction state known
    simp only [checkFeatureSiteWith, knownLocals, Option.map_some,
      wellShaped_expand (featureLocalEligible_none raw), known, Bool.true_and, transfer.1,
      FeatureState.expand_stack]
    cases transferred : featureTransferAtWith layouts raw
        (LocalFacts.known raw.locals.length (featureLocalEligible raw)) profile
        (calleeConstant constants (linkAt pc) emitted) role instruction state with
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
    (constants : Nat → Option W32) (linkAt : Nat → Option Link) (raw : RawMethod)
    (profile : FeatureProfile)
    (certificate : FeatureCertificate) (reachable : List Bool) (code : List Instruction) :
    FeatureFlowValid layouts constants linkAt raw profile certificate reachable code ↔
      AllKnown raw certificate ∧ FeatureListValid layouts constants linkAt raw profile
        (expandCertificate raw certificate) reachable code := by
  rw [FeatureFlowValid_iff_indexed]
  unfold FeatureListValid
  have sitesEqual (allKnown : AllKnown raw certificate) := all3_map
    (Option.map (FeatureState.expand raw.locals.length))
    (featureSites 0 none raw.code (foldRoles raw.code)) certificate code
    fun site state emitted member =>
      checkFeatureSiteWith_known_eq_list layouts constants linkAt raw profile certificate
        (fun target => (foldRoles raw.code)[target]?) allKnown site state emitted member
  constructor
  · rintro ⟨length, codeLength, mask, entry, sites⟩
    have allKnown : AllKnown raw certificate := by
      intro state member
      obtain ⟨⟨pc, previous, instruction, role⟩, emitted, checked⟩ := all3_mem sites member
      simp only [checkFeatureSiteWith, knownLocals, Bool.and_eq_true,
        wellShaped_expand (featureLocalEligible_none raw)] at checked
      exact checked.1.1.1.1
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
    {linkAt : Nat → Option Link}
    {raw : RawMethod} {profile : FeatureProfile} {certificate : FeatureCertificate}
    {reachable : List Bool} {code : List Instruction}
    (valid : FeatureFlowValid layouts constants linkAt raw profile certificate reachable code) :
    FeatureListValid layouts constants linkAt raw profile
      (certificate.map (Option.map (FeatureState.expand raw.locals.length))) reachable code :=
  ((FeatureFlowValid_iff_expand layouts constants linkAt raw profile certificate reachable code).mp
    valid).2

#print axioms FeatureFlowValid.expand

/-- The known facts of a specification state. -/
private def FeatureListState.compress (state : FeatureListState) : FeatureState :=
  { stack := state.stack, locals := compressKnown 0 state.locals }

/-- Every state a certificate the list specification accepts holds one fact per local. -/
private theorem FeatureListValid.lengths {layouts : Array RawLayout}
    {constants : Nat → Option W32} {linkAt : Nat → Option Link} {raw : RawMethod}
    {profile : FeatureProfile}
    {certificate : FeatureListCertificate} {reachable : List Bool} {code : List Instruction}
    (valid : FeatureListValid layouts constants linkAt raw profile certificate reachable code)
    {state : FeatureListState} (member : some state ∈ certificate) :
    state.locals.length = raw.locals.length := by
  obtain ⟨⟨pc, previous, instruction, role⟩, emitted, checked⟩ := all3_mem valid.2.2.2.2 member
  simp only [checkFeatureSiteWith, wellShaped, LocalFacts.list, Bool.and_eq_true,
    beq_iff_eq] at checked
  exact checked.1.1.1.1.1

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
    {linkAt : Nat → Option Link}
    {raw : RawMethod} {profile : FeatureProfile} {certificate : FeatureListCertificate}
    {reachable : List Bool} {code : List Instruction}
    (valid : FeatureListValid layouts constants linkAt raw profile certificate reachable code) :
    ∃ known : FeatureCertificate,
      (FeatureFlowValid layouts constants linkAt raw profile known reachable code ∧
        known.map (Option.map (FeatureState.expand raw.locals.length)) = certificate) ∧
      ∀ other : FeatureCertificate,
        FeatureFlowValid layouts constants linkAt raw profile other reachable code →
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
  have accepted : FeatureFlowValid layouts constants linkAt raw profile known reachable code :=
    (FeatureFlowValid_iff_expand layouts constants linkAt raw profile known reachable code).mpr
      ⟨allKnown, expanded ▸ valid⟩
  refine ⟨known, ⟨accepted, expanded⟩, fun other otherValid otherExpanded => ?_⟩
  have otherKnown :=
    ((FeatureFlowValid_iff_expand layouts constants linkAt raw profile other reachable code).mp
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
def FeatureEdge (layouts : Array RawLayout) (constants : Nat → Option W32)
    (linkAt : Nat → Option Link) (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureCertificate) (code : List Instruction) (pc target : Nat) : Prop :=
  ∃ instruction role state emitted after successors,
    (raw.code.zip (foldRoles raw.code))[pc]? = some (instruction, role) ∧
    certificate[pc]? = some (some state) ∧ code[pc]? = some emitted ∧
    featureTransferAt layouts raw profile (calleeConstant constants (linkAt pc) emitted) role
      instruction state = some after ∧
    featureSuccessors role pc instruction state.stack = some successors ∧ target ∈ successors

/-- Validation establishes closure under every independently recomputed edge,
    including backedges and every possible switch destination. -/
theorem FeatureFlowValid.edge_closed {layouts : Array RawLayout}
    {constants : Nat → Option W32} {linkAt : Nat → Option Link} {raw : RawMethod}
    {profile : FeatureProfile}
    {certificate : FeatureCertificate} {reachable : List Bool} {code : List Instruction}
    (valid : FeatureFlowValid layouts constants linkAt raw profile certificate reachable code)
    {pc target : Nat}
    (edge : FeatureEdge layouts constants linkAt raw profile certificate code pc target) :
    ∃ incoming, certificate[target]? = some (some incoming) := by
  obtain ⟨instruction, role, state, emitted, after, successors, rawAt, stateAt, codeAt,
    transferred, successorsAt, member⟩ := edge
  obtain ⟨instructionAt, roleAt⟩ := List.getElem?_zip_eq_some.mp rawAt
  have indexed := featureSites_at instructionAt roleAt
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
    (linkAt : Nat → Option Link) (raw : RawMethod) (profile : FeatureProfile)
    (certificate : FeatureCertificate) (code : List Instruction) : Nat → Prop where
  | entry : FeaturePath layouts constants linkAt raw profile certificate code 0
  | next {pc target} : FeaturePath layouts constants linkAt raw profile certificate code pc →
      FeatureEdge layouts constants linkAt raw profile certificate code pc target →
        FeaturePath layouts constants linkAt raw profile certificate code target

/-- Arbitrarily many steps through the validated graph remain in the emitted
    reachable mask; this includes cyclic paths without a bound on iterations. -/
theorem FeatureFlowValid.path_reachable {layouts : Array RawLayout}
    {constants : Nat → Option W32} {linkAt : Nat → Option Link} {raw : RawMethod}
    {profile : FeatureProfile}
    {certificate : FeatureCertificate} {reachable : List Bool} {code : List Instruction}
    (valid : FeatureFlowValid layouts constants linkAt raw profile certificate reachable code)
    {pc : Nat} (path : FeaturePath layouts constants linkAt raw profile certificate code pc) :
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
