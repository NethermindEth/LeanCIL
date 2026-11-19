import CIL.Extraction.UnsafeTransfers
import CIL.Extraction.ValueDecoding

/-!
# Indirect accesses

`Instruction.ofRaw?` decodes integer `ldind` and `stind`. A raw `cpblk` or `initblk` determines
its block alignment, which an `unaligned.` prefix lowers. `indirectAccessMatches` checks the
emitted instruction against the opcode, operand type and preceding instruction. It reserves
those memory operations for these opcodes and for calls, which `UnsafeCallsValid` binds.
`FeatureFlowValid` and `ScalarFlowValid` apply `indirectSiteWindow` at every reachable pc,
reading the neighbouring raw instructions through an index of the body built once.
-/

namespace CIL.Extraction

/-- The alignment the instruction before an access gives it: `some none` without a prefix and
    `some (some n)` after `unaligned. n` for an `n` of 1, 2 or 4. `volatile.` and any other
    alignment give `none`, since extraction refuses both. -/
def accessAlignment : Option RawInstruction → Option (Option Nat)
  | some ⟨_, 65042, operand⟩ => (prefixAlignment operand).map some
  | some ⟨_, 65043, _⟩ => none
  | _ => some none

/-- The one instruction extraction emits for a `cpblk` or `initblk` whose prefix gives
    `alignment`; `none` for any other opcode. -/
def indirectEmission? (alignment : Option Nat) : Nat → Option Instruction
  | 65047 => some (.memory (.copyBlock (alignment.getD defaultBlockAlignment)))
  | 65048 => some (.memory (.initBlock (alignment.getD defaultBlockAlignment)))
  | _ => none

/-- Whether two emitted loads, stores or block operations are the same instruction. -/
def sameIndirectEmission : Instruction → Instruction → Bool
  | .loadScalar width signed, .loadScalar otherWidth otherSigned =>
    width == otherWidth && signed == otherSigned
  | .storeScalar width, .storeScalar otherWidth => width == otherWidth
  | .memory (.copyBlock alignment), .memory (.copyBlock other)
  | .memory (.initBlock alignment), .memory (.initBlock other) => alignment == other
  | _, _ => false

/-- Emitted loads, stores and block operations whose width, sign extension or alignment a raw
    instruction decides; only the opcodes `indirectOpcode` names and calls may emit one. -/
def indirectEmission : Instruction → Bool
  | .loadScalar .. | .storeScalar _ | .ldind _ | .stind _ | .loadAggregate _ | .storeAggregate _
  | .memory (.copyBlock _) | .memory (.initBlock _)
  | .memory .load128 | .memory .load256 | .memory .load512
  | .memory .store128 | .memory .store256 | .memory .store512 => true
  | _ => false

/-- The indirect load and store opcodes and the block memory operations. -/
def indirectOpcode (opcode : Nat) : Bool :=
  (70 ≤ opcode && opcode ≤ 87) || opcode ∈ [223, 65047, 65048]

/-- An indirect access after `previous` emits exactly the instruction its opcode, operand type
    and prefix give. Integer indirect loads and stores retain their decoded kinds. Any other
    instruction emits none of the forms `indirectEmission` names, except a call, which
    `UnsafeCallsValid` binds and which never emits an `ldind` or `stind`. -/
def indirectAccessMatches (previous : Option RawInstruction) (instruction : RawInstruction)
    (emitted : Instruction) (skipEncoding := false) : Bool :=
  if instruction.opcode == 0x71 then emitted matches .ldobj _
  else if instruction.opcode == 0x81 then emitted matches .stobj _
  else if !indirectOpcode instruction.opcode then
    if instruction.opcode == 40 then !(emitted matches .ldind _ | .stind _)
    else !indirectEmission emitted
  else match accessAlignment previous, instruction.opcode, instruction.operand with
    | none, _, _ => false
    | some alignment, opcode, .none =>
      skipEncoding || valueEncodingMatches previous instruction emitted ||
        (indirectEmission? alignment opcode).any (sameIndirectEmission · emitted)
    | _, _, _ => false

/-- The indirect access rule at `pc`, reading the raw instructions next to it through `rawAt`:
    `unaligned.` has an admitted alignment, precedes an instruction that takes it and emits
    nothing; `volatile.` is refused; every other instruction meets `indirectAccessMatches` with
    the instruction before it. -/
def indirectSiteWindow (rawAt : Nat → Option RawInstruction) (pc : Nat)
    (instruction : RawInstruction) (emitted : Instruction) (skipEncoding := false) : Bool :=
  match instruction.opcode with
  | 65042 =>
    (rawAt (pc + 1)).any (prefixTakes instruction) && (emitted matches .nop)
  | 65043 => false
  | _ => indirectAccessMatches (rawBefore rawAt pc) instruction emitted skipEncoding

end CIL.Extraction
