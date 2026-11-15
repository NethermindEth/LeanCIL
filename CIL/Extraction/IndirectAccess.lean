import CIL.Extraction.UnsafeTransfers
import CIL.Extraction.ValueDecoding

/-!
# Indirect accesses

A raw integer `ldind` or `stind` emits the instruction `Instruction.ofRaw?` decodes from it, a raw
`ldobj` or `stobj` decides the width and sign extension of the load or store extraction emits for
it, and a raw `cpblk` or `initblk` decides the alignment of its block operation, which an
`unaligned.` prefix lowers. `indirectAccessMatches` gives that one emission from the opcode, the
operand type and the instruction before it, and reserves the emitted loads, stores and block
operations for these opcodes and for calls, which `UnsafeCallsValid` binds.
`FeatureFlowValid` and `ScalarFlowValid` apply `indirectSiteWindow` at every reachable pc,
reading the neighbouring raw instructions through an index of the body built once.
-/

namespace CIL.Extraction

/-- The opcodes extraction admits after `unaligned.`: the integer `ldind` and `stind` forms,
    `ldfld`, `stfld`, `ldobj`, `stobj`, `cpblk` and `initblk`. -/
def unalignedTaker (opcode : Nat) : Bool :=
  (70 ≤ opcode && opcode ≤ 77) || (82 ≤ opcode && opcode ≤ 85) ||
    opcode ∈ [223, 123, 125, 113, 129, 65047, 65048]

/-- The alignment the instruction before an access gives it: `some none` without a prefix and
    `some (some n)` after `unaligned. n` for an `n` of 1, 2 or 4. `volatile.` and any other
    alignment give `none`, since extraction refuses both. -/
def accessAlignment : Option RawInstruction → Option (Option Nat)
  | some ⟨_, 65042, .integer alignment⟩ =>
    if alignment == 1 || alignment == 2 || alignment == 4 then some (some alignment.toNat)
    else none
  | some ⟨_, 65042, _⟩ | some ⟨_, 65043, _⟩ => none
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

/-- Every `ldind` and `stind` kind, `ldobj`, `stobj`, `cpblk` and `initblk`. -/
def indirectOpcode (opcode : Nat) : Bool :=
  (70 ≤ opcode && opcode ≤ 87) || opcode ∈ [223, 113, 129, 65047, 65048]

/-- Whether `typedTransferMatches` fixes the emission for `type` without a layout table: an
    integer vector, or a primitive or enum type. -/
private def layoutFreeTransfer (type : TypeExpr) : Bool :=
  (integerVectorWidth type).isSome || match typeStorage [] type with
    | some (.field kind) => (primitiveFieldWidth kind).isSome
    | _ => false

/-- An indirect access after `previous` emits exactly the instruction its opcode, operand type
    and prefix give; an aggregate `ldobj` or `stobj` emits its aggregate transfer, whose width
    the layout use binds; a span `ldobj` emits `.nop`, and `ldobj` or `stobj` of any other
    operand type is refused; an integer `ldind` or `stind` emits its decoded instruction. Any other
    instruction emits none of the forms `indirectEmission` names, except a call, which
    `UnsafeCallsValid` binds and which never emits an `ldind` or `stind`. -/
def indirectAccessMatches (previous : Option RawInstruction) (instruction : RawInstruction)
    (emitted : Instruction) : Bool :=
  if !indirectOpcode instruction.opcode then
    if instruction.opcode == 40 then !(emitted matches .ldind _ | .stind _)
    else !indirectEmission emitted
  else match accessAlignment previous, instruction.opcode, instruction.operand with
    | none, _, _ => false
    | some _, 113, .type (.aggregate ..) => (emitted matches .loadAggregate _)
    | some _, 129, .type (.aggregate ..) => (emitted matches .storeAggregate _)
    | some _, 113, .type type | some _, 129, .type type =>
      if layoutFreeTransfer type then
        typedTransferMatches [] type (instruction.opcode == 113) emitted
      -- A span `ldobj` copies nothing; extraction refuses every other operand type.
      else instruction.opcode == 113 && spanLocal type && (emitted matches .nop)
    | some alignment, opcode, _ =>
      valueEncodingMatches instruction emitted ||
        (indirectEmission? alignment opcode).any (sameIndirectEmission · emitted)

/-- The indirect access rule at `pc`, reading the raw instructions next to it through `rawAt`:
    `unaligned.` has an admitted alignment, precedes an instruction that takes it and emits
    nothing; `volatile.` is refused; every other instruction meets `indirectAccessMatches` with
    the instruction before it. -/
def indirectSiteWindow (rawAt : Nat → Option RawInstruction) (pc : Nat)
    (instruction : RawInstruction) (emitted : Instruction) : Bool :=
  match instruction.opcode with
  | 65042 =>
    (accessAlignment (some instruction)).any Option.isSome &&
      (rawAt (pc + 1)).any (fun next => unalignedTaker next.opcode) && (emitted matches .nop)
  | 65043 => false
  -- `pc - 1` saturates at 0, so the first instruction must not read itself as its prefix.
  | _ => indirectAccessMatches (if pc == 0 then none else rawAt (pc - 1)) instruction emitted

end CIL.Extraction
