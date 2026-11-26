import CIL.Extraction.ValueDecoding

/-!
# Indirect accesses

`Instruction.ofRaw?` decodes integer `ldind` and `stind`, and `cpblk` and `initblk` at the block
alignment `blockAlignment` reads from an `unaligned.` before them. `indirectAccessMatches`
checks the emitted instruction against the opcode, operand type and preceding instruction. It
reserves the block instructions for their two raw opcodes. Typed transfer calls retain their
method reference and use the bound runtime model. `ScalarFlowValid` applies
`indirectSiteWindow` at every reachable pc, reading the neighbouring raw instructions through an
index of the body built once.
-/

namespace CIL.Extraction

/-- The alignment the instruction before an access gives it: `some none` without a prefix and
    `some (some n)` after `unaligned. n` for an `n` of 1, 2 or 4. `volatile.` and any other
    alignment give `none`, since extraction refuses both. -/
def accessAlignment : Option RawInstruction → Option (Option Nat)
  | some ⟨_, 65042, operand⟩ => (prefixAlignment operand).map some
  | some ⟨_, 65043, _⟩ => none
  | _ => some none

/-- Indirect instructions whose operand or alignment comes from their raw site. -/
def indirectEmission : Instruction → Bool
  | .ldind _ | .stind _ | .cpblk _ | .initblk _ => true
  | _ => false

/-- The indirect load and store opcodes and the block memory operations. -/
def indirectOpcode (opcode : Nat) : Bool :=
  (70 ≤ opcode && opcode ≤ 87) || opcode ∈ [223, 65047, 65048]

/-- An indirect access after `previous` emits exactly the instruction its opcode, operand type
    and prefix give. Integer indirect loads and stores retain their decoded kinds. Any other
    raw opcode emits none of these four instructions. Modelled calls retain their method reference. -/
def indirectAccessMatches (previous : Option RawInstruction) (instruction : RawInstruction)
    (emitted : Instruction) (skipEncoding := false) : Bool :=
  if instruction.opcode == 0x71 || instruction.opcode == 0x81 ||
      (emitted matches .ldobj _ | .stobj _) then
    skipEncoding || valueEncodingMatches previous instruction emitted
  else if !indirectOpcode instruction.opcode then
    !indirectEmission emitted
  else match accessAlignment previous, instruction.operand with
    | some _, .none => skipEncoding || valueEncodingMatches previous instruction emitted
    | _, _ => false

/-- The indirect access rule at `pc`, reading the raw instructions next to it through `rawAt`:
    `unaligned.` has an admitted alignment, precedes an instruction that takes it and emits
    nothing; `volatile.` is refused; every other instruction meets `indirectAccessMatches` with
    the instruction before it. -/
def indirectSiteWindow (rawAt : Nat → Option RawInstruction) (pc : Nat)
    (instruction : RawInstruction) (emitted : Instruction) (skipEncoding := false)
    (previous := rawBefore rawAt pc) : Bool :=
  match instruction.opcode with
  | 65042 =>
    (rawAt (pc + 1)).any (prefixTakes instruction) && (emitted matches .nop)
  | 65043 => false
  | _ => indirectAccessMatches previous instruction emitted skipEncoding

end CIL.Extraction
