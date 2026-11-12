import CIL.Extraction.Translation

/-!
# The body and metadata check on literal evidence

The evidence of `Arithmetic::Add(ulong,ulong)` as the extractor emits it, written out as
literals. `bodyMatches` is irreducible, so the elaborator's `decide` refuses it at once, within
a small heartbeat budget, and only kernel evaluation decides it. Fixtures that build their
evidence with a function must use kernel evaluation too, since the elaborator would evaluate
the builder by name without sharing.
-/

namespace Tests.BodyLiteral

open CIL CIL.Extraction
def assembly0Metadata : Extraction.AssemblyMetadata :=
  { identity := "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null",
              tableHeader := [0, 0, 0, 0, 2, 0, 0, 1, 87, 223, 163, 43, 9, 30, 0, 0, 0, 250, 1,
              51, 0, 22, 0, 0, 1, 0, 0, 0, 106, 0, 0, 0, 227, 0, 0, 0, 227, 0, 0, 0, 248, 4, 0, 0,
              191, 6, 0, 0, 43, 0, 0, 0, 37, 2, 0, 0, 26, 0, 0, 0, 50, 1, 0, 0, 1, 0, 0, 0, 31, 0,
              0, 0, 13, 0, 0, 0, 111, 0, 0, 0, 20, 0, 0, 0, 31, 0, 0, 0, 34, 0, 0, 0, 28, 0, 0, 0,
              85, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 27, 0, 0, 0, 76, 0, 0, 0, 60, 1, 0,
              0, 88, 0, 0, 0], assemblyRow := [4, 128, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              0, 0, 9, 52, 0, 0], strings := [(0, [0]), (13321, [69, 120, 97, 109, 112, 108, 101,
              115, 0])], blobs := [(0, [0])] }
/-- The unsigned 64-bit integer. -/
def word : TypeExpr := .atom runtimeScope "System.UInt64"

def method0Original : RawMethod :=
  { token := 100663796,
    owner := "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null::Examples.Arithmetic",
    hasThis := false, explicitThis := false, callingConvention := 0, attributes := 150,
    implementation := 0, returnType := word, parameters := [word, word], locals := [],
    initLocals := false, maxStack := 8, genericParameters := [],
    code := [{ offset := 0, opcode := 2, operand := .none },
             { offset := 1, opcode := 3, operand := .none },
             { offset := 2, opcode := 88, operand := .none },
             { offset := 3, opcode := 42, operand := .none }] }
def method0Bytes : List Nat :=
  [18, 2, 3, 88, 42]
def method0Metadata : Extraction.MethodMetadata :=
  { own := { assembly := assembly0Metadata, rows := [(16777235, [6, 0, 115, 57, 153, 38]),
              (33554505, [128, 1, 16, 0, 223, 12, 9, 52, 77, 0, 70, 0, 244, 1]), (33554506, [16,
              1, 16, 0, 236, 57, 9, 52, 101, 0, 70, 0, 7, 2]), (100663796, [192, 68, 0, 0, 0, 0,
              150, 0, 111, 14, 52, 10, 203, 2]), (587202561, [10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
              77, 17, 217, 23, 0, 0, 0, 0])], strings := [(0, [0]), (3295, [65, 114, 105, 116,
              104, 109, 101, 116, 105, 99, 0]), (3695, [65, 100, 100, 0]), (6105, [83, 121, 115,
              116, 101, 109, 46, 82, 117, 110, 116, 105, 109, 101, 0]), (9881, [83, 121, 115, 116,
              101, 109, 0]), (13321, [69, 120, 97, 109, 112, 108, 101, 115, 0]), (14707, [79, 98,
              106, 101, 99, 116, 0])], blobs := [(2612, [5, 0, 2, 11, 11, 11]), (4429, [8, 176,
              63, 95, 127, 17, 213, 10, 58])], userStrings := [], corlib := 1, links := [⟨1,
              100663796, 0, 33554505⟩] }, others := [] }
def method0Body : Extraction.BodyEvidence :=
  { bytes := method0Bytes, tokens := { operands := [] }, metadata := method0Metadata,
              rva := 17600 }

/-- The pin of the assembly the method was extracted from. -/
def pin : AssemblyPin := ⟨"Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"⟩

theorem add_body_decodes : BodyDecodes pin method0Body method0Original := by decide +kernel
#print axioms add_body_decodes

set_option maxHeartbeats 20000 in
/-- error: Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : BodyDecodes pin method0Body method0Original := by decide

/-- A changed body byte fails the kernel's decision. -/
theorem changed_byte_is_rejected :
    bodyMatches pin { method0Body with bytes := method0Bytes.set 1 3 } method0Original = false := by
  decide +kernel
#print axioms changed_byte_is_rejected

end Tests.BodyLiteral
