import CIL.Extraction.Translation

/-!
# The body and metadata check on literal evidence

The evidence of `Arithmetic::Add(ulong,ulong)` as the extractor emits it: every byte list is a
`fixedBytes` literal. Each kind of literal equals, in the kernel, the same bytes written as a list
literal; the longer ones are split into 32-byte literals here to keep lines short.
`bodyMatches` is irreducible, so the elaborator's `decide` refuses it at once, within a small
heartbeat budget, and only kernel evaluation decides it. Fixtures that build their evidence with a
function must use kernel evaluation too, since the elaborator would evaluate the builder by name
without sharing. The cost rows at the end bound how elaborating a byte literal and checking a body
read from one grow with the number of bytes.
-/

namespace Tests.BodyLiteral

open CIL CIL.Extraction

/-! ## The evidence as list literals -/

namespace Lists

/-- The table stream header of the `Examples` assembly. -/
def tableHeader : List Nat :=
  [0, 0, 0, 0, 2, 0, 0, 1, 87, 223, 163, 43, 9, 30, 0, 0, 0, 250, 1, 51, 0, 22, 0, 0, 1, 0, 0, 0,
   106, 0, 0, 0, 227, 0, 0, 0, 227, 0, 0, 0, 248, 4, 0, 0, 191, 6, 0, 0, 43, 0, 0, 0, 37, 2, 0, 0,
   26, 0, 0, 0, 50, 1, 0, 0, 1, 0, 0, 0, 31, 0, 0, 0, 13, 0, 0, 0, 111, 0, 0, 0, 20, 0, 0, 0, 31,
   0, 0, 0, 34, 0, 0, 0, 28, 0, 0, 0, 85, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 27, 0, 0, 0,
   76, 0, 0, 0, 60, 1, 0, 0, 88, 0, 0, 0]

/-- The `Assembly` row of the `Examples` assembly. -/
def assemblyRow : List Nat :=
  [4, 128, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 52, 0, 0]

/-- The heap entries the assembly block carries. -/
def assemblyStrings : List ByteEntry :=
  [(0, [0]), (13321, [69, 120, 97, 109, 112, 108, 101, 115, 0])]

/-- The bytes of `Add`'s body. -/
def bodyBytes : List Nat := [18, 2, 3, 88, 42]

/-- The rows of `Add`'s metadata slice. -/
def rows : List ByteEntry :=
  [(16777235, [6, 0, 115, 57, 153, 38]), (33554505, [128, 1, 16, 0, 223, 12, 9, 52, 77, 0, 70, 0,
   244, 1]), (33554506, [16, 1, 16, 0, 236, 57, 9, 52, 101, 0, 70, 0, 7, 2]), (100663796, [192, 68,
   0, 0, 0, 0, 150, 0, 111, 14, 52, 10, 203, 2]), (587202561, [11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   77, 17, 217, 23, 0, 0, 0, 0])]

/-- The `#Strings` entries of `Add`'s metadata slice. -/
def strings : List ByteEntry :=
  [(0, [0]), (3295, [65, 114, 105, 116, 104, 109, 101, 116, 105, 99, 0]), (3695, [65, 100, 100,
   0]), (6105, [83, 121, 115, 116, 101, 109, 46, 82, 117, 110, 116, 105, 109, 101, 0]), (9881, [83,
   121, 115, 116, 101, 109, 0]), (13321, [69, 120, 97, 109, 112, 108, 101, 115, 0]), (14707, [79,
   98, 106, 101, 99, 116, 0])]

/-- The `#Blob` entries of `Add`'s metadata slice. -/
def blobs : List ByteEntry :=
  [(2612, [5, 0, 2, 11, 11, 11]), (4429, [8, 176, 63, 95, 127, 17, 213, 10, 58])]

/-- The bytes the `Assembly` row spells. -/
def identity : List Nat :=
  [69, 120, 97, 109, 112, 108, 101, 115, 44, 32, 86, 101, 114, 115, 105, 111, 110, 61, 49, 46, 48,
   46, 48, 46, 48, 44, 32, 67, 117, 108, 116, 117, 114, 101, 61, 110, 101, 117, 116, 114, 97, 108,
   44, 32, 80, 117, 98, 108, 105, 99, 75, 101, 121, 84, 111, 107, 101, 110, 61, 110, 117, 108, 108]

/-- The owner name the metadata gives `Add`. -/
def owner : List Nat :=
  [69, 120, 97, 109, 112, 108, 101, 115, 44, 32, 86, 101, 114, 115, 105, 111, 110, 61, 49, 46, 48,
   46, 48, 46, 48, 44, 32, 67, 117, 108, 116, 117, 114, 101, 61, 110, 101, 117, 116, 114, 97, 108,
   44, 32, 80, 117, 98, 108, 105, 99, 75, 101, 121, 84, 111, 107, 101, 110, 61, 110, 117, 108, 108,
   58, 58, 69, 120, 97, 109, 112, 108, 101, 115, 46, 65, 114, 105, 116, 104, 109, 101, 116, 105,
   99]

/-- The full name the metadata gives `Add`. -/
def signature : List Nat :=
  [83, 121, 115, 116, 101, 109, 46, 85, 73, 110, 116, 54, 52, 32, 69, 120, 97, 109, 112, 108, 101,
   115, 46, 65, 114, 105, 116, 104, 109, 101, 116, 105, 99, 58, 58, 65, 100, 100, 40, 83, 121, 115,
   116, 101, 109, 46, 85, 73, 110, 116, 54, 52, 44, 83, 121, 115, 116, 101, 109, 46, 85, 73, 110,
   116, 54, 52, 41]

end Lists

/-! ## The evidence as the extractor emits it -/

def assembly0Metadata : Extraction.AssemblyMetadata :=
  { identity := "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null",
    tableHeader :=
      (fixedBytes 32 0x000000000200000157DFA32B091E000000FA013300160000010000006A000000) ++
      (fixedBytes 32 0xE3000000E3000000F8040000BF0600002B000000250200001A00000032010000) ++
      (fixedBytes 32 0x010000001F0000000D0000006F000000140000001F000000220000001C000000) ++
      (fixedBytes 32 0x550000000300000001000000040000001B0000004C0000003C01000058000000),
    assemblyRow := (fixedBytes 22 0x04800000010000000000000000000000000009340000),
    strings := [(0, (fixedBytes 1 0x00)), (13321, (fixedBytes 9 0x4578616D706C657300))],
    blobs := [(0, (fixedBytes 1 0x00))] }

/-- The block's byte literals are the list literals. -/
theorem assembly_literals_are_lists :
    assembly0Metadata =
      { assembly0Metadata with
        tableHeader := Lists.tableHeader, assemblyRow := Lists.assemblyRow,
        strings := Lists.assemblyStrings, blobs := [(0, [0])] } := by
  cil_kernel_rfl
#print axioms assembly_literals_are_lists

/-- The unsigned 64-bit integer. -/
def word : TypeExpr := .atom runtimeScope "System.UInt64"
def method0Original : RawMethod :=
  { token := 100663796,
    owner :=
      "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null::Examples.Arithmetic",
    hasThis := false, explicitThis := false, callingConvention := 0, attributes := 150,
    implementation := 0, returnType := word, parameters := [word, word], locals := [],
    initLocals := false, maxStack := 8, genericParameters := [],
    code := [{ offset := 0, opcode := 2, operand := .none },
             { offset := 1, opcode := 3, operand := .none },
             { offset := 2, opcode := 88, operand := .none },
             { offset := 3, opcode := 42, operand := .none }] }
def method0Bytes : List Nat :=
  (fixedBytes 5 0x120203582A)

/-- The body literal is the list literal. -/
theorem body_literal_is_list : method0Bytes = Lists.bodyBytes := by cil_kernel_rfl
#print axioms body_literal_is_list

def method0Metadata : Extraction.MethodMetadata :=
  { own :=
      { assembly := assembly0Metadata,
        rows := [(16777235, (fixedBytes 6 0x060073399926)),
          (33554505, (fixedBytes 14 0x80011000DF0C09344D004600F401)),
          (33554506, (fixedBytes 14 0x10011000EC390934650046000702)),
          (100663796, (fixedBytes 14 0xC0440000000096006F0E340ACB02)),
          (587202561, (fixedBytes 20 0x0B00000000000000000000004D11D91700000000))],
        strings := [(0, (fixedBytes 1 0x00)), (3295, (fixedBytes 11 0x41726974686D6574696300)),
          (3695, (fixedBytes 4 0x41646400)),
          (6105, (fixedBytes 15 0x53797374656D2E52756E74696D6500)),
          (9881, (fixedBytes 7 0x53797374656D00)), (13321, (fixedBytes 9 0x4578616D706C657300)),
          (14707, (fixedBytes 7 0x4F626A65637400))],
        blobs := [(2612, (fixedBytes 6 0x0500020B0B0B)),
          (4429, (fixedBytes 9 0x08B03F5F7F11D50A3A))],
        userStrings := [], corlib := 1, links := [⟨1, 100663796, 0, 33554505⟩] },
    others := [] }

/-- The slice's byte literals are the list literals. -/
theorem metadata_literals_are_lists :
    method0Metadata =
      { method0Metadata with
        own := { method0Metadata.own with
          rows := Lists.rows, strings := Lists.strings, blobs := Lists.blobs } } := by
  cil_kernel_rfl
#print axioms metadata_literals_are_lists

/-- The lookup tables of `method0Metadata`, as the decoder builds them. -/
def method0Tables : List Extraction.IndexTables :=
  match method0Metadata.tables with
  | .ok built => built
  | .error _ => []

/-- The lookup tables as the extractor emits them. -/
def method0TablesLiteral : List Extraction.IndexTables :=
  [{ rows := (.node (.node (.node .leaf 16777235 (fixedBytes 6 0x060073399926) .leaf) 33554505
       (fixedBytes 14 0x80011000DF0C09344D004600F401) .leaf) 33554506
       (fixedBytes 14 0x10011000EC390934650046000702) (.node (.node .leaf 100663796
       (fixedBytes 14 0xC0440000000096006F0E340ACB02) .leaf) 587202561
       (fixedBytes 20 0x0B00000000000000000000004D11D91700000000) .leaf)),
     strings := (.node (.node (.node .leaf 0 (fixedBytes 1 0x00) .leaf) 3295
       (fixedBytes 11 0x41726974686D6574696300) (.node .leaf 3695 (fixedBytes 4 0x41646400) .leaf))
       6105 (fixedBytes 15 0x53797374656D2E52756E74696D6500) (.node (.node .leaf 9881
       (fixedBytes 7 0x53797374656D00) .leaf) 13321 (fixedBytes 9 0x4578616D706C657300) (.node
       .leaf 14707 (fixedBytes 7 0x4F626A65637400) .leaf))),
     blobs := (.node (.node .leaf 2612 (fixedBytes 6 0x0500020B0B0B) .leaf) 4429
       (fixedBytes 9 0x08B03F5F7F11D50A3A) .leaf),
     userStrings := .leaf,
     links := (.node .leaf 4395631092 (0, 33554505) .leaf),
     instanceBefore := .leaf,
     instanceTotal := (.node .leaf 33554505 0 .leaf),
     genericOwners := .leaf }]

/-- The emitted tables are the ones the decoder builds from the slice. -/
theorem tables_literal_is_built : method0TablesLiteral = method0Tables := by cil_kernel_rfl
#print axioms tables_literal_is_built

/-- The bytes the `Assembly` row spells, which the extraction proves once per assembly. -/
def assembly0Identity : List Nat :=
  (fixedBytes 32 0x4578616D706C65732C2056657273696F6E3D312E302E302E302C2043756C7475) ++
    (fixedBytes 31 0x72653D6E65757472616C2C205075626C69634B6579546F6B656E3D6E756C6C)

/-- The identity literal is the list literal. -/
theorem identity_literal_is_list : assembly0Identity = Lists.identity := by cil_kernel_rfl
#print axioms identity_literal_is_list

theorem assembly0_identified : AssemblyIdentified assembly0Metadata assembly0Identity :=
  ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩

/-- `assembly0Metadata` stating a header with one `TypeDef` row more than its bytes give. -/
def miscountedAssembly : AssemblyMetadata :=
  let counts := assembly0Metadata.header.rowCounts.map fun (table, count) =>
    (table, if table == Table.typeDef then count + 1 else count)
  { assembly0Metadata with
    header := TableHeader.ofCounts assembly0Metadata.header.heapSizes counts }

/-- `Add`'s slice of `miscountedAssembly`. -/
def miscountedSlice : MetadataSlice := { method0Metadata.own with assembly := miscountedAssembly }

/-- A stated header its bytes do not decode to is refused: the assembly is not identified with
    it, and a slice of it has no index. -/
theorem refuses_a_header_its_bytes_do_not_give :
    (decodeTableHeader miscountedAssembly.tableHeader).toOption ≠
        some miscountedAssembly.header ∧
      (match miscountedSlice.index with
        | .error .malformedTableHeader => true
        | _ => false) = true := by
  decide +kernel
#print axioms refuses_a_header_its_bytes_do_not_give

/-- The owner name and the full name the metadata gives `Add`, as bytes. -/
def method0Names : Extraction.MethodNames :=
  { owner :=
      (fixedBytes 32 0x4578616D706C65732C2056657273696F6E3D312E302E302E302C2043756C7475) ++
      (fixedBytes 32 0x72653D6E65757472616C2C205075626C69634B6579546F6B656E3D6E756C6C3A) ++
      (fixedBytes 20 0x3A4578616D706C65732E41726974686D65746963),
    signature :=
      (fixedBytes 32 0x53797374656D2E55496E743634204578616D706C65732E41726974686D657469) ++
      (fixedBytes 32 0x633A3A4164642853797374656D2E55496E7436342C53797374656D2E55496E74) ++
      (fixedBytes 3 0x363429) }

/-- The name literals are the list literals. -/
theorem names_literals_are_lists :
    method0Names = { method0Names with owner := Lists.owner, signature := Lists.signature } := by
  cil_kernel_rfl
#print axioms names_literals_are_lists

/-- The signature a proof selects `Add` by. -/
def method0Signature : String :=
  "System.UInt64 Examples.Arithmetic::Add(System.UInt64,System.UInt64)"

def method0Body : Extraction.BodyEvidence :=
  { bytes := method0Bytes, tokens := { operands := [] }, metadata := method0Metadata,
              identities := [assembly0Identity], tables := method0Tables, names := method0Names,
              pinned := cil_pin_index [assembly0Identity] }

/-- The pin of the assembly the method was extracted from. -/
def pin : AssemblyPin := ⟨"Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"⟩

theorem add_body_decodes :
    BodyDecodes [pin] pin method0Body method0Original [] method0Signature :=
  ⟨AllIdentified.cons assembly0_identified AllIdentified.nil, by decide +kernel,
    by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl, by decide +kernel⟩
#print axioms add_body_decodes

set_option maxHeartbeats 20000 in
/-- error: Tactic `decide` failed to reduce -/
#guard_msgs (substring := true) in
example : bodyMatches method0Body method0Original [] = true := by decide

/-- A changed body byte fails the kernel's decision: the second byte of the literal is `03`. -/
theorem changed_byte_is_rejected :
    bodyMatches { method0Body with bytes := fixedBytes 5 0x120303582A } method0Original [] =
      false := by
  decide +kernel
#print axioms changed_byte_is_rejected

/-- A full name the row does not spell fails the kernel's decision: `Add` read as `Sub`. -/
theorem other_full_name_is_rejected :
    bodyMatches { method0Body with names := { method0Names with
      signature := method0Names.signature.set 35 83 |>.set 36 117 |>.set 37 98 } }
      method0Original [] = false := by
  decide +kernel
#print axioms other_full_name_is_rejected

/-! ## Cost of a byte literal -/

/-- `Add`'s decoded method with its code replaced by `count` `nop`s and a `ret`. -/
def nopMethod (count : Nat) : RawMethod :=
  { method0Original with
    code := (List.range count).map (fun offset =>
        { offset := offset, opcode := 0, operand := .none }) ++
      [{ offset := count, opcode := 42, operand := .none }] }

/-- The bytes of `nopMethod count`: a fat header with `Add`'s stack depth and no locals. -/
def nopBody (count : Nat) : List Nat :=
  let codeSize := count + 1
  [0x03, 0x30, 8, 0, codeSize % 256, codeSize / 256 % 256, codeSize / 65536 % 256, 0] ++
    [0, 0, 0, 0] ++ List.replicate count 0 ++ [0x2A]

/-- Two uppercase hexadecimal digits of a byte. -/
def hexByte (byte : Nat) : String :=
  let digits := "0123456789ABCDEF".toList
  String.ofList [digits[byte / 16]!, digits[byte % 16]!]

/-- How much more a cost may be at four times the bytes: linear growth with headroom for the
    logarithmic factor of the decode and for measurement noise. -/
def growthBound : Nat := 6

open Lean Elab Command Meta in
set_option maxHeartbeats 0 in
run_cmd do
  let mut previousElaboration := 0
  let mut previousDecode := 0
  let mut previousCheck := 0
  for count in [128, 512, 2048] do
    let bytes := nopBody count
    let name := mkIdent (Name.mkSimple s!"nopBytes{count}")
    let literal := Syntax.mkNumLit ("0x" ++ String.join (bytes.map hexByte))
    let start ← IO.getNumHeartbeats
    elabCommand (← `(def $name : List Nat := fixedBytes $(quote bytes.length) $literal))
    let elaboration := (← IO.getNumHeartbeats) - start
    logInfo m!"byte literal elaboration: {bytes.length} bytes, {elaboration} heartbeats"
    if previousElaboration != 0 && elaboration > previousElaboration * growthBound then
      throwError "byte literal elaboration grew faster than its bytes"
    previousElaboration := elaboration
    let proof := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let decoded ← liftTermElabM do
      let claim ← `(($name == nopBody $(quote count)) = true)
      instantiateMVars (← Term.elabTermAndSynthesize claim (some (mkSort 0)))
    let start ← IO.getNumHeartbeats
    match Kernel.check (← getEnv) {} (Expr.letE `decoded decoded proof (.bvar 0) false) with
    | .error error => throwKernelException error
    | .ok _ => pure ()
    let decode := (← IO.getNumHeartbeats) - start
    logInfo m!"byte literal decode: {bytes.length} bytes, {decode} heartbeats"
    if previousDecode != 0 && decode > previousDecode * growthBound then
      throwError "the kernel decode of a byte literal grew faster than its bytes"
    previousDecode := decode
    let statement ← liftTermElabM do
      let claim ← `(bodyMatches { method0Body with bytes := $name } (nopMethod $(quote count)) [] =
        true)
      instantiateMVars (← Term.elabTermAndSynthesize claim (some (mkSort 0)))
    let start ← IO.getNumHeartbeats
    match Kernel.check (← getEnv) {} (Expr.letE `checked statement proof (.bvar 0) false) with
    | .error error => throwKernelException error
    | .ok _ => pure ()
    let check := (← IO.getNumHeartbeats) - start
    logInfo m!"body check of a byte literal: {bytes.length} bytes, {check} heartbeats"
    if previousCheck != 0 && check > previousCheck * growthBound then
      throwError "the body check of a byte literal grew faster than its bytes"
    previousCheck := check

end Tests.BodyLiteral
