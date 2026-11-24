import CIL.Runtime.Net11WinX64.RangeConstructor

/-! The pinned Examples.Throws.Percent body, its original string tokens and its reference
through System.Runtime to the two-string constructor in CoreLib. -/

namespace Tests.PercentRuntime.Source
open CIL CIL.Extraction CIL.Runtime.Net11WinX64
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Examples assembly identity, table header and heaps. -/
def assembly0Metadata : AssemblyMetadata := {
  identity := "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null",
  tableHeader := (fixedBytes 128 0x000000000200000157DFA32B091E000000FA013300160000010000006A000000EB000000F100000013050000E40600002B0000002A0200001A00000032010000010000001F0000000D00000071000000140000001F000000220000001C00000057000000030000000100000004000000230000004C0000003E01000058000000),
  header := .ofCounts 0 [(0, 1), (1, 106), (2, 235), (4, 241), (6, 1299),
    (8, 1764), (9, 43), (10, 554), (11, 26), (12, 306), (14, 1),
    (15, 31), (16, 13), (17, 113), (21, 20), (23, 31), (24, 34),
    (25, 28), (27, 87), (29, 3), (32, 1), (35, 4), (41, 35), (42, 76),
    (43, 318), (44, 88)],
  assemblyRow := (fixedBytes 22 0x04800000010000000000000000000000000001000000),
  strings := [(0, (fixedBytes 1 0x00)), (1, (fixedBytes 9 0x4578616D706C657300))],
  blobs := [(0, (fixedBytes 1 0x00))]}

/-- Identity bytes for the compiled Examples fixture. -/
def id0 := bytesOf "Examples, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

/-- The image metadata authenticates the Examples identity. -/
theorem image0_identified : AssemblyIdentified assembly0Metadata id0 := ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms image0_identified

/-- The caller constructor reference after resolution to its defining method. -/
def member : CallSite := {
  method := {
    owner := .object coreLibraryScope "System.ArgumentOutOfRangeException",
    name := name! ".ctor",
    hasThis := true,
    genericArity := 0,
    returnType := .void,
    parameters := [.object coreLibraryScope "System.String", .object coreLibraryScope "System.String"],
    methodArguments := []},
  name := ".ctor",
  target := .managed 100666618,
  typeArguments := [],
  ownerArgumentCount := 0,
  parameterCount := 2,
  returnsValue := false,
  declared := {
    convention := 32,
    returnType := .void,
    parameters := [.object Extraction.runtimeScope "System.String",
      .object Extraction.runtimeScope "System.String"]}}

/-- Metadata rows and heap entries used by this method. -/
def rows : MethodMetadata := {
  own := {
    assembly := assembly0Metadata,
    rows := [(16777235, (fixedBytes 6 0x060004000600)), (16777307, (fixedBytes 6 0x060002000600)),
      (33554613, (fixedBytes 14 0x81011000080003004D00AF00F103)),
      (33554614, (fixedBytes 14 0x81011000FFFF03004D00AF00F903)),
      (100664308, (fixedBytes 14 0x0000000000009600050001005705)),
      (167772664, (fixedBytes 6 0xD90201000200)), (587202561, (fixedBytes 20 0x0B00000000000000000000000300070000000000)),
      (704643091, (fixedBytes 8 0x000000006501FFFF)), (704643092, (fixedBytes 8 0x000018006F01FFFF))],
    strings := [(0, (fixedBytes 1 0x00)), (1, (fixedBytes 6 0x2E63746F7200)),
      (2, (fixedBytes 28 0x417267756D656E744F75744F6652616E6765457863657074696F6E00)),
      (3, (fixedBytes 9 0x4578616D706C657300)), (4, (fixedBytes 7 0x4F626A65637400)),
      (5, (fixedBytes 8 0x50657263656E7400)), (6, (fixedBytes 7 0x53797374656D00)),
      (7, (fixedBytes 15 0x53797374656D2E52756E74696D6500)), (8, (fixedBytes 7 0x5468726F777300))],
    blobs := [(1, (fixedBytes 5 0x0400010909)), (2, (fixedBytes 6 0x052002010E0E)),
      (3, (fixedBytes 9 0x08B03F5F7F11D50A3A))],
    userStrings := [(1, (fixedBytes 12 0x0B760061006C007500650000)),
      (277, (fixedBytes 40 0x276D0075007300740020006E006F0074002000650078006300650065006400200031003000300000))],
    corlib := 1,
    links := [⟨0, 16777235, 2, 33554594⟩, ⟨0, 16777307, 2, 33554675⟩,
      ⟨0, 167772664, 2, 100666618⟩, ⟨1, 100664308, 0, 33554613⟩,
      ⟨4, 16777235, 1, 654311851⟩, ⟨4, 16777307, 1, 654311462⟩]},
  others := rangeDependencies}

/-- Metadata indexes reconstructed from the supplied rows. -/
private def tables : List IndexTables := rows.tables.toOption.getD []

/-- The reconstructed indexes match the carried metadata. -/
theorem tables_valid : tablesMatch rows tables = true := by decide +kernel
#print axioms tables_valid

/-- Original caller body, scoped token operands and assembly pins. -/
def source : BodyEvidence := {
  bytes := [94, 2, 31, 100, 54, 16, 114, 1, 0, 0, 112, 114, 21, 1, 0, 112, 115, 248, 1, 0, 10, 122, 2, 42],
  tokens := { operands := [(1879048193, .text "value"), (1879048469, .text "must not exceed 100"), (167772664, .call member)] }, metadata := rows,
  tables, identities := [id0, facadeIdentity, coreIdentity], pinned := PinnedIndex.ofIdentities [id0, facadeIdentity, coreIdentity], names := {} }

/-- Constructor resolution through the pinned facade and defining assembly. -/
def resolved := do
  let env ← source.environment
  let site ← env.methodSite 167772664
  return site.definition

/-- The caller refers to the two-string CoreLib constructor. -/
theorem defining_method : resolved.toOption = some (some (2, 100666618)) := by decide +kernel
#print axioms defining_method

/-- Decode the caller body bytes and branch targets with its scoped metadata. -/
def decoded := do
  let env ← source.environment.mapError BodyError.metadata
  decodeBody env 0 0 source

/-- The allocation operand resolves to the checked constructor reference. -/
theorem bound_newobj : (decoded.toOption.bind fun d => (d.code[5]?).map (·.operand)) = some (.call member) := by decide +kernel
#print axioms bound_newobj

/-- Method declaration with instructions, stack limit and locals from the decoder. -/
def raw : RawMethod :=
  let b := decoded.toOption.getD { maxStack := 0, initLocals := false, localSignature := 0, code := [], statics := [] }
  { token := 100664308, owner := (assembly0Metadata.identity ++ "::Examples.Throws"),
    hasThis := false, explicitThis := false, callingConvention := 0, attributes := 150,
    implementation := 0, returnType := .atom runtimeScope "System.UInt32",
    parameters := [.atom runtimeScope "System.UInt32"], locals := [], initLocals := b.initLocals,
    maxStack := b.maxStack, genericParameters := [], code := b.code }

/-- Encoded owner, bases and signature checked against the method declaration. -/
def names : MethodNames := {
  owner := bytesOf (assembly0Metadata.identity ++ "::Examples.Throws"),
  signature := bytesOf "System.UInt32 Examples.Throws::Percent(System.UInt32)" }

/-- The metadata and body bytes justify this caller definition. -/
theorem body_bound : BodyDecodes [⟨assembly0Metadata.identity⟩,⟨runtimeScope⟩,⟨coreLibraryScope⟩] {}
    ⟨assembly0Metadata.identity⟩ {source with names} raw [] "System.UInt32 Examples.Throws::Percent(System.UInt32)" :=
  ⟨.cons image0_identified (.cons facadeIdentified (.cons coreIdentified .nil)),
   tables_valid, by cil_kernel_rfl, by decide +kernel,rfl,by cil_kernel_rfl, by cil_kernel_rfl,by cil_body_decodes⟩
#print axioms body_bound
end Tests.PercentRuntime.Source
