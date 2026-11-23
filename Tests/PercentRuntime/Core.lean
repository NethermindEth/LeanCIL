import Tests.CoreLibImage

/-! Method bodies, metadata and constructor signatures from the .NET 11.0.0 Windows x64
CoreLib fixture. Each body is replayed with the metadata tables reconstructed from its rows. -/

namespace Tests.PercentRuntime.Core
open CIL CIL.Extraction

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

/-- Runtime identity bound to the CoreLib metadata and signature rows. -/
private def identity := bytesOf coreLibraryScope

/-- The runtime assembly identity is justified by its table row and heaps. -/
private theorem identified :
    AssemblyIdentified Tests.CoreLibImage.assembly (bytesOf coreLibraryScope) :=
  ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms identified

namespace RangeCtor

/-- Metadata rows and heap entries used by this method. -/
def rows : MethodMetadata := {
  own := {
    assembly := Tests.CoreLibImage.assembly,
    rows := [(33554576, (fixedBytes 18 0x0120100004000000070000008802A802E505)),
      (33554577, (fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06)),
      (33554594, (fixedBytes 18 0x0120100005000000070000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF070000003003FE022507)),
      (33554673, (fixedBytes 18 0x012010000200000007000000A407B603E00C)),
      (33554674, (fixedBytes 18 0x01201000FFFFFFFF07000000C403B703EE0C)),
      (33554675, (fixedBytes 18 0x012010000300000007000000C403B703F80C)),
      (33554676, (fixedBytes 18 0x01201000FFFFFFFF07000000A407B803130D)),
      (33554911, (fixedBytes 18 0x800110000600000007000000880217066821)),
      (33554912, (fixedBytes 18 0x01211000FFFFFFFF07000000A4071D062F26)),
      (33554921, (fixedBytes 18 0x01201000080000000700000040022F067826)),
      (33554922, (fixedBytes 18 0x01011000FFFFFFFF07000000DC012F067C26)),
      (67109544, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109545, (fixedBytes 10 0x0300FFFFFFFFFFFFFFFF)),
      (67109546, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109547, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109548, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109549, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109550, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109551, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109552, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109553, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109554, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109555, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109556, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)), (67109557, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109558, (fixedBytes 10 0x5180FFFFFFFFFFFFFFFF)), (67109559, (fixedBytes 10 0x5280FFFFFFFFFFFFFFFF)),
      (67109814, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)), (67109815, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (100664849, (fixedBytes 20 0x00000000000086080A000000020000001F0D0000)),
      (100666596, (fixedBytes 20 0x0000000000008618010000000300000010190000)),
      (100666618, (fixedBytes 20 0x000000000000861801000000030000002F190000)),
      (100671882, (fixedBytes 20 0x00000000000093080900000001000000733C0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)), (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF)),
      (704643224, (fixedBytes 12 0x00002200D0010000FFFFFFFF)), (704643225, (fixedBytes 12 0x00000000EE010000FFFFFFFF)),
      (704643422, (fixedBytes 12 0x00001800B4030000FFFFFFFF)), (704643423, (fixedBytes 12 0x0000000006040000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)), (2, (fixedBytes 18 0x417267756D656E74457863657074696F6E00)),
      (3, (fixedBytes 28 0x417267756D656E744F75744F6652616E6765457863657074696F6E00)),
      (4, (fixedBytes 10 0x457863657074696F6E00)), (5, (fixedBytes 7 0x4F626A65637400)),
      (6, (fixedBytes 3 0x535200)), (7, (fixedBytes 7 0x53797374656D00)),
      (8, (fixedBytes 16 0x53797374656D457863657074696F6E00)), (9, (fixedBytes 36 0x6765745F4172675F417267756D656E744F75744F6652616E6765457863657074696F6E00)),
      (10, (fixedBytes 12 0x7365745F48526573756C7400))],
    blobs := [(1, (fixedBytes 4 0x0300000E)), (2, (fixedBytes 5 0x0420010108)),
      (3, (fixedBytes 6 0x052002010E0E))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 100664849, 0, 33554576⟩, ⟨1, 100666596, 0, 33554673⟩,
      ⟨1, 100666618, 0, 33554675⟩, ⟨1, 100671882, 0, 33554911⟩]},
  others := []}

/-- Metadata indexes reconstructed from the supplied rows. -/
private def tables : List IndexTables := rows.tables.toOption.getD []

/-- The reconstructed indexes match the carried metadata. -/
theorem tables_valid : tablesMatch rows tables = true := by decide +kernel
#print axioms tables_valid

/-- Original IL bytes and the scoped operands needed to decode them. -/
def body : BodyEvidence := {
  bytes := [118, 2, 4, 37, 45, 6, 38, 40, 138, 33, 0, 6, 3, 40,
    228, 12, 0, 6, 2, 32, 2, 21, 19, 128, 40, 17, 6, 0, 6, 42],
  tokens := {
    operands := [(100671882, .call {
          method := {
            owner := .object coreLibraryScope "System.SR",
            name := name! "get_Arg_ArgumentOutOfRangeException",
            hasThis := false,
            genericArity := 0,
            returnType := .object coreLibraryScope "System.String",
            parameters := [],
            methodArguments := []},
          name := "get_Arg_ArgumentOutOfRangeException",
          target := .managed 100671882,
          typeArguments := [],
          ownerArgumentCount := 0,
          parameterCount := 0,
          returnsValue := true,
          declared := {
            convention := 0,
            returnType := .object coreLibraryScope "System.String",
            parameters := []}}), (100666596, .call {
          method := {
            owner := .object coreLibraryScope "System.ArgumentException",
            name := name! ".ctor",
            hasThis := true,
            genericArity := 0,
            returnType := .void,
            parameters := [.object coreLibraryScope "System.String",
              .object coreLibraryScope "System.String"],
            methodArguments := []},
          name := ".ctor",
          target := .managed 100666596,
          typeArguments := [],
          ownerArgumentCount := 0,
          parameterCount := 2,
          returnsValue := false,
          declared := {
            convention := 32,
            returnType := .void,
            parameters := [.object coreLibraryScope "System.String",
              .object coreLibraryScope "System.String"]}}), (100664849, .call {
          method := {
            owner := .object coreLibraryScope "System.Exception",
            name := name! "set_HResult",
            hasThis := true,
            genericArity := 0,
            returnType := .void,
            parameters := [.atom coreLibraryScope "System.Int32"],
            methodArguments := []},
          name := "set_HResult",
          target := .managed 100664849,
          typeArguments := [],
          ownerArgumentCount := 0,
          parameterCount := 1,
          returnsValue := false,
          declared := {
            convention := 32,
            returnType := .void,
            parameters := [.atom coreLibraryScope "System.Int32"]}})]},
  metadata := rows,
  identities := [identity],
  tables,
  names := {
    },
  pinned := PinnedIndex.ofIdentities [identity]}

/-- Decode the original body in its checked metadata environment. -/
def checked := do
  let env ← body.environment.mapError BodyError.metadata
  decodeBody env 0 0 body

/-- Method declaration with instructions, stack limit and locals from the decoder. -/
def raw (decoded : DecodedBody) : RawMethod := {
  token := 100666618, owner := (coreLibraryScope ++ "::System.ArgumentOutOfRangeException"), hasThis := true, explicitThis := false,
  callingConvention := 0, attributes := 6278,
  implementation := 0, returnType := .void,
  parameters := [.object coreLibraryScope "System.String",.object coreLibraryScope "System.String"],
  locals := [], objectReceiver := true, objectBases := [.object coreLibraryScope "System.ArgumentException",.object coreLibraryScope "System.SystemException",.object coreLibraryScope "System.Exception"],
  objectFieldCount := 16, initLocals := decoded.initLocals, maxStack := decoded.maxStack,
  genericParameters := [], code := decoded.code }

/-- Encoded owner, bases and signature checked against the method declaration. -/
def names : MethodNames := {
  owner := bytesOf (coreLibraryScope ++ "::System.ArgumentOutOfRangeException"), bases := [(bytesOf coreLibraryScope,bytesOf "System.ArgumentException"),(bytesOf coreLibraryScope,bytesOf "System.SystemException"),(bytesOf coreLibraryScope,bytesOf "System.Exception")],
  signature := bytesOf "System.Void System.ArgumentOutOfRangeException::.ctor(System.String,System.String)" }

/-- The declared method with its decoded instructions. -/
def definition := raw (checked.toOption.getD {
  maxStack := 0, initLocals := false,
  localSignature := 0, code := [], statics := [] })

/-- The typed declaration and instructions are bound to the original body and metadata. -/
theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    {body with names} definition [] "System.Void System.ArgumentOutOfRangeException::.ctor(System.String,System.String)" :=
  ⟨AllIdentified.cons identified AllIdentified.nil,tables_valid, by cil_kernel_rfl,
   by decide +kernel,rfl,by cil_kernel_rfl, by cil_kernel_rfl,by cil_body_decodes⟩
#print axioms bound
end RangeCtor
namespace ArgumentCtor

/-- Metadata rows and heap entries used by this method. -/
def rows : MethodMetadata := {
  own := {
    assembly := Tests.CoreLibImage.assembly,
    rows := [(33554576, (fixedBytes 18 0x0120100003000000050000008802A802E505)),
      (33554577, (fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06)),
      (33554594, (fixedBytes 18 0x0120100004000000050000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF050000003003FE022507)),
      (33554673, (fixedBytes 18 0x012010000200000005000000A407B603E00C)),
      (33554674, (fixedBytes 18 0x01201000FFFFFFFF05000000C403B703EE0C)),
      (33554921, (fixedBytes 18 0x01201000060000000500000040022F067826)),
      (33554922, (fixedBytes 18 0x01011000FFFFFFFF05000000DC012F067C26)),
      (67109544, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109545, (fixedBytes 10 0x0300FFFFFFFF01000000)),
      (67109546, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109547, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109548, (fixedBytes 10 0x0100FFFFFFFF01000000)), (67109549, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109550, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109551, (fixedBytes 10 0x0100FFFFFFFF01000000)),
      (67109552, (fixedBytes 10 0x0100FFFFFFFF01000000)), (67109553, (fixedBytes 10 0x0100FFFFFFFF01000000)),
      (67109554, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109555, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109556, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)), (67109557, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109558, (fixedBytes 10 0x5180FFFFFFFFFFFFFFFF)), (67109559, (fixedBytes 10 0x5280FFFFFFFF01000000)),
      (67109814, (fixedBytes 10 0x21000700000001000000)), (100664849, (fixedBytes 20 0x000000000000860808000000020000001F0D0000)),
      (100666596, (fixedBytes 20 0x0000000000008618010000000400000010190000)),
      (100673145, (fixedBytes 20 0x00000000000086180100000003000000D33C0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)), (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF)),
      (704643224, (fixedBytes 12 0x00002200D0010000FFFFFFFF)), (704643225, (fixedBytes 12 0x00000000EE010000FFFFFFFF)),
      (704643422, (fixedBytes 12 0x00001800B4030000FFFFFFFF)), (704643423, (fixedBytes 12 0x0000000006040000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)), (2, (fixedBytes 18 0x417267756D656E74457863657074696F6E00)),
      (3, (fixedBytes 10 0x457863657074696F6E00)), (4, (fixedBytes 7 0x4F626A65637400)),
      (5, (fixedBytes 7 0x53797374656D00)), (6, (fixedBytes 16 0x53797374656D457863657074696F6E00)),
      (7, (fixedBytes 11 0x5F706172616D4E616D6500)), (8, (fixedBytes 12 0x7365745F48526573756C7400))],
    blobs := [(1, (fixedBytes 3 0x02060E)), (2, (fixedBytes 5 0x0420010108)),
      (3, (fixedBytes 5 0x042001010E)), (4, (fixedBytes 6 0x052002010E0E))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 67109814, 0, 33554673⟩, ⟨1, 100664849, 0, 33554576⟩,
      ⟨1, 100666596, 0, 33554673⟩, ⟨1, 100673145, 0, 33554921⟩]},
  others := []}

/-- Metadata indexes reconstructed from the supplied rows. -/
private def tables : List IndexTables := rows.tables.toOption.getD []

/-- The reconstructed indexes match the carried metadata. -/
theorem tables_valid : tablesMatch rows tables = true := by decide +kernel
#print axioms tables_valid

/-- Original IL bytes and the scoped operands needed to decode them. -/
def body : BodyEvidence := {
  bytes := [106, 2, 3, 40, 121, 38, 0, 6, 2, 4, 125, 182, 3, 0,
    4, 2, 32, 87, 0, 7, 128, 40, 17, 6, 0, 6, 42],
  tokens := {
    operands := [(100673145, .call {
          method := {
            owner := .object coreLibraryScope "System.SystemException",
            name := name! ".ctor",
            hasThis := true,
            genericArity := 0,
            returnType := .void,
            parameters := [.object coreLibraryScope "System.String"],
            methodArguments := []},
          name := ".ctor",
          target := .managed 100673145,
          typeArguments := [],
          ownerArgumentCount := 0,
          parameterCount := 1,
          returnsValue := false,
          declared := {
            convention := 32,
            returnType := .void,
            parameters := [.object coreLibraryScope "System.String"]}}),
      (67109814, .field (.object coreLibraryScope "System.ArgumentException") 14 (.object coreLibraryScope "System.String") name! "_paramName" false),
      (100664849, .call {
          method := {
            owner := .object coreLibraryScope "System.Exception",
            name := name! "set_HResult",
            hasThis := true,
            genericArity := 0,
            returnType := .void,
            parameters := [.atom coreLibraryScope "System.Int32"],
            methodArguments := []},
          name := "set_HResult",
          target := .managed 100664849,
          typeArguments := [],
          ownerArgumentCount := 0,
          parameterCount := 1,
          returnsValue := false,
          declared := {
            convention := 32,
            returnType := .void,
            parameters := [.atom coreLibraryScope "System.Int32"]}})]},
  metadata := rows,
  identities := [identity],
  tables,
  names := {
    },
  pinned := PinnedIndex.ofIdentities [identity]}

/-- Decode the original body in its checked metadata environment. -/
def checked := do
  let env ← body.environment.mapError BodyError.metadata
  decodeBody env 0 0 body

/-- Method declaration with instructions, stack limit and locals from the decoder. -/
def raw (decoded : DecodedBody) : RawMethod := {
  token := 100666596, owner := (coreLibraryScope ++ "::System.ArgumentException"), hasThis := true, explicitThis := false,
  callingConvention := 0, attributes := 6278,
  implementation := 0, returnType := .void,
  parameters := [.object coreLibraryScope "System.String",.object coreLibraryScope "System.String"],
  locals := [], objectReceiver := true, objectBases := [.object coreLibraryScope "System.SystemException",.object coreLibraryScope "System.Exception"],
  objectFieldCount := 15, initLocals := decoded.initLocals, maxStack := decoded.maxStack,
  genericParameters := [], code := decoded.code }

/-- Encoded owner, bases and signature checked against the method declaration. -/
def names : MethodNames := {
  owner := bytesOf (coreLibraryScope ++ "::System.ArgumentException"), bases := [(bytesOf coreLibraryScope,bytesOf "System.SystemException"),(bytesOf coreLibraryScope,bytesOf "System.Exception")],
  signature := bytesOf "System.Void System.ArgumentException::.ctor(System.String,System.String)" }

/-- The declared method with its decoded instructions. -/
def definition := raw (checked.toOption.getD {
  maxStack := 0, initLocals := false,
  localSignature := 0, code := [], statics := [] })

/-- The typed declaration and instructions are bound to the original body and metadata. -/
theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    {body with names} definition [] "System.Void System.ArgumentException::.ctor(System.String,System.String)" :=
  ⟨AllIdentified.cons identified AllIdentified.nil,tables_valid, by cil_kernel_rfl,
   by decide +kernel,rfl,by cil_kernel_rfl, by cil_kernel_rfl,by cil_body_decodes⟩
#print axioms bound
end ArgumentCtor
namespace SystemExceptionCtor

/-- Metadata rows and heap entries used by this method. -/
def rows : MethodMetadata := {
  own := {
    assembly := Tests.CoreLibImage.assembly,
    rows := [(33554576, (fixedBytes 18 0x0120100002000000040000008802A802E505)),
      (33554577, (fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06)),
      (33554594, (fixedBytes 18 0x0120100003000000040000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF040000003003FE022507)),
      (33554921, (fixedBytes 18 0x01201000050000000400000040022F067826)),
      (33554922, (fixedBytes 18 0x01011000FFFFFFFF04000000DC012F067C26)),
      (67109544, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109545, (fixedBytes 10 0x0300FFFFFFFFFFFFFFFF)),
      (67109546, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109547, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109548, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109549, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109550, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109551, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109552, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109553, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109554, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109555, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109556, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)), (67109557, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109558, (fixedBytes 10 0x5180FFFFFFFFFFFFFFFF)), (67109559, (fixedBytes 10 0x5280FFFFFFFFFFFFFFFF)),
      (100664832, (fixedBytes 20 0x00000000000086180100000002000000140D0000)),
      (100664849, (fixedBytes 20 0x000000000000860806000000010000001F0D0000)),
      (100673145, (fixedBytes 20 0x00000000000086180100000002000000D33C0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)), (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF)),
      (704643422, (fixedBytes 12 0x00001800B4030000FFFFFFFF)), (704643423, (fixedBytes 12 0x0000000006040000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)), (2, (fixedBytes 10 0x457863657074696F6E00)),
      (3, (fixedBytes 7 0x4F626A65637400)), (4, (fixedBytes 7 0x53797374656D00)),
      (5, (fixedBytes 16 0x53797374656D457863657074696F6E00)), (6, (fixedBytes 12 0x7365745F48526573756C7400))],
    blobs := [(1, (fixedBytes 5 0x0420010108)), (2, (fixedBytes 5 0x042001010E))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 100664832, 0, 33554576⟩, ⟨1, 100664849, 0, 33554576⟩,
      ⟨1, 100673145, 0, 33554921⟩]},
  others := []}

/-- Metadata indexes reconstructed from the supplied rows. -/
private def tables : List IndexTables := rows.tables.toOption.getD []

/-- The reconstructed indexes match the carried metadata. -/
theorem tables_valid : tablesMatch rows tables = true := by decide +kernel
#print axioms tables_valid

/-- Original IL bytes and the scoped operands needed to decode them. -/
def body : BodyEvidence := {
  bytes := [78, 2, 3, 40, 0, 6, 0, 6, 2, 32, 1, 21, 19, 128, 40,
    17, 6, 0, 6, 42],
  tokens := {
    operands := [(100664832, .call {
          method := {
            owner := .object coreLibraryScope "System.Exception",
            name := name! ".ctor",
            hasThis := true,
            genericArity := 0,
            returnType := .void,
            parameters := [.object coreLibraryScope "System.String"],
            methodArguments := []},
          name := ".ctor",
          target := .managed 100664832,
          typeArguments := [],
          ownerArgumentCount := 0,
          parameterCount := 1,
          returnsValue := false,
          declared := {
            convention := 32,
            returnType := .void,
            parameters := [.object coreLibraryScope "System.String"]}}),
      (100664849, .call {
          method := {
            owner := .object coreLibraryScope "System.Exception",
            name := name! "set_HResult",
            hasThis := true,
            genericArity := 0,
            returnType := .void,
            parameters := [.atom coreLibraryScope "System.Int32"],
            methodArguments := []},
          name := "set_HResult",
          target := .managed 100664849,
          typeArguments := [],
          ownerArgumentCount := 0,
          parameterCount := 1,
          returnsValue := false,
          declared := {
            convention := 32,
            returnType := .void,
            parameters := [.atom coreLibraryScope "System.Int32"]}})]},
  metadata := rows,
  identities := [identity],
  tables,
  names := {
    },
  pinned := PinnedIndex.ofIdentities [identity]}

/-- Decode the original body in its checked metadata environment. -/
def checked := do
  let env ← body.environment.mapError BodyError.metadata
  decodeBody env 0 0 body

/-- Method declaration with instructions, stack limit and locals from the decoder. -/
def raw (decoded : DecodedBody) : RawMethod := {
  token := 100673145, owner := (coreLibraryScope ++ "::System.SystemException"), hasThis := true, explicitThis := false,
  callingConvention := 0, attributes := 6278,
  implementation := 0, returnType := .void,
  parameters := [.object coreLibraryScope "System.String"],
  locals := [], objectReceiver := true, objectBases := [.object coreLibraryScope "System.Exception"],
  objectFieldCount := 14, initLocals := decoded.initLocals, maxStack := decoded.maxStack,
  genericParameters := [], code := decoded.code }

/-- Encoded owner, bases and signature checked against the method declaration. -/
def names : MethodNames := {
  owner := bytesOf (coreLibraryScope ++ "::System.SystemException"), bases := [(bytesOf coreLibraryScope,bytesOf "System.Exception")],
  signature := bytesOf "System.Void System.SystemException::.ctor(System.String)" }

/-- The declared method with its decoded instructions. -/
def definition := raw (checked.toOption.getD {
  maxStack := 0, initLocals := false,
  localSignature := 0, code := [], statics := [] })

/-- The typed declaration and instructions are bound to the original body and metadata. -/
theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    {body with names} definition [] "System.Void System.SystemException::.ctor(System.String)" :=
  ⟨AllIdentified.cons identified AllIdentified.nil,tables_valid, by cil_kernel_rfl,
   by decide +kernel,rfl,by cil_kernel_rfl, by cil_kernel_rfl,by cil_body_decodes⟩
#print axioms bound
end SystemExceptionCtor
namespace ExceptionMessageCtor

/-- Metadata rows and heap entries used by this method. -/
def rows : MethodMetadata := {
  own := {
    assembly := Tests.CoreLibImage.assembly,
    rows := [(33554576, (fixedBytes 18 0x0120100002000000040000008802A802E505)),
      (33554577, (fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06)),
      (33554594, (fixedBytes 18 0x0120100003000000040000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF040000003003FE022507)),
      (67109544, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109545, (fixedBytes 10 0x03000500000001000000)),
      (67109546, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109547, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109548, (fixedBytes 10 0x0100FFFFFFFF01000000)), (67109549, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109550, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109551, (fixedBytes 10 0x0100FFFFFFFF01000000)),
      (67109552, (fixedBytes 10 0x0100FFFFFFFF01000000)), (67109553, (fixedBytes 10 0x0100FFFFFFFF01000000)),
      (67109554, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109555, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109556, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)), (67109557, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109558, (fixedBytes 10 0x5180FFFFFFFFFFFFFFFF)), (67109559, (fixedBytes 10 0x5280FFFFFFFF01000000)),
      (100664831, (fixedBytes 20 0x00000000000086180100000002000000140D0000)),
      (100664832, (fixedBytes 20 0x00000000000086180100000003000000140D0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)), (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)), (2, (fixedBytes 10 0x457863657074696F6E00)),
      (3, (fixedBytes 7 0x4F626A65637400)), (4, (fixedBytes 7 0x53797374656D00)),
      (5, (fixedBytes 9 0x5F6D65737361676500))],
    blobs := [(1, (fixedBytes 3 0x02060E)), (2, (fixedBytes 4 0x03200001)),
      (3, (fixedBytes 5 0x042001010E))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 67109545, 0, 33554576⟩, ⟨1, 100664831, 0, 33554576⟩,
      ⟨1, 100664832, 0, 33554576⟩]},
  others := []}

/-- Metadata indexes reconstructed from the supplied rows. -/
private def tables : List IndexTables := rows.tables.toOption.getD []

/-- The reconstructed indexes match the carried metadata. -/
theorem tables_valid : tablesMatch rows tables = true := by decide +kernel
#print axioms tables_valid

/-- Original IL bytes and the scoped operands needed to decode them. -/
def body : BodyEvidence := {
  bytes := [58, 2, 40, 255, 5, 0, 6, 2, 3, 125, 169, 2, 0, 4, 42],
  tokens := {
    operands := [(100664831, .call {
          method := {
            owner := .object coreLibraryScope "System.Exception",
            name := name! ".ctor",
            hasThis := true,
            genericArity := 0,
            returnType := .void,
            parameters := [],
            methodArguments := []},
          name := ".ctor",
          target := .managed 100664831,
          typeArguments := [],
          ownerArgumentCount := 0,
          parameterCount := 0,
          returnsValue := false,
          declared := {
            convention := 32,
            returnType := .void,
            parameters := []}}), (67109545, .field (.object coreLibraryScope "System.Exception") 1 (.object coreLibraryScope "System.String") name! "_message" false)]},
  metadata := rows,
  identities := [identity],
  tables,
  names := {
    },
  pinned := PinnedIndex.ofIdentities [identity]}

/-- Decode the original body in its checked metadata environment. -/
def checked := do
  let env ← body.environment.mapError BodyError.metadata
  decodeBody env 0 0 body

/-- Method declaration with instructions, stack limit and locals from the decoder. -/
def raw (decoded : DecodedBody) : RawMethod := {
  token := 100664832, owner := (coreLibraryScope ++ "::System.Exception"), hasThis := true, explicitThis := false,
  callingConvention := 0, attributes := 6278,
  implementation := 0, returnType := .void,
  parameters := [.object coreLibraryScope "System.String"],
  locals := [], objectReceiver := true, objectBases := [],
  objectFieldCount := 14, initLocals := decoded.initLocals, maxStack := decoded.maxStack,
  genericParameters := [], code := decoded.code }

/-- Encoded owner, bases and signature checked against the method declaration. -/
def names : MethodNames := {
  owner := bytesOf (coreLibraryScope ++ "::System.Exception"), bases := [],
  signature := bytesOf "System.Void System.Exception::.ctor(System.String)" }

/-- The declared method with its decoded instructions. -/
def definition := raw (checked.toOption.getD {
  maxStack := 0, initLocals := false,
  localSignature := 0, code := [], statics := [] })

/-- The typed declaration and instructions are bound to the original body and metadata. -/
theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    {body with names} definition [] "System.Void System.Exception::.ctor(System.String)" :=
  ⟨AllIdentified.cons identified AllIdentified.nil,tables_valid, by cil_kernel_rfl,
   by decide +kernel,rfl,by cil_kernel_rfl, by cil_kernel_rfl,by cil_body_decodes⟩
#print axioms bound
end ExceptionMessageCtor
namespace ExceptionCtor

/-- Metadata rows and heap entries used by this method. -/
def rows : MethodMetadata := {
  own := {
    assembly := Tests.CoreLibImage.assembly,
    rows := [(33554576, (fixedBytes 18 0x0120100002000000040000008802A802E505)),
      (33554577, (fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06)),
      (33554594, (fixedBytes 18 0x0120100003000000040000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF040000003003FE022507)),
      (67109544, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109545, (fixedBytes 10 0x0300FFFFFFFFFFFFFFFF)),
      (67109546, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109547, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109548, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109549, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109550, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109551, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109552, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109553, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109554, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109555, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109556, (fixedBytes 10 0x21000600000001000000)), (67109557, (fixedBytes 10 0x01000500000001000000)),
      (67109558, (fixedBytes 10 0x5180FFFFFFFF01000000)), (67109559, (fixedBytes 10 0x5280FFFFFFFFFFFFFFFF)),
      (100664831, (fixedBytes 20 0x00000000000086180100000002000000140D0000)),
      (100665118, (fixedBytes 20 0x00000000000086180100000002000000C20E0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)), (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)), (2, (fixedBytes 10 0x457863657074696F6E00)),
      (3, (fixedBytes 7 0x4F626A65637400)), (4, (fixedBytes 7 0x53797374656D00)),
      (5, (fixedBytes 9 0x5F48526573756C7400)), (6, (fixedBytes 7 0x5F78636F646500))],
    blobs := [(1, (fixedBytes 3 0x020608)), (2, (fixedBytes 4 0x03200001))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 67109556, 0, 33554576⟩, ⟨1, 67109557, 0, 33554576⟩,
      ⟨1, 100664831, 0, 33554576⟩, ⟨1, 100665118, 0, 33554594⟩]},
  others := []}

/-- Metadata indexes reconstructed from the supplied rows. -/
private def tables : List IndexTables := rows.tables.toOption.getD []

/-- The reconstructed indexes match the carried metadata. -/
theorem tables_valid : tablesMatch rows tables = true := by decide +kernel
#print axioms tables_valid

/-- Original IL bytes and the scoped operands needed to decode them. -/
def body : BodyEvidence := {
  bytes := [118, 2, 32, 82, 67, 67, 224, 125, 180, 2, 0, 4, 2, 40,
    30, 7, 0, 6, 2, 32, 0, 21, 19, 128, 125, 181, 2, 0, 4, 42],
  tokens := {
    operands := [(67109556, .field (.object coreLibraryScope "System.Exception") 12 (.atom coreLibraryScope "System.Int32") name! "_xcode" false),
      (100665118, .call {
          method := {
            owner := .object coreLibraryScope "System.Object",
            name := name! ".ctor",
            hasThis := true,
            genericArity := 0,
            returnType := .void,
            parameters := [],
            methodArguments := []},
          name := ".ctor",
          target := .managed 100665118,
          typeArguments := [],
          ownerArgumentCount := 0,
          parameterCount := 0,
          returnsValue := false,
          declared := {
            convention := 32,
            returnType := .void,
            parameters := []}}), (67109557, .field (.object coreLibraryScope "System.Exception") 13 (.atom coreLibraryScope "System.Int32") name! "_HResult" false)]},
  metadata := rows,
  identities := [identity],
  tables,
  names := {
    },
  pinned := PinnedIndex.ofIdentities [identity]}

/-- Decode the original body in its checked metadata environment. -/
def checked := do
  let env ← body.environment.mapError BodyError.metadata
  decodeBody env 0 0 body

/-- Method declaration with instructions, stack limit and locals from the decoder. -/
def raw (decoded : DecodedBody) : RawMethod := {
  token := 100664831, owner := (coreLibraryScope ++ "::System.Exception"), hasThis := true, explicitThis := false,
  callingConvention := 0, attributes := 6278,
  implementation := 0, returnType := .void,
  parameters := [],
  locals := [], objectReceiver := true, objectBases := [],
  objectFieldCount := 14, initLocals := decoded.initLocals, maxStack := decoded.maxStack,
  genericParameters := [], code := decoded.code }

/-- Encoded owner, bases and signature checked against the method declaration. -/
def names : MethodNames := {
  owner := bytesOf (coreLibraryScope ++ "::System.Exception"), bases := [],
  signature := bytesOf "System.Void System.Exception::.ctor()" }

/-- The declared method with its decoded instructions. -/
def definition := raw (checked.toOption.getD {
  maxStack := 0, initLocals := false,
  localSignature := 0, code := [], statics := [] })

/-- The typed declaration and instructions are bound to the original body and metadata. -/
theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    {body with names} definition [] "System.Void System.Exception::.ctor()" :=
  ⟨AllIdentified.cons identified AllIdentified.nil,tables_valid, by cil_kernel_rfl,
   by decide +kernel,rfl,by cil_kernel_rfl, by cil_kernel_rfl,by cil_body_decodes⟩
#print axioms bound
end ExceptionCtor
namespace ObjectCtor

/-- Metadata rows and heap entries used by this method. -/
def rows : MethodMetadata := {
  own := {
    assembly := Tests.CoreLibImage.assembly,
    rows := [(33554594, (fixedBytes 18 0x0120100002000000030000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF030000003003FE022507)),
      (100665118, (fixedBytes 20 0x00000000000086180100000001000000C20E0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)), (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)), (2, (fixedBytes 7 0x4F626A65637400)),
      (3, (fixedBytes 7 0x53797374656D00))],
    blobs := [(1, (fixedBytes 4 0x03200001))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 100665118, 0, 33554594⟩]},
  others := []}

/-- Metadata indexes reconstructed from the supplied rows. -/
private def tables : List IndexTables := rows.tables.toOption.getD []

/-- The reconstructed indexes match the carried metadata. -/
theorem tables_valid : tablesMatch rows tables = true := by decide +kernel
#print axioms tables_valid

/-- Original IL bytes and the scoped operands needed to decode them. -/
def body : BodyEvidence := {
  bytes := [6, 42],
  tokens := {
    operands := []},
  metadata := rows,
  identities := [identity],
  tables,
  names := {
    },
  pinned := PinnedIndex.ofIdentities [identity]}

/-- Decode the original body in its checked metadata environment. -/
def checked := do
  let env ← body.environment.mapError BodyError.metadata
  decodeBody env 0 0 body

/-- Method declaration with instructions, stack limit and locals from the decoder. -/
def raw (decoded : DecodedBody) : RawMethod := {
  token := 100665118, owner := (coreLibraryScope ++ "::System.Object"), hasThis := true, explicitThis := false,
  callingConvention := 0, attributes := 6278,
  implementation := 0, returnType := .void,
  parameters := [],
  locals := [], objectReceiver := true, objectBases := [],
  objectFieldCount := 0, initLocals := decoded.initLocals, maxStack := decoded.maxStack,
  genericParameters := [], code := decoded.code }

/-- Encoded owner, bases and signature checked against the method declaration. -/
def names : MethodNames := {
  owner := bytesOf (coreLibraryScope ++ "::System.Object"), bases := [],
  signature := bytesOf "System.Void System.Object::.ctor()" }

/-- The declared method with its decoded instructions. -/
def definition := raw (checked.toOption.getD {
  maxStack := 0, initLocals := false,
  localSignature := 0, code := [], statics := [] })

/-- The typed declaration and instructions are bound to the original body and metadata. -/
theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    {body with names} definition [] "System.Void System.Object::.ctor()" :=
  ⟨AllIdentified.cons identified AllIdentified.nil,tables_valid, by cil_kernel_rfl,
   by decide +kernel,rfl,by cil_kernel_rfl, by cil_kernel_rfl,by cil_body_decodes⟩
#print axioms bound
end ObjectCtor
namespace SetHResult

/-- Metadata rows and heap entries used by this method. -/
def rows : MethodMetadata := {
  own := {
    assembly := Tests.CoreLibImage.assembly,
    rows := [(33554576, (fixedBytes 18 0x0120100001000000030000008802A802E505)),
      (33554577, (fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06)),
      (33554594, (fixedBytes 18 0x0120100002000000030000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF030000003003FE022507)),
      (67109544, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109545, (fixedBytes 10 0x0300FFFFFFFFFFFFFFFF)),
      (67109546, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109547, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109548, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109549, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109550, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109551, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109552, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109553, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109554, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)), (67109555, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109556, (fixedBytes 10 0x2100FFFFFFFF01000000)), (67109557, (fixedBytes 10 0x01000400000001000000)),
      (67109558, (fixedBytes 10 0x5180FFFFFFFF01000000)), (67109559, (fixedBytes 10 0x5280FFFFFFFFFFFFFFFF)),
      (100664849, (fixedBytes 20 0x000000000000860805000000020000001F0D0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)), (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF))],
    strings := [(1, (fixedBytes 10 0x457863657074696F6E00)), (2, (fixedBytes 7 0x4F626A65637400)),
      (3, (fixedBytes 7 0x53797374656D00)), (4, (fixedBytes 9 0x5F48526573756C7400)),
      (5, (fixedBytes 12 0x7365745F48526573756C7400))],
    blobs := [(1, (fixedBytes 3 0x020608)), (2, (fixedBytes 5 0x0420010108))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 67109557, 0, 33554576⟩, ⟨1, 100664849, 0, 33554576⟩]},
  others := []}

/-- Metadata indexes reconstructed from the supplied rows. -/
private def tables : List IndexTables := rows.tables.toOption.getD []

/-- The reconstructed indexes match the carried metadata. -/
theorem tables_valid : tablesMatch rows tables = true := by decide +kernel
#print axioms tables_valid

/-- Original IL bytes and the scoped operands needed to decode them. -/
def body : BodyEvidence := {
  bytes := [34, 2, 3, 125, 181, 2, 0, 4, 42],
  tokens := {
    operands := [(67109557, .field (.object coreLibraryScope "System.Exception") 13 (.atom coreLibraryScope "System.Int32") name! "_HResult" false)]},
  metadata := rows,
  identities := [identity],
  tables,
  names := {
    },
  pinned := PinnedIndex.ofIdentities [identity]}

/-- Decode the original body in its checked metadata environment. -/
def checked := do
  let env ← body.environment.mapError BodyError.metadata
  decodeBody env 0 0 body

/-- Method declaration with instructions, stack limit and locals from the decoder. -/
def raw (decoded : DecodedBody) : RawMethod := {
  token := 100664849, owner := (coreLibraryScope ++ "::System.Exception"), hasThis := true, explicitThis := false,
  callingConvention := 0, attributes := 2182,
  implementation := 0, returnType := .void,
  parameters := [.atom coreLibraryScope "System.Int32"],
  locals := [], objectReceiver := true, objectBases := [],
  objectFieldCount := 14, initLocals := decoded.initLocals, maxStack := decoded.maxStack,
  genericParameters := [], code := decoded.code }

/-- Encoded owner, bases and signature checked against the method declaration. -/
def names : MethodNames := {
  owner := bytesOf (coreLibraryScope ++ "::System.Exception"), bases := [],
  signature := bytesOf "System.Void System.Exception::set_HResult(System.Int32)" }

/-- The declared method with its decoded instructions. -/
def definition := raw (checked.toOption.getD {
  maxStack := 0, initLocals := false,
  localSignature := 0, code := [], statics := [] })

/-- The typed declaration and instructions are bound to the original body and metadata. -/
theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    {body with names} definition [] "System.Void System.Exception::set_HResult(System.Int32)" :=
  ⟨AllIdentified.cons identified AllIdentified.nil,tables_valid, by cil_kernel_rfl,
   by decide +kernel,rfl,by cil_kernel_rfl, by cil_kernel_rfl,by cil_body_decodes⟩
#print axioms bound
end SetHResult

/-- The CoreLib resource lookup called from the null-message path. -/
def lookup : MethodRef := {
  owner := .object coreLibraryScope "System.SR", name := name!"GetResourceString",
  hasThis := false, genericArity := 0, returnType := .object coreLibraryScope "System.String",
  parameters := [.object coreLibraryScope "System.String"] }
namespace RangeResource

/-- Metadata rows and heap entries used by this method. -/
def rows : MethodMetadata := {
  own := {
    assembly := Tests.CoreLibImage.assembly,
    rows := [(33554594, (fixedBytes 18 0x0120100002000000040000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF040000003003FE022507)),
      (33554911, (fixedBytes 18 0x800110000300000004000000880217066821)),
      (33554912, (fixedBytes 18 0x01211000FFFFFFFF04000000A4071D062F26)),
      (67110423, (fixedBytes 10 0x3100FFFFFFFFFFFFFFFF)), (67110424, (fixedBytes 10 0x1100FFFFFFFFFFFFFFFF)),
      (67110425, (fixedBytes 10 0x1100FFFFFFFFFFFFFFFF)), (67110426, (fixedBytes 10 0x1100FFFFFFFFFFFFFFFF)),
      (67110427, (fixedBytes 10 0x3100FFFFFFFFFFFFFFFF)), (67110428, (fixedBytes 10 0x1100FFFFFFFFFFFFFFFF)),
      (100671851, (fixedBytes 20 0x00000000000093000100000002000000603C0000)),
      (100671882, (fixedBytes 20 0x00000000000093080500000001000000733C0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)), (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF)),
      (704643422, (fixedBytes 12 0x00001800B4030000FFFFFFFF)), (704643423, (fixedBytes 12 0x0000000006040000FFFFFFFF))],
    strings := [(1, (fixedBytes 18 0x4765745265736F75726365537472696E6700)),
      (2, (fixedBytes 7 0x4F626A65637400)), (3, (fixedBytes 3 0x535200)),
      (4, (fixedBytes 7 0x53797374656D00)), (5, (fixedBytes 36 0x6765745F4172675F417267756D656E744F75744F6652616E6765457863657074696F6E00))],
    blobs := [(1, (fixedBytes 4 0x0300000E)), (2, (fixedBytes 5 0x0400010E0E))],
    userStrings := [(11466, (fixedBytes 64 0x3F4100720067005F0041007200670075006D0065006E0074004F00750074004F006600520061006E006700650045007800630065007000740069006F006E0000))],
    corlib := 0,
    links := [⟨1, 100671851, 0, 33554911⟩, ⟨1, 100671882, 0, 33554911⟩]},
  others := []}

/-- Metadata indexes reconstructed from the supplied rows. -/
private def tables : List IndexTables := rows.tables.toOption.getD []

/-- The reconstructed indexes match the carried metadata. -/
theorem tables_valid : tablesMatch rows tables = true := by decide +kernel
#print axioms tables_valid

/-- Original IL bytes and the scoped operands needed to decode them. -/
def body : BodyEvidence := {
  bytes := [46, 114, 202, 44, 0, 112, 40, 107, 33, 0, 6, 42],
  tokens := {
    operands := [(1879059658, .text "Arg_ArgumentOutOfRangeException"),
      (100671851, .call {
          method := lookup,
          name := "GetResourceString",
          declared := lookup.signature 0,
          target := .managed 100671851,
          typeArguments := [],
          parameterCount := 1,
          returnsValue := true})]},
  metadata := rows,
  identities := [identity],
  tables,
  names := {
    },
  pinned := PinnedIndex.ofIdentities [identity]}

/-- Decode the original body in its checked metadata environment. -/
def checked := do
  let env ← body.environment.mapError BodyError.metadata
  decodeBody env 0 0 body

/-- Method declaration with instructions, stack limit and locals from the decoder. -/
def raw : RawMethod :=
  let decoded := checked.toOption.getD { maxStack := 0, initLocals := false, localSignature := 0, code := [], statics := [] }
  { token := 100671882, owner := (coreLibraryScope ++ "::System.SR"), hasThis := false, explicitThis := false,
    callingConvention := 0, attributes := 2195,
    implementation := 0,
    returnType := .object coreLibraryScope "System.String", parameters := [], locals := [],
    initLocals := decoded.initLocals, maxStack := decoded.maxStack, genericParameters := [], code := decoded.code }

/-- Encoded owner, bases and signature checked against the method declaration. -/
def names : MethodNames := {
  owner := bytesOf (coreLibraryScope ++ "::System.SR"), signature := bytesOf "System.String System.SR::get_Arg_ArgumentOutOfRangeException()" }

/-- The typed declaration and instructions are bound to the original body and metadata. -/
theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    {body with names} raw [] "System.String System.SR::get_Arg_ArgumentOutOfRangeException()" :=
  ⟨.cons identified .nil, tables_valid, by cil_kernel_rfl, by decide +kernel,rfl,by cil_kernel_rfl,
   by cil_kernel_rfl, by cil_body_decodes⟩
#print axioms bound
end RangeResource

end Tests.PercentRuntime.Core
