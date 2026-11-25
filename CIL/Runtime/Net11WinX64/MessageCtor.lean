import CIL.Runtime.Net11WinX64.InnerMethods

/-! The physical InvalidOperationException constructor that takes only a message. A null
message reads the default text from a resource getter; a non-null message passes straight to the
SystemException constructor. -/

namespace CIL.Runtime.Net11WinX64.Core.InvalidOperationMessageCtor
open CIL CIL.Extraction
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- Compact metadata for the physical definition and its scoped operands. -/
def rows : MethodMetadata := {
  own := {
    assembly := CoreLib.assembly,
    rows := [(33554576, (fixedBytes 18 0x0120100002000000060000008802A802E505)),
      (33554577, (fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06)),
      (33554594, (fixedBytes 18 0x0120100004000000060000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF060000003003FE022507)),
      (33554816, (fixedBytes 18 0x012010000300000006000000A4078205631B)),
      (33554817, (fixedBytes 18 0x01211000FFFFFFFF06000000A4078205671B)),
      (33554911, (fixedBytes 18 0x800110000500000006000000880217066821)),
      (33554912, (fixedBytes 18 0x01211000FFFFFFFF06000000A4071D062F26)),
      (33554921, (fixedBytes 18 0x01201000070000000600000040022F067826)),
      (33554922, (fixedBytes 18 0x01011000FFFFFFFF06000000DC012F067C26)),
      (67109544, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109545, (fixedBytes 10 0x0300FFFFFFFFFFFFFFFF)),
      (67109546, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109547, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109548, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109549, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109550, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109551, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109552, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109553, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109554, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109555, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109556, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109557, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109558, (fixedBytes 10 0x5180FFFFFFFFFFFFFFFF)),
      (67109559, (fixedBytes 10 0x5280FFFFFFFFFFFFFFFF)),
      (100664849, (fixedBytes 20 0x000000000000860809000000020000001F0D0000)),
      (100670308, (fixedBytes 20 0x00000000000086180100000003000000DE310000)),
      (100671961, (fixedBytes 20 0x00000000000093080800000001000000733C0000)),
      (100673145, (fixedBytes 20 0x00000000000086180100000003000000D33C0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)),
      (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF)),
      (704643390, (fixedBytes 12 0x00001800E6020000FFFFFFFF)),
      (704643391, (fixedBytes 12 0x0000010006030000FFFFFFFF)),
      (704643422, (fixedBytes 12 0x00001800B4030000FFFFFFFF)),
      (704643423, (fixedBytes 12 0x0000000006040000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)),
      (2, (fixedBytes 10 0x457863657074696F6E00)),
      (3, (fixedBytes 26 0x496E76616C69644F7065726174696F6E457863657074696F6E00)),
      (4, (fixedBytes 7 0x4F626A65637400)),
      (5, (fixedBytes 3 0x535200)),
      (6, (fixedBytes 7 0x53797374656D00)),
      (7, (fixedBytes 16 0x53797374656D457863657074696F6E00)),
      (8, (fixedBytes 34 0x6765745F4172675F496E76616C69644F7065726174696F6E457863657074696F6E00)),
      (9, (fixedBytes 12 0x7365745F48526573756C7400))],
    blobs := [(1, (fixedBytes 4 0x0300000E)),
      (2, (fixedBytes 5 0x0420010108)),
      (3, (fixedBytes 5 0x042001010E))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 100664849, 0, 33554576⟩,
      ⟨1, 100670308, 0, 33554816⟩,
      ⟨1, 100671961, 0, 33554911⟩,
      ⟨1, 100673145, 0, 33554921⟩] },
  others := [] }

/-- Constructor body bytes and member operands. The getter supplies the default message. -/
def body : BodyEvidence := {
  InvalidOperationInnerCtor.body with
  bytes := (fixedBytes 29 0x720203252D062628D9210006287926000602200915138028110600062A)
  tokens := { operands := [
    (100671961, .call {
      method := {
        owner := .object coreLibraryScope "System.SR",
        name := name!"get_Arg_InvalidOperationException", hasThis := false,
        genericArity := 0,
        returnType := .object coreLibraryScope "System.String",
        parameters := [],
        methodArguments := [] },
        name := "get_Arg_InvalidOperationException",
      target := .managed 100671961, typeArguments := [],
      ownerArgumentCount := 0, parameterCount := 0, returnsValue := true,
      declared := {
        convention := 0,
        returnType := .object coreLibraryScope "System.String",
        parameters := [] } }),
    (100673145, .call {
      method := {
        owner := .object coreLibraryScope "System.SystemException",
        name := name!".ctor", hasThis := true,
        genericArity := 0,
        returnType := .void,
        parameters := [.object coreLibraryScope "System.String"],
        methodArguments := [] },
        name := ".ctor",
      target := .managed 100673145, typeArguments := [],
      ownerArgumentCount := 0, parameterCount := 1, returnsValue := false,
      declared := {
        convention := 32,
        returnType := .void,
        parameters := [.object coreLibraryScope "System.String"] } }),
    (100664849, .call {
      method := {
        owner := .object coreLibraryScope "System.Exception",
        name := name!"set_HResult", hasThis := true,
        genericArity := 0,
        returnType := .void,
        parameters := [.atom coreLibraryScope "System.Int32"],
        methodArguments := [] },
        name := "set_HResult",
      target := .managed 100664849, typeArguments := [],
      ownerArgumentCount := 0, parameterCount := 1, returnsValue := false,
      declared := {
        convention := 32,
        returnType := .void,
        parameters := [.atom coreLibraryScope "System.Int32"] } })] }
  metadata := rows
  tables := rows.tables.toOption.getD [] }

/-- Physical definition decoded with its own metadata. -/
def definition : RawMethod :=
  let decoded := (do
    let env ← body.environment.mapError BodyError.metadata
    decodeBody env 0 0 body).toOption.getD {
      maxStack := 0, initLocals := false, localSignature := 0, code := [], statics := [] }
  { InvalidOperationInnerCtor.definition with
    token := 100670308, parameters := [.object coreLibraryScope "System.String"],
    initLocals := decoded.initLocals, maxStack := decoded.maxStack, code := decoded.code }

/-- Raw owner, base classes and constructor signature. -/
def names : MethodNames := {
  InvalidOperationInnerCtor.names with
  signature := bytesOf "System.Void System.InvalidOperationException::.ctor(System.String)" }

/-- The checked body and signature resolve to this MethodDef. -/
theorem bound : BodyDecodes [⟨coreLibraryAssembly⟩] {} ⟨coreLibraryAssembly⟩
    { body with names } definition []
      "System.Void System.InvalidOperationException::.ctor(System.String)" :=
  ⟨.cons ⟨by cil_kernel_rfl, by cil_kernel_rfl⟩ .nil, by decide +kernel,
    by cil_kernel_rfl, by decide +kernel, rfl, by cil_kernel_rfl, by cil_kernel_rfl,
    by cil_body_decodes⟩
#print axioms bound

end CIL.Runtime.Net11WinX64.Core.InvalidOperationMessageCtor
