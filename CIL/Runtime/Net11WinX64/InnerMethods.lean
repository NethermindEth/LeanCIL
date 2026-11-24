import CIL.Runtime.Net11WinX64.RangeMethods

/-! Physical constructor bodies shared by the exception overloads that carry an inner exception,
including the InvalidOperationException overload whose null-message branch calls a resource
getter. -/

namespace CIL.Runtime.Net11WinX64.Core
open CIL CIL.Extraction
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace ArgumentInnerCtor

/-- Compact metadata for the physical definition and its scoped operands. -/
def rows : MethodMetadata := {
  own := {
    assembly := CoreLib.assembly,
    rows := [(33554576, (fixedBytes 18 0x0120100003000000050000008802A802E505)),
      (33554577, (fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06)),
      (33554594, (fixedBytes 18 0x0120100004000000050000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF050000003003FE022507)),
      (33554673, (fixedBytes 18 0x012010000200000005000000A407B603E00C)),
      (33554674, (fixedBytes 18 0x01201000FFFFFFFF05000000C403B703EE0C)),
      (33554921, (fixedBytes 18 0x01201000060000000500000040022F067826)),
      (33554922, (fixedBytes 18 0x01011000FFFFFFFF05000000DC012F067C26)),
      (67109544, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109545, (fixedBytes 10 0x0300FFFFFFFF01000000)),
      (67109546, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109547, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109548, (fixedBytes 10 0x0100FFFFFFFF01000000)),
      (67109549, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109550, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109551, (fixedBytes 10 0x0100FFFFFFFF01000000)),
      (67109552, (fixedBytes 10 0x0100FFFFFFFF01000000)),
      (67109553, (fixedBytes 10 0x0100FFFFFFFF01000000)),
      (67109554, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109555, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109556, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109557, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109558, (fixedBytes 10 0x5180FFFFFFFFFFFFFFFF)),
      (67109559, (fixedBytes 10 0x5280FFFFFFFF01000000)),
      (67109814, (fixedBytes 10 0x21000700000001000000)),
      (100664849, (fixedBytes 20 0x000000000000860808000000020000001F0D0000)),
      (100666595, (fixedBytes 20 0x000000000000861801000000040000000D190000)),
      (100673146, (fixedBytes 20 0x00000000000086180100000003000000D43C0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)),
      (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF)),
      (704643224, (fixedBytes 12 0x00002200D0010000FFFFFFFF)),
      (704643225, (fixedBytes 12 0x00000000EE010000FFFFFFFF)),
      (704643422, (fixedBytes 12 0x00001800B4030000FFFFFFFF)),
      (704643423, (fixedBytes 12 0x0000000006040000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)),
      (2, (fixedBytes 18 0x417267756D656E74457863657074696F6E00)),
      (3, (fixedBytes 10 0x457863657074696F6E00)),
      (4, (fixedBytes 7 0x4F626A65637400)),
      (5, (fixedBytes 7 0x53797374656D00)),
      (6, (fixedBytes 16 0x53797374656D457863657074696F6E00)),
      (7, (fixedBytes 11 0x5F706172616D4E616D6500)),
      (8, (fixedBytes 12 0x7365745F48526573756C7400))],
    blobs := [(1, (fixedBytes 3 0x02060E)),
      (2, (fixedBytes 5 0x0420010108)),
      (3, (fixedBytes 8 0x072002010E128240)),
      (4, (fixedBytes 9 0x082003010E0E128240))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 67109814, 0, 33554673⟩,
      ⟨1, 100664849, 0, 33554576⟩,
      ⟨1, 100666595, 0, 33554673⟩,
      ⟨1, 100673146, 0, 33554921⟩] },
  others := [] }

/-- Constructor body bytes and member operands. -/
def body : BodyEvidence := {
  ArgumentCtor.body with
  bytes := (fixedBytes 28 0x6E020305287A26000602047DB603000402205700078028110600062A)
  tokens := { operands := [
    (100673146, .call {
      method := {
        owner := .object coreLibraryScope "System.SystemException",
        name := name!".ctor", hasThis := true,
        genericArity := 0,
        returnType := .void,
        parameters := [.object coreLibraryScope "System.String", .object coreLibraryScope "System.Exception"],
        methodArguments := [] },
        name := ".ctor",
      target := .managed 100673146, typeArguments := [],
      ownerArgumentCount := 0, parameterCount := 2, returnsValue := false,
      declared := {
        convention := 32,
        returnType := .void,
        parameters := [.object coreLibraryScope "System.String", .object coreLibraryScope "System.Exception"] } }),
    (67109814, .field (.object coreLibraryScope "System.ArgumentException") 14 (.object coreLibraryScope "System.String") name!"_paramName" false), (100664849, .call {
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
def definition : RawMethod := Id.run do
  let decoded := do
    let env ← body.environment.mapError BodyError.metadata
    decodeBody env 0 0 body
  let raw := ArgumentCtor.raw (decoded.toOption.getD {
    maxStack := 0, initLocals := false, localSignature := 0, code := [], statics := [] })
  return { raw with token := 100666595, parameters := [.object coreLibraryScope "System.String", .object coreLibraryScope "System.String", .object coreLibraryScope "System.Exception"] }

/-- Raw owner, base classes and constructor signature. -/
def names : MethodNames := {
  ArgumentCtor.names with
  signature := bytesOf "System.Void System.ArgumentException::.ctor(System.String,System.String,System.Exception)" }

/-- The checked body and signature resolve to this MethodDef. -/
theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    { body with names } definition [] "System.Void System.ArgumentException::.ctor(System.String,System.String,System.Exception)" :=
  ⟨.cons ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩ .nil, by decide +kernel,
    by cil_kernel_rfl, by decide +kernel, rfl, by cil_kernel_rfl, by cil_kernel_rfl,
    by cil_body_decodes⟩
#print axioms bound
end ArgumentInnerCtor

namespace SystemInnerCtor

/-- Compact metadata for the physical definition and its scoped operands. -/
def rows : MethodMetadata := {
  own := {
    assembly := CoreLib.assembly,
    rows := [(33554576, (fixedBytes 18 0x0120100002000000040000008802A802E505)),
      (33554577, (fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06)),
      (33554594, (fixedBytes 18 0x0120100003000000040000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF040000003003FE022507)),
      (33554921, (fixedBytes 18 0x01201000050000000400000040022F067826)),
      (33554922, (fixedBytes 18 0x01011000FFFFFFFF04000000DC012F067C26)),
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
      (100664833, (fixedBytes 20 0x00000000000086180100000002000000150D0000)),
      (100664849, (fixedBytes 20 0x000000000000860806000000010000001F0D0000)),
      (100673146, (fixedBytes 20 0x00000000000086180100000002000000D43C0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)),
      (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF)),
      (704643422, (fixedBytes 12 0x00001800B4030000FFFFFFFF)),
      (704643423, (fixedBytes 12 0x0000000006040000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)),
      (2, (fixedBytes 10 0x457863657074696F6E00)),
      (3, (fixedBytes 7 0x4F626A65637400)),
      (4, (fixedBytes 7 0x53797374656D00)),
      (5, (fixedBytes 16 0x53797374656D457863657074696F6E00)),
      (6, (fixedBytes 12 0x7365745F48526573756C7400))],
    blobs := [(1, (fixedBytes 5 0x0420010108)),
      (2, (fixedBytes 8 0x072002010E128240))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 100664833, 0, 33554576⟩,
      ⟨1, 100664849, 0, 33554576⟩,
      ⟨1, 100673146, 0, 33554921⟩] },
  others := [] }

/-- Constructor body bytes and member operands. -/
def body : BodyEvidence := {
  SystemExceptionCtor.body with
  bytes := (fixedBytes 21 0x52020304280106000602200115138028110600062A)
  tokens := { operands := [
    (100664833, .call {
      method := {
        owner := .object coreLibraryScope "System.Exception",
        name := name!".ctor", hasThis := true,
        genericArity := 0,
        returnType := .void,
        parameters := [.object coreLibraryScope "System.String", .object coreLibraryScope "System.Exception"],
        methodArguments := [] },
        name := ".ctor",
      target := .managed 100664833, typeArguments := [],
      ownerArgumentCount := 0, parameterCount := 2, returnsValue := false,
      declared := {
        convention := 32,
        returnType := .void,
        parameters := [.object coreLibraryScope "System.String", .object coreLibraryScope "System.Exception"] } }),
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
def definition : RawMethod := Id.run do
  let decoded := do
    let env ← body.environment.mapError BodyError.metadata
    decodeBody env 0 0 body
  let raw := SystemExceptionCtor.raw (decoded.toOption.getD {
    maxStack := 0, initLocals := false, localSignature := 0, code := [], statics := [] })
  return { raw with token := 100673146, parameters := [.object coreLibraryScope "System.String", .object coreLibraryScope "System.Exception"] }

/-- Raw owner, base classes and constructor signature. -/
def names : MethodNames := {
  SystemExceptionCtor.names with
  signature := bytesOf "System.Void System.SystemException::.ctor(System.String,System.Exception)" }

/-- The checked body and signature resolve to this MethodDef. -/
theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    { body with names } definition [] "System.Void System.SystemException::.ctor(System.String,System.Exception)" :=
  ⟨.cons ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩ .nil, by decide +kernel,
    by cil_kernel_rfl, by decide +kernel, rfl, by cil_kernel_rfl, by cil_kernel_rfl,
    by cil_body_decodes⟩
#print axioms bound
end SystemInnerCtor

namespace ExceptionInnerCtor

/-- Compact metadata for the physical definition and its scoped operands. -/
def rows : MethodMetadata := {
  own := {
    assembly := CoreLib.assembly,
    rows := [(33554576, (fixedBytes 18 0x0120100002000000040000008802A802E505)),
      (33554577, (fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06)),
      (33554594, (fixedBytes 18 0x0120100003000000040000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF040000003003FE022507)),
      (67109544, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109545, (fixedBytes 10 0x03000600000001000000)),
      (67109546, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109547, (fixedBytes 10 0x21000500000003000000)),
      (67109548, (fixedBytes 10 0x0100FFFFFFFF01000000)),
      (67109549, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109550, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109551, (fixedBytes 10 0x0100FFFFFFFF01000000)),
      (67109552, (fixedBytes 10 0x0100FFFFFFFF01000000)),
      (67109553, (fixedBytes 10 0x0100FFFFFFFF01000000)),
      (67109554, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109555, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109556, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109557, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109558, (fixedBytes 10 0x5180FFFFFFFFFFFFFFFF)),
      (67109559, (fixedBytes 10 0x5280FFFFFFFF01000000)),
      (100664831, (fixedBytes 20 0x00000000000086180100000002000000140D0000)),
      (100664833, (fixedBytes 20 0x00000000000086180100000004000000150D0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)),
      (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)),
      (2, (fixedBytes 10 0x457863657074696F6E00)),
      (3, (fixedBytes 7 0x4F626A65637400)),
      (4, (fixedBytes 7 0x53797374656D00)),
      (5, (fixedBytes 16 0x5F696E6E6572457863657074696F6E00)),
      (6, (fixedBytes 9 0x5F6D65737361676500))],
    blobs := [(1, (fixedBytes 3 0x02060E)),
      (2, (fixedBytes 4 0x03200001)),
      (3, (fixedBytes 5 0x0406128240)),
      (4, (fixedBytes 8 0x072002010E128240))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 67109545, 0, 33554576⟩,
      ⟨1, 67109547, 0, 33554576⟩,
      ⟨1, 100664831, 0, 33554576⟩,
      ⟨1, 100664833, 0, 33554576⟩] },
  others := [] }

/-- Constructor body bytes and member operands. -/
def body : BodyEvidence := {
  ExceptionMessageCtor.body with
  bytes := (fixedBytes 22 0x560228FF05000602037DA902000402047DAB0200042A)
  tokens := { operands := [
    (100664831, .call {
      method := {
        owner := .object coreLibraryScope "System.Exception",
        name := name!".ctor", hasThis := true,
        genericArity := 0,
        returnType := .void,
        parameters := [],
        methodArguments := [] },
        name := ".ctor",
      target := .managed 100664831, typeArguments := [],
      ownerArgumentCount := 0, parameterCount := 0, returnsValue := false,
      declared := {
        convention := 32,
        returnType := .void,
        parameters := [] } }),
    (67109545, .field (.object coreLibraryScope "System.Exception") 1 (.object coreLibraryScope "System.String") name!"_message" false), (67109547, .field (.object coreLibraryScope "System.Exception") 3 (.object coreLibraryScope "System.Exception") name!"_innerException" false)] }
  metadata := rows
  tables := rows.tables.toOption.getD [] }

/-- Physical definition decoded with its own metadata. -/
def definition : RawMethod := Id.run do
  let decoded := do
    let env ← body.environment.mapError BodyError.metadata
    decodeBody env 0 0 body
  let raw := ExceptionMessageCtor.raw (decoded.toOption.getD {
    maxStack := 0, initLocals := false, localSignature := 0, code := [], statics := [] })
  return { raw with token := 100664833, parameters := [.object coreLibraryScope "System.String", .object coreLibraryScope "System.Exception"] }

/-- Raw owner, base classes and constructor signature. -/
def names : MethodNames := {
  ExceptionMessageCtor.names with
  signature := bytesOf "System.Void System.Exception::.ctor(System.String,System.Exception)" }

/-- The checked body and signature resolve to this MethodDef. -/
theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    { body with names } definition [] "System.Void System.Exception::.ctor(System.String,System.Exception)" :=
  ⟨.cons ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩ .nil, by decide +kernel,
    by cil_kernel_rfl, by decide +kernel, rfl, by cil_kernel_rfl, by cil_kernel_rfl,
    by cil_body_decodes⟩
#print axioms bound
end ExceptionInnerCtor

namespace InvalidOperationInnerCtor

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
      (100670309, (fixedBytes 20 0x00000000000086180100000003000000DF310000)),
      (100671961, (fixedBytes 20 0x00000000000093080800000001000000733C0000)),
      (100673146, (fixedBytes 20 0x00000000000086180100000003000000D43C0000)),
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
      (3, (fixedBytes 8 0x072002010E128240))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 100664849, 0, 33554576⟩,
      ⟨1, 100670309, 0, 33554816⟩,
      ⟨1, 100671961, 0, 33554911⟩,
      ⟨1, 100673146, 0, 33554921⟩] },
  others := [] }

/-- Constructor body bytes and member operands. The getter supplies the default message. -/
def body : BodyEvidence := {
  SystemInnerCtor.body with
  bytes := (fixedBytes 30 0x760203252D062628D921000604287A26000602200915138028110600062A)
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
    (100673146, .call {
      method := {
        owner := .object coreLibraryScope "System.SystemException",
        name := name!".ctor", hasThis := true,
        genericArity := 0,
        returnType := .void,
        parameters := [.object coreLibraryScope "System.String",
          .object coreLibraryScope "System.Exception"],
        methodArguments := [] },
        name := ".ctor",
      target := .managed 100673146, typeArguments := [],
      ownerArgumentCount := 0, parameterCount := 2, returnsValue := false,
      declared := {
        convention := 32,
        returnType := .void,
        parameters := [.object coreLibraryScope "System.String",
          .object coreLibraryScope "System.Exception"] } }),
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
  { token := 100670309, owner := (coreLibraryScope ++ "::System.InvalidOperationException"),
    hasThis := true, explicitThis := false, callingConvention := 0, attributes := 6278,
    implementation := 0, returnType := .void,
    parameters := [.object coreLibraryScope "System.String",
      .object coreLibraryScope "System.Exception"],
    locals := [],
    receiverClass := some (.object coreLibraryScope "System.InvalidOperationException"),
    objectBases := [.object coreLibraryScope "System.SystemException",
      .object coreLibraryScope "System.Exception"],
    objectFieldCount := 14, initLocals := decoded.initLocals, maxStack := decoded.maxStack,
    genericParameters := [], code := decoded.code }

/-- Raw owner, base classes and constructor signature. -/
def names : MethodNames := {
  owner := bytesOf (coreLibraryScope ++ "::System.InvalidOperationException"),
  bases := [(bytesOf coreLibraryScope, "System.SystemException"),
    (bytesOf coreLibraryScope, "System.Exception")],
  signature :=
    bytesOf "System.Void System.InvalidOperationException::.ctor(System.String,System.Exception)" }

/-- The checked body and signature resolve to this MethodDef. -/
theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    { body with names } definition []
      "System.Void System.InvalidOperationException::.ctor(System.String,System.Exception)" :=
  ⟨.cons ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩ .nil, by decide +kernel,
    by cil_kernel_rfl, by decide +kernel, rfl, by cil_kernel_rfl, by cil_kernel_rfl,
    by cil_body_decodes⟩
#print axioms bound
end InvalidOperationInnerCtor

end CIL.Runtime.Net11WinX64.Core
