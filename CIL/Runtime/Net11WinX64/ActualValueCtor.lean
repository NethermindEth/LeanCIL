import CIL.Runtime.Net11WinX64.RangeMethods

/-! The three-argument range constructor stores the actual value before setting HResult. -/

namespace CIL.Runtime.Net11WinX64.Core.ActualValueCtor
open CIL CIL.Extraction

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

/-- Metadata rows and heaps for the physical constructor. -/
def rows : MethodMetadata := {
  own := {
    assembly := CIL.Runtime.Net11WinX64.CoreLib.assembly,
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
      (67109544, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109545, (fixedBytes 10 0x0300FFFFFFFFFFFFFFFF)),
      (67109546, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109547, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109548, (fixedBytes 10 0x0100FFFFFFFFFFFFFFFF)),
      (67109549, (fixedBytes 10 0x0100FFFFFFFF01000000)),
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
      (67109814, (fixedBytes 10 0x2100FFFFFFFFFFFFFFFF)),
      (67109815, (fixedBytes 10 0x21000900000001000000)),
      (100664849, (fixedBytes 20 0x00000000000086080B000000030000001F0D0000)),
      (100666596, (fixedBytes 20 0x0000000000008618010000000400000010190000)),
      (100666620, (fixedBytes 20 0x0000000000008618010000000500000033190000)),
      (100671882, (fixedBytes 20 0x00000000000093080A00000002000000733C0000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)),
      (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF)),
      (704643224, (fixedBytes 12 0x00002200D0010000FFFFFFFF)),
      (704643225, (fixedBytes 12 0x00000000EE010000FFFFFFFF)),
      (704643422, (fixedBytes 12 0x00001800B4030000FFFFFFFF)),
      (704643423, (fixedBytes 12 0x0000000006040000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)),
      (2, (fixedBytes 18 0x417267756D656E74457863657074696F6E00)),
      (3, (fixedBytes 28 0x417267756D656E744F75744F6652616E6765457863657074696F6E00)),
      (4, (fixedBytes 10 0x457863657074696F6E00)),
      (5, (fixedBytes 7 0x4F626A65637400)),
      (6, (fixedBytes 3 0x535200)),
      (7, (fixedBytes 7 0x53797374656D00)),
      (8, (fixedBytes 16 0x53797374656D457863657074696F6E00)),
      (9, (fixedBytes 13 0x5F61637475616C56616C756500)),
      (10, (fixedBytes 36 0x6765745F4172675F417267756D656E744F75744F6652616E6765457863657074696F6E00)),
      (11, (fixedBytes 12 0x7365745F48526573756C7400))],
    blobs := [(1, (fixedBytes 3 0x02061C)),
      (2, (fixedBytes 4 0x0300000E)),
      (3, (fixedBytes 5 0x0420010108)),
      (4, (fixedBytes 6 0x052002010E0E)),
      (5, (fixedBytes 7 0x062003010E1C0E))],
    userStrings := [],
    corlib := 0, links := [⟨1, 67109815, 0, 33554675⟩, ⟨1, 100664849, 0, 33554576⟩, ⟨1, 100666596, 0, 33554673⟩, ⟨1, 100666620, 0, 33554675⟩, ⟨1, 100671882, 0, 33554911⟩] },
  others := [] }

/-- The original body and scoped member operands of the actual-value overload. -/
def body : BodyEvidence := {
  RangeCtor.body with
  bytes := [146, 2, 5, 37, 45, 6, 38, 40, 138, 33, 0, 6, 3, 40, 228, 12, 0, 6,
    2, 4, 125, 183, 3, 0, 4, 2, 32, 2, 21, 19, 128, 40, 17, 6, 0, 6, 42]
  tokens := { operands := RangeCtor.body.tokens.operands ++ [
    (67109815, .field (.object coreLibraryScope "System.ArgumentOutOfRangeException") 15
      (.object coreLibraryScope "System.Object") name!"_actualValue" false)] }
  metadata := rows
  tables := rows.tables.toOption.getD [] }

private def decoded := do
  let env ← body.environment.mapError BodyError.metadata
  decodeBody env 0 0 body

/-- The caller-visible parameter types and the physical method definition. -/
def definition : RawMethod := {
  RangeCtor.definition with
  token := 100666620
  parameters := [.object coreLibraryScope "System.String", .object coreLibraryScope "System.Object",
    .object coreLibraryScope "System.String"]
  code := (decoded.toOption.map DecodedBody.code).getD [] }

/-- Physical owner, bases and overload signature. -/
def names : MethodNames := {
  RangeCtor.names with
  signature := bytesOf
    "System.Void System.ArgumentOutOfRangeException::.ctor(System.String,System.Object,System.String)" }

theorem bound : BodyDecodes [⟨coreLibraryScope⟩] {} ⟨coreLibraryScope⟩
    {body with names} definition []
    "System.Void System.ArgumentOutOfRangeException::.ctor(System.String,System.Object,System.String)" :=
  ⟨.cons ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩ .nil, by decide +kernel,
    by cil_kernel_rfl, by decide +kernel, rfl, by cil_kernel_rfl, by cil_kernel_rfl,
    by cil_body_decodes⟩
#print axioms bound

end CIL.Runtime.Net11WinX64.Core.ActualValueCtor
