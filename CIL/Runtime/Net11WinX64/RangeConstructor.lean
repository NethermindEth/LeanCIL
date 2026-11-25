import CIL.Extraction.ManagedPackage
import CIL.Runtime.Net11WinX64.ActualValueCtor
import CIL.Runtime.Net11WinX64.InnerMethods
import CIL.Runtime.Net11WinX64.MessageCtor

/-! Managed execution of the bound exception constructors in the .NET 11.0.0 Windows x64 runtime:
the two range constructors, the ArgumentException constructors with a parameter name and with an
inner exception, and the InvalidOperationException constructors with a message and with an inner
exception. A resource getter reached only by a null message is declared in the slot after the
executable methods. -/

namespace CIL.Runtime.Net11WinX64
open CIL.Extraction Core

/-- System.Runtime facade identity, table header and heaps. -/
def facadeAssembly : AssemblyMetadata := {
  identity := runtimeScope,
  keyToken := (fixedBytes 16 0x62303366356637663131643530613361),
  tableHeader := (fixedBytes 56 0x000000000200000A071400008900000000FA01330016C40001000000120000000100000010000000140000000100000002000000BE030000),
  header := .ofCounts 0 [(0, 1), (1, 18), (2, 1), (10, 16), (12, 20),
    (32, 1), (35, 2), (39, 958)],
  assemblyRow := (fixedBytes 22 0x048000000B0000000000000001000000010001000000),
  strings := [(0, (fixedBytes 1 0x00)), (1, (fixedBytes 15 0x53797374656D2E52756E74696D6500))],
  blobs := [(1, (fixedBytes 162 0x80A0002400000480000094000000060200000024000052534131000400000100010007D1FA57C4AED9F0A32E84AA0FAEFD0DE9E8FD6AEC8F87FB03766C834C99921EB23BE79AD9D5DCC1DD9AD236132102900B723CF980957FC4E177108FC607774F29E8320E92EA05ECE4E821C0A5EFE8F1645C4C0C93C1AB99285D622CAA652C1DFAD63D745D6F2DE5F17E5EAF0FC4963D261C8A12436518206DC093344D5AD293))]}

/-- Identity bytes for the System.Runtime facade. -/
def facadeIdentity := bytesOf runtimeScope

/-- The facade metadata authenticates the System.Runtime identity. -/
theorem facadeIdentified : AssemblyIdentified facadeAssembly facadeIdentity := ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms facadeIdentified

/-- Defining CoreLib assembly for the forwarded constructor. -/
private def coreAssembly := CoreLib.assembly

/-- Identity bytes for the defining CoreLib assembly. -/
def coreIdentity := bytesOf coreLibraryScope

/-- The definition metadata authenticates the CoreLib identity. -/
theorem coreIdentified : AssemblyIdentified coreAssembly coreIdentity := ⟨by cil_kernel_rfl, by cil_kernel_rfl, by cil_kernel_rfl⟩
#print axioms coreIdentified

/-- Caller-side facade and CoreLib slices for the two-string range constructor. -/
private def rangeMemberDependencies (token : Nat) (methodRow signature : List Nat) :
    List MetadataSlice := [{
      assembly := facadeAssembly,
      rows := [(587202561, (fixedBytes 20 0x0B00000000000000000000000100040000000000)),
        (654311462, (fixedBytes 14 0x0000200000000000010003000500)),
        (654311851, (fixedBytes 14 0x0000200000000000020003000500))],
      strings := [(0, (fixedBytes 1 0x00)), (1, (fixedBytes 28 0x417267756D656E744F75744F6652616E6765457863657074696F6E00)),
        (2, (fixedBytes 7 0x4F626A65637400)), (3, (fixedBytes 7 0x53797374656D00)),
        (4, (fixedBytes 23 0x53797374656D2E507269766174652E436F72654C696200))],
      blobs := [(1, (fixedBytes 9 0x087CEC85D7BEA7798E))],
      userStrings := [],
      corlib := 1,
      links := []}, {
      assembly := coreAssembly,
      rows := [(33554594, (fixedBytes 18 0x0120100004000000050000000000FE021C07)),
        (33554673, (fixedBytes 18 0x012010000200000005000000A407B603E00C)),
        (33554675, (fixedBytes 18 0x012010000300000005000000C403B703F80C)),
        (33554676, (fixedBytes 18 0x01201000FFFFFFFF05000000A407B803130D)),
        (token, methodRow),
        (704643224, (fixedBytes 12 0x00002200D0010000FFFFFFFF)),
        (704643225, (fixedBytes 12 0x00000000EE010000FFFFFFFF))],
      strings := [(1, (fixedBytes 6 0x2E63746F7200)), (2, (fixedBytes 18 0x417267756D656E74457863657074696F6E00)),
        (3, (fixedBytes 28 0x417267756D656E744F75744F6652616E6765457863657074696F6E00)),
        (4, (fixedBytes 7 0x4F626A65637400)), (5, (fixedBytes 7 0x53797374656D00))],
      blobs := [(1, signature)],
      userStrings := [],
      corlib := 0,
      links := [⟨1, token, 2, 33554675⟩]}]

/-- Forwarded MethodDef and signature for the two-string overload. -/
def rangeDependencies := rangeMemberDependencies 100666618
  (fixedBytes 20 0x000000000000861801000000010000002F190000) (fixedBytes 6 0x052002010E0E)

/-- Forwarded MethodDef and signature for the overload with an actual value. -/
private def actualDependencies := rangeMemberDependencies 100666620
  (fixedBytes 20 0x0000000000008618010000000100000033190000) (fixedBytes 7 0x062003010E1C0E)

/-- Forwarders and MethodDef for the argument constructor carrying an inner exception. -/
private def argumentInnerDependencies : List MetadataSlice := [{
    assembly := facadeAssembly,
    rows := [(587202561, (fixedBytes 20 0x0B00000000000000000000000100050000000000)),
      (654311460, (fixedBytes 14 0x0000200000000000010004000500)),
      (654311620, (fixedBytes 14 0x0000200000000000020004000500)),
      (654311851, (fixedBytes 14 0x0000200000000000030004000500))],
    strings := [(0, (fixedBytes 1 0x00)),
      (1, (fixedBytes 18 0x417267756D656E74457863657074696F6E00)),
      (2, (fixedBytes 10 0x457863657074696F6E00)),
      (3, (fixedBytes 7 0x4F626A65637400)),
      (4, (fixedBytes 7 0x53797374656D00)),
      (5, (fixedBytes 23 0x53797374656D2E507269766174652E436F72654C696200))],
    blobs := [(1, (fixedBytes 9 0x087CEC85D7BEA7798E))],
    userStrings := [],
    corlib := 1,
    links := [] }, {
    assembly := CoreLib.assembly,
    rows := [(33554576, (fixedBytes 18 0x0120100003000000050000008802A802E505)),
      (33554577, (fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06)),
      (33554594, (fixedBytes 18 0x0120100004000000050000000000FE021C07)),
      (33554673, (fixedBytes 18 0x012010000200000005000000A407B603E00C)),
      (33554674, (fixedBytes 18 0x01201000FFFFFFFF05000000C403B703EE0C)),
      (33554921, (fixedBytes 18 0x01201000060000000500000040022F067826)),
      (100666595, (fixedBytes 20 0x000000000000861801000000010000000D190000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)),
      (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF)),
      (704643224, (fixedBytes 12 0x00002200D0010000FFFFFFFF)),
      (704643225, (fixedBytes 12 0x00000000EE010000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)),
      (2, (fixedBytes 18 0x417267756D656E74457863657074696F6E00)),
      (3, (fixedBytes 10 0x457863657074696F6E00)),
      (4, (fixedBytes 7 0x4F626A65637400)),
      (5, (fixedBytes 7 0x53797374656D00)),
      (6, (fixedBytes 16 0x53797374656D457863657074696F6E00))],
    blobs := [(1, (fixedBytes 9 0x082003010E0E128240))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 100666595, 2, 33554673⟩] }]

/-- Forwarders and MethodDef for the InvalidOperationException constructor with an inner
exception. -/
private def invalidOperationInnerDependencies : List MetadataSlice := [{
    assembly := facadeAssembly,
    rows := [(587202561, (fixedBytes 20 0x0B00000000000000000000000100050000000000)),
      (654311620, (fixedBytes 14 0x0000200000000000010004000500)),
      (654311720, (fixedBytes 14 0x0000200000000000020004000500)),
      (654311851, (fixedBytes 14 0x0000200000000000030004000500))],
    strings := [(0, (fixedBytes 1 0x00)),
      (1, (fixedBytes 10 0x457863657074696F6E00)),
      (2, (fixedBytes 26 0x496E76616C69644F7065726174696F6E457863657074696F6E00)),
      (3, (fixedBytes 7 0x4F626A65637400)),
      (4, (fixedBytes 7 0x53797374656D00)),
      (5, (fixedBytes 23 0x53797374656D2E507269766174652E436F72654C696200))],
    blobs := [(1, (fixedBytes 9 0x087CEC85D7BEA7798E))],
    userStrings := [],
    corlib := 1,
    links := [] }, {
    assembly := CoreLib.assembly,
    rows := [(33554576, (fixedBytes 18 0x0120100002000000050000008802A802E505)),
      (33554577, (fixedBytes 18 0x05010000FFFFFFFF000000002402B8021A06)),
      (33554594, (fixedBytes 18 0x0120100004000000050000000000FE021C07)),
      (33554816, (fixedBytes 18 0x012010000300000005000000A4078205631B)),
      (33554817, (fixedBytes 18 0x01211000FFFFFFFF05000000A4078205671B)),
      (33554921, (fixedBytes 18 0x01201000060000000500000040022F067826)),
      (100670309, (fixedBytes 20 0x00000000000086180100000001000000DF310000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)),
      (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF)),
      (704643390, (fixedBytes 12 0x00001800E6020000FFFFFFFF)),
      (704643391, (fixedBytes 12 0x0000010006030000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)),
      (2, (fixedBytes 10 0x457863657074696F6E00)),
      (3, (fixedBytes 26 0x496E76616C69644F7065726174696F6E457863657074696F6E00)),
      (4, (fixedBytes 7 0x4F626A65637400)),
      (5, (fixedBytes 7 0x53797374656D00)),
      (6, (fixedBytes 16 0x53797374656D457863657074696F6E00))],
    blobs := [(1, (fixedBytes 8 0x072002010E128240))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 100670309, 2, 33554816⟩] }]

/-- Forwarders and MethodDef for the InvalidOperationException constructor with only a
message. -/
private def invalidOperationMessageDependencies : List MetadataSlice := [{
    assembly := facadeAssembly,
    rows := [(587202561, (fixedBytes 20 0x0B00000000000000000000000100040000000000)),
      (654311720, (fixedBytes 14 0x0000200000000000010003000500)),
      (654311851, (fixedBytes 14 0x0000200000000000020003000500))],
    strings := [(0, (fixedBytes 1 0x00)),
      (1, (fixedBytes 26 0x496E76616C69644F7065726174696F6E457863657074696F6E00)),
      (2, (fixedBytes 7 0x4F626A65637400)),
      (3, (fixedBytes 7 0x53797374656D00)),
      (4, (fixedBytes 23 0x53797374656D2E507269766174652E436F72654C696200))],
    blobs := [(1, (fixedBytes 9 0x087CEC85D7BEA7798E))],
    userStrings := [],
    corlib := 1,
    links := [] }, {
    assembly := CoreLib.assembly,
    rows := [(33554594, (fixedBytes 18 0x0120100003000000040000000000FE021C07)),
      (33554595, (fixedBytes 18 0x09011000FFFFFFFF040000003003FE022507)),
      (33554816, (fixedBytes 18 0x012010000200000004000000A4078205631B)),
      (33554817, (fixedBytes 18 0x01211000FFFFFFFF04000000A4078205671B)),
      (33554921, (fixedBytes 18 0x01201000050000000400000040022F067826)),
      (100670308, (fixedBytes 20 0x00000000000086180100000001000000DE310000)),
      (704643081, (fixedBytes 12 0x0000180016010000FFFFFFFF)),
      (704643082, (fixedBytes 12 0x000004006A010000FFFFFFFF)),
      (704643390, (fixedBytes 12 0x00001800E6020000FFFFFFFF)),
      (704643391, (fixedBytes 12 0x0000010006030000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)),
      (2, (fixedBytes 26 0x496E76616C69644F7065726174696F6E457863657074696F6E00)),
      (3, (fixedBytes 7 0x4F626A65637400)),
      (4, (fixedBytes 7 0x53797374656D00)),
      (5, (fixedBytes 16 0x53797374656D457863657074696F6E00))],
    blobs := [(1, (fixedBytes 5 0x042001010E))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 100670308, 2, 33554816⟩] }]

/-- Forwarders and MethodDef for the ArgumentException constructor with a message and a
parameter name. -/
private def argumentNameDependencies : List MetadataSlice := [{
    assembly := facadeAssembly,
    rows := [(587202561, (fixedBytes 20 0x0B00000000000000000000000100040000000000)),
      (654311460, (fixedBytes 14 0x0000200000000000010003000500)),
      (654311851, (fixedBytes 14 0x0000200000000000020003000500))],
    strings := [(0, (fixedBytes 1 0x00)),
      (1, (fixedBytes 18 0x417267756D656E74457863657074696F6E00)),
      (2, (fixedBytes 7 0x4F626A65637400)),
      (3, (fixedBytes 7 0x53797374656D00)),
      (4, (fixedBytes 23 0x53797374656D2E507269766174652E436F72654C696200))],
    blobs := [(1, (fixedBytes 9 0x087CEC85D7BEA7798E))],
    userStrings := [],
    corlib := 1,
    links := [] }, {
    assembly := CoreLib.assembly,
    rows := [(33554594, (fixedBytes 18 0x0120100003000000040000000000FE021C07)),
      (33554673, (fixedBytes 18 0x012010000200000004000000A407B603E00C)),
      (33554674, (fixedBytes 18 0x01201000FFFFFFFF04000000C403B703EE0C)),
      (33554921, (fixedBytes 18 0x01201000050000000400000040022F067826)),
      (100666596, (fixedBytes 20 0x0000000000008618010000000100000010190000)),
      (704643224, (fixedBytes 12 0x00002200D0010000FFFFFFFF)),
      (704643225, (fixedBytes 12 0x00000000EE010000FFFFFFFF))],
    strings := [(1, (fixedBytes 6 0x2E63746F7200)),
      (2, (fixedBytes 18 0x417267756D656E74457863657074696F6E00)),
      (3, (fixedBytes 7 0x4F626A65637400)),
      (4, (fixedBytes 7 0x53797374656D00)),
      (5, (fixedBytes 16 0x53797374656D457863657074696F6E00))],
    blobs := [(1, (fixedBytes 6 0x052002010E0E))],
    userStrings := [],
    corlib := 0,
    links := [⟨1, 100666596, 2, 33554673⟩] }]

/-- Physical bodies reached by the constructor with a non-null message argument. -/
def coreBytes : List (BodyEvidence × RawMethod) := [
    ({ RangeCtor.body with names := RangeCtor.names }, RangeCtor.definition),
    ({ ArgumentCtor.body with names := ArgumentCtor.names }, ArgumentCtor.definition),
    ({ SystemExceptionCtor.body with names := SystemExceptionCtor.names }, SystemExceptionCtor.definition),
    ({ ExceptionMessageCtor.body with names := ExceptionMessageCtor.names }, ExceptionMessageCtor.definition),
    ({ ExceptionCtor.body with names := ExceptionCtor.names }, ExceptionCtor.definition),
    ({ ObjectCtor.body with names := ObjectCtor.names }, ObjectCtor.definition),
    ({ SetHResult.body with names := SetHResult.names }, SetHResult.definition)]

/-- Executable definitions in the closed three-argument ArgumentException call graph. -/
private def argumentInnerMethods : List (BodyEvidence × RawMethod) := [
    ({ ArgumentInnerCtor.body with names := ArgumentInnerCtor.names }, ArgumentInnerCtor.definition),
    ({ SystemInnerCtor.body with names := SystemInnerCtor.names }, SystemInnerCtor.definition),
    ({ ExceptionInnerCtor.body with names := ExceptionInnerCtor.names }, ExceptionInnerCtor.definition),
    ({ ExceptionCtor.body with names := ExceptionCtor.names }, ExceptionCtor.definition),
    ({ ObjectCtor.body with names := ObjectCtor.names }, ObjectCtor.definition),
    ({ SetHResult.body with names := SetHResult.names }, SetHResult.definition)]

/-- Executable definitions reached by the InvalidOperationException overload with a message. -/
private def invalidOperationInnerMethods : List (BodyEvidence × RawMethod) :=
  ({ InvalidOperationInnerCtor.body with names := InvalidOperationInnerCtor.names },
    InvalidOperationInnerCtor.definition) :: argumentInnerMethods.tail

/-- Executable definitions reached by the InvalidOperationException overload with only a non-null
message. -/
private def invalidOperationMessageMethods : List (BodyEvidence × RawMethod) :=
  ({ InvalidOperationMessageCtor.body with names := InvalidOperationMessageCtor.names },
    InvalidOperationMessageCtor.definition) :: coreBytes.drop 2

/-- Admit a managed call or allocation only if the raw site selects its unique physical target. -/
def linked (table : List SpecializedMethod) (raw : RawInstruction) : Option Link := do
  let .call site := raw.operand | none
  let .managed token := site.target | none
  let [(callee,ordinal)] := table.zipIdx.filter (fun item => calleeMatchesSite site token item.1) | none
  if raw.opcode == 0x73 then
    let link := Link.object ordinal callee.closed.objectBases (objectFieldOffset callee.closed.objectFieldCount)
    guard (validateConstructionWith (fun i => table[i]?) raw true (some link) site.method)
    return link
  guard (raw.opcode == 0x28)
  let link := Link.direct ordinal
  guard (validateManagedCallWith table.length (fun i => table[i]?) (fun _ => none)
    raw true (some link) (.call site.method {}))
  return link
/-- Checked links indexed by the original instruction positions. -/
def links (table : List SpecializedMethod) (raw : RawMethod) :=
  raw.code.zipIdx.filterMap fun (op,pc) => (linked table op).map (pc,·)

/-- The scalar and x64 execution profiles with the runtime image's pointer width and byte order. -/
def supportsProfile (profile : FeatureProfile) : Bool :=
  profile.nativeWidth == 64 && profile.littleEndian && profile.architecture != .arm64

/-- Infer scalar stacks along reachable paths from the entry and from every handler start. With no
caller-supplied feature facts, both successors of a conditional are considered and every stack
value has unknown feature bits. -/
private def inferFlow? (raw : RawMethod) (method : Method)
    (supplied : Option FeatureCertificate) : Option (FeatureCertificate × ScalarCertificate) := do
  let sites := (raw.code.zip (foldRoles raw.code)).toArray
  let facts := supplied.map List.toArray
  let code := method.code.toArray
  guard (sites.size > 0 && facts.all (·.size == sites.size) && code.size == sites.size)
  let context := nativeDispatchContext raw
  let locals := ScalarLocals.indexed raw context
  let rec visit : Nat → List Nat → Array (Option (List ScalarKind)) → Option ScalarCertificate
    | _, [], states => some states.toList
    | 0, _ :: _, _ => none
    | fuel + 1, pc :: pending, states => do
      let (op, role) ← sites[pc]?
      let some stack ← states[pc]? | none
      let emitted ← code[pc]?
      if scalarStoreFault raw op stack emitted locals then return ← visit fuel pending states
      let features ← match facts with
        | none => some (List.replicate stack.length none)
        | some known => (known[pc]?).join.map (·.stack)
      let after ← scalarTransfer raw op stack role context locals
      let next ← featureSuccessors role pc op features
      let mut todo := pending
      let mut incoming := states
      for target in next do
        match ← incoming[target]? with
        | some known => guard (known == after)
        | none =>
          incoming := incoming.set! target (some after)
          todo := target :: todo
      visit fuel todo incoming
  let roots := (0, []) :: raw.handlers.map fun clause => (clause.handlerStart, clause.entryKinds)
  let seeded := roots.foldl (fun states (pc, stack) => states.set! pc (some stack))
    (Array.replicate sites.size none)
  let states ← visit (sites.size + roots.length) (roots.map Prod.fst) seeded
  let features := supplied.getD (states.map (·.map fun stack =>
    { stack := List.replicate stack.length none, locals := [] }))
  return (features, states)

/-- Physical runtime definitions use the caller's complete pin index, platform and layouts. -/
private def runtimeRow? (table : List SpecializedMethod) (caller : BodyEvidence)
    (profile : FeatureProfile) (environment : LayoutEnvironment)
    (source : BodyEvidence × RawMethod) : Option (MethodEvidence × Method) := do
  let original := source.2
  let body := { source.1 with
    pinned := caller.pinned, platform := caller.platform,
    layoutDeclarations := caller.layoutDeclarations }
  let closed ← instantiateMethod environment.rawLayouts original []
  let storage ← closedArguments environment.rawLayouts closed
  let live := List.replicate original.code.length true
  let bound := links table closed
  let method ← Method.ofBody? profile environment bound live body original []
  let (features, scalars) ← inferFlow? closed method none
  let signature ← spelled? body.names.signature
  let item : MethodEvidence := {
    original, body, arguments := [], closed, parameterInput := storage,
    reachable := live, featureStates := features, scalarStates := scalars, layoutUses := [],
    assembly := ⟨coreLibraryScope⟩, signature, links := bound }
  return (item, method)

/-- The resource slot exposes the physical getter's metadata, with no executable feature facts. -/
private def resourceDeclaration? (caller : BodyEvidence) (environment : LayoutEnvironment)
    (getter : ResourceGetter) : Option MethodEvidence := do
  let original := getter.raw
  let body := { getter.body with
    names := getter.names, pinned := caller.pinned,
    platform := caller.platform, layoutDeclarations := caller.layoutDeclarations }
  let closed ← instantiateMethod environment.rawLayouts original []
  let storage ← closedArguments environment.rawLayouts closed
  let signature ← spelled? body.names.signature
  return {
    original, body, arguments := [], closed, parameterInput := storage, reachable := [],
    featureStates := [], scalarStates := [], layoutUses := [], assembly := ⟨coreLibraryScope⟩,
    signature }

/-- Physical inputs needed to bind a caller. The executable, closed method, construction
links and scalar certificate are derived after resolving the managed constructor. -/
structure ConstructorSource where
  original : RawMethod
  body : BodyEvidence
  arguments : List TypeExpr
  reachable : List Bool
  featureStates : FeatureCertificate
  layoutUses : List LayoutUse
  dispatchTypes : List DispatchType
  assembly : AssemblyPin
  signature : String

/-- The raw source fields shared with an ordinary extraction. -/
def ConstructorSource.ofEvidence (item : MethodEvidence) : ConstructorSource :=
  ⟨item.original, item.body, item.arguments, item.reachable, item.featureStates,
    item.layoutUses, item.dispatchTypes, item.assembly, item.signature⟩

/-- Live external exception constructions in source instruction order. -/
def ConstructorSource.sites (source : ConstructorSource) : List Nat :=
  (source.original.code.zip source.reachable).zipIdx.filterMap fun ((op, live), pc) => do
    guard (live && op.opcode == 0x73)
    let .call site := op.operand | none
    let _ ← exceptionConstructor? site
    return pc

/-- The physical call graph bound for one constructor overload. `loads` lists the opcodes that
must load the trailing arguments directly before `newobj`, so a declared getter is never
reached. -/
private structure BoundOverload where
  dependencies : List MetadataSlice
  methods : List (BodyEvidence × RawMethod)
  getter : Option ResourceGetter
  loads : List Nat

/-- `ldstr`, which loads a non-null string. -/
private def loadString := 0x72

/-- `ldnull`. -/
private def loadNull := 0x14

/-- The bound overloads by exception owner and declared parameter types. -/
private def boundOverloads : List (ExceptionType × List TypeExpr × BoundOverload) :=
  let message := messageParameter
  [(.argumentOutOfRange, [message, message],
      ⟨rangeDependencies, coreBytes, some rangeResource, [loadString]⟩),
    (.argumentOutOfRange, [message, actualParameter, message],
      ⟨actualDependencies, ({ ActualValueCtor.body with names := ActualValueCtor.names },
        ActualValueCtor.definition) :: coreBytes.tail, some rangeResource, [loadString]⟩),
    (.argument, [message, message], ⟨argumentNameDependencies, coreBytes.tail, none, []⟩),
    (.argument, [message, message, innerParameter],
      ⟨argumentInnerDependencies, argumentInnerMethods, none, []⟩),
    (.invalidOperation, [message],
      ⟨invalidOperationMessageDependencies, invalidOperationMessageMethods,
        some invalidOperationResource, [loadString]⟩),
    (.invalidOperation, [message, innerParameter],
      ⟨invalidOperationInnerDependencies, invalidOperationInnerMethods,
        some invalidOperationResource, [loadString, loadNull]⟩)]

/-- Select the bound overload from the exception owner and its exact parameter types, as the
extractor's selector does. Binding then checks that the MemberRef resolves to the head method's
MethodDef. -/
private def selectOverload? (raised : ExceptionType) (parameters : List TypeExpr) :
    Option BoundOverload := do
  let (_, _, image) ← boundOverloads.find? fun (owner, declared, _) =>
    owner == raised && declared == parameters
  return image

/-- The bound overload a live external exception constructor selects. -/
private def boundOverload? (constructor : CallSite) : Option BoundOverload := do
  selectOverload? (← exceptionConstructor? constructor) constructor.parameterTypes

/-- The items of `items` with a distinct `key`, each first occurrence in order. -/
private def firstByKey (key : α → Nat) (items : List α) : List α :=
  items.foldl (fun kept item => if kept.any (key · == key item) then kept else kept ++ [item]) []

/-- The runtime definitions, declared getters and dependency slices bound for a set of
constructor overloads. A definition or getter shared between overloads appears once, at its
first use, so each call in the image selects a unique slot. -/
structure ConstructorImage where
  dependencies : List MetadataSlice
  methods : List (BodyEvidence × RawMethod)
  getters : List ResourceGetter

/-- The image of the overloads named by exception owner and exact parameter types. Every overload
must resolve through the same dependency slices. -/
def ConstructorImage.of? (overloads : List (ExceptionType × List TypeExpr)) :
    Option ConstructorImage := do
  let selected ← overloads.mapM fun (raised, parameters) => selectOverload? raised parameters
  -- Comparing the first slices with themselves would make `decide` over the program evaluate them.
  let first :: rest := selected | none
  guard (rest.all fun overload => overload.dependencies == first.dependencies)
  return {
    dependencies := first.dependencies,
    methods := firstByKey (·.2.token) (selected.flatMap (·.methods)),
    getters := firstByKey (·.token) (selected.flatMap (·.getter.toList)) }

/-- A caller rebound to an image: its body carrying the dependency rows and member links, its
method decoded from that body, and the construction link of each bound site. -/
structure BoundCaller where
  body : BodyEvidence
  original : RawMethod
  links : List (Nat × Link)

/-- Bind the live exception constructions at `pcs` in a caller whose program places the image's
methods from slot `base`. Each site selects an overload of the image, and every entry to its
`newobj` runs that overload's literal loads, so a declared getter is never reached. -/
def ConstructorImage.bindCaller? (image : ConstructorImage) (base : Nat) (body : BodyEvidence)
    (source : RawMethod) (pcs : List Nat) : Option BoundCaller := do
  let sites ← pcs.mapM fun pc => do
    let site ← source.code[pc]?
    let .call constructor := site.operand | none
    let overload ← boundOverload? constructor
    guard (overload.methods.all fun (_, method) =>
      image.methods.any (·.2.token == method.token))
    guard (overload.getter.all fun getter => image.getters.any (·.token == getter.token))
    let (_, callee) ← overload.methods.head?
    let ordinal ← image.methods.findIdx? (·.2.token == callee.token)
    return (pc, overload.loads, callee, base + ordinal)
  let bound ← body.bindConstructors? source
    (sites.map fun (pc, _, callee, _) => (pc, ⟨[], callee, ⟨coreLibraryScope⟩⟩))
    image.dependencies
  let code ← (checkBody bound source []).toOption
  let raw := { source with
    code := code.code, initLocals := code.initLocals, handlers := code.handlers }
  let targets := branchTargets raw.code
  -- Every entry to each newobj runs its loads, so the message is a string literal.
  guard (sites.all fun (pc, loads, _, _) =>
    let start := pc - loads.length
    pc ≥ loads.length && !targets.contains pc &&
      loads.zipIdx.all fun (opcode, offset) =>
        (raw.code[start + offset]?.map (·.opcode)) == some opcode &&
          !targets.contains (start + offset + 1))
  let links := sites.map fun (pc, _, callee, ordinal) =>
    (pc, Link.object ordinal callee.objectBases (objectFieldOffset callee.objectFieldCount))
  return ⟨bound, raw, links⟩

/-- The image's executable definitions and getter declarations, in the program that places
`locals` first. Each definition uses the pins, platform and layouts of `caller`. -/
def ConstructorImage.rows? (image : ConstructorImage) (locals : List SpecializedMethod)
    (caller : BodyEvidence) (profile : FeatureProfile) (environment : LayoutEnvironment) :
    Option (List (MethodEvidence × Method) × List MethodEvidence) := do
  let runtime := image.methods.map Prod.snd ++ image.getters.map (·.raw)
  let table := locals ++ runtime.map (⟨[], ·, ⟨coreLibraryScope⟩⟩)
  let definitions ← image.methods.mapM (runtimeRow? table caller profile environment)
  let declarations ← image.getters.mapM (resourceDeclaration? caller environment)
  return (definitions, declarations)

/-- Decode a single entry method and the framework methods reached with a non-null message.
The caller must resolve its constructor through the two pinned runtime slices. -/
def constructorImage? (item : ConstructorSource) (pc : Nat)
    (profile : FeatureProfile) (environment : LayoutEnvironment) : Option ManagedPackage := do
  guard (supportsProfile profile && item.arguments.isEmpty)
  let site ← item.original.code[pc]?
  let .call constructor := site.operand | none
  let image ← ConstructorImage.of?
    [(← exceptionConstructor? constructor, constructor.parameterTypes)]
  let bound ← image.bindCaller? 1 item.body item.original [pc]
  let raw := bound.original
  -- This single-entry image supplies only the constructor at the selected call site.
  guard (raw.code.zipIdx.all fun (site, index) =>
    match site.operand with | .call _ => index == pc | _ => true)
  let entry ← Method.ofBody? profile environment bound.links item.reachable bound.body raw []
  let closed ← instantiateMethod environment.rawLayouts raw []
  let storage ← closedArguments environment.rawLayouts closed
  let (_, scalars) ← inferFlow? closed entry (some item.featureStates)
  let caller : MethodEvidence := {
    original := raw, body := bound.body, closed, parameterInput := storage, links := bound.links,
    scalarStates := scalars, arguments := item.arguments, reachable := item.reachable,
    featureStates := item.featureStates, layoutUses := item.layoutUses,
    dispatchTypes := item.dispatchTypes, assembly := item.assembly, signature := item.signature }
  let own : SpecializedMethod := ⟨[], raw, ⟨bound.body.metadata.own.assembly.identity⟩⟩
  let (definitions, declarations) ← image.rows? [own] bound.body profile environment
  return ⟨(caller, entry), definitions, declarations⟩

/-- The pins every package body shares: the source assemblies and CoreLib. The forwarding facade
is carried as a slice of each bound caller and stays unpinned. -/
def packagePins (source : List AssemblyPin) : List AssemblyPin :=
  source ++ [⟨coreLibraryScope⟩]

/-- Bind the unique live exception constructor in a closed single-caller extraction. -/
def constructorPackage? (source : ConstructorSource) (imports : List ImportSlot)
    (profile : FeatureProfile) (environment : LayoutEnvironment) : Option ManagedPackage := do
  guard imports.isEmpty
  let [pc] := source.sites | none
  constructorImage? source pc profile environment

/-- Check the executable prefix and its declarations against the extraction's physical inputs. -/
def checkPackage? (package : ManagedPackage) (environment : LayoutEnvironment)
    (pins : List AssemblyPin) (platform : PlatformTable) :
    Option {p : ManagedPackage // p.checked environment (packagePins pins) platform} :=
  if valid : package.checked environment (packagePins pins) platform then some ⟨package, valid⟩
  else none

end CIL.Runtime.Net11WinX64
