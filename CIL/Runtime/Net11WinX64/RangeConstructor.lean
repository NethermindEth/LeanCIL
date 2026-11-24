import CIL.Runtime.Net11WinX64.RangeMethods

/-! Managed execution of the two-string range exception constructor in the .NET 11.0.0
Windows x64 runtime. The resource getter on the null-message branch occupies the first
import slot after the local methods. -/

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
def rangeDependencies : List MetadataSlice := [{
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
        (100666618, (fixedBytes 20 0x000000000000861801000000010000002F190000)),
        (704643224, (fixedBytes 12 0x00002200D0010000FFFFFFFF)),
        (704643225, (fixedBytes 12 0x00000000EE010000FFFFFFFF))],
      strings := [(1, (fixedBytes 6 0x2E63746F7200)), (2, (fixedBytes 18 0x417267756D656E74457863657074696F6E00)),
        (3, (fixedBytes 28 0x417267756D656E744F75744F6652616E6765457863657074696F6E00)),
        (4, (fixedBytes 7 0x4F626A65637400)), (5, (fixedBytes 7 0x53797374656D00))],
      blobs := [(1, (fixedBytes 6 0x052002010E0E))],
      userStrings := [],
      corlib := 0,
      links := [⟨1, 100666618, 2, 33554675⟩]}]

/-- Physical bodies reached by the constructor with a non-null message argument. -/
def coreBytes : List (BodyEvidence × RawMethod) := [
    ({ RangeCtor.body with names := RangeCtor.names }, RangeCtor.definition),
    ({ ArgumentCtor.body with names := ArgumentCtor.names }, ArgumentCtor.definition),
    ({ SystemExceptionCtor.body with names := SystemExceptionCtor.names }, SystemExceptionCtor.definition),
    ({ ExceptionMessageCtor.body with names := ExceptionMessageCtor.names }, ExceptionMessageCtor.definition),
    ({ ExceptionCtor.body with names := ExceptionCtor.names }, ExceptionCtor.definition),
    ({ ObjectCtor.body with names := ObjectCtor.names }, ObjectCtor.definition),
    ({ SetHResult.body with names := SetHResult.names }, SetHResult.definition)]

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

/-- The physical getter reached only by the null-message branch of the constructor. -/
def rangeResourceImport : SpecializedMethod := ⟨[], RangeResource.raw, ⟨coreLibraryScope⟩⟩

/-- The caller and executable runtime bodies, their original literal operands and the
remaining managed import, whose index follows the last executable body. -/
structure RangeImage where
  caller : MethodEvidence
  methods : Program
  originals : List RawMethod
  resourceImport : SpecializedMethod

/-- The scalar and x64 execution profiles with the runtime image's pointer width and byte order. -/
def supportsProfile (profile : FeatureProfile) : Bool :=
  profile.nativeWidth == 64 && profile.littleEndian && profile.architecture != .arm64

/-- Infer the incoming scalar stacks of the rebound caller from its original instructions.
Each reachable pc enters the queue once. Incoming edges must agree on the stack kinds. -/
private def callerScalars? (raw : RawMethod) (features : FeatureCertificate)
    (method : Method) : Option ScalarCertificate := do
  let sites := (raw.code.zip (foldRoles raw.code)).toArray
  let facts := features.toArray
  let code := method.code.toArray
  guard (sites.size > 0 && facts.size == sites.size && code.size == sites.size)
  let context := nativeDispatchContext raw
  let locals := ScalarLocals.indexed raw context
  let rec visit : Nat → List Nat → Array (Option (List ScalarKind)) → Option ScalarCertificate
    | _, [], states => some states.toList
    | 0, _ :: _, _ => none
    | fuel + 1, pc :: pending, states => do
      let (op, role) ← sites[pc]?
      let some stack ← states[pc]? | none
      let some feature ← facts[pc]? | none
      let emitted ← code[pc]?
      if scalarStoreFault raw op stack emitted locals then return ← visit fuel pending states
      let after ← scalarTransfer raw op stack role context locals
      let next ← featureSuccessors role pc op feature.stack
      let mut todo := pending
      let mut incoming := states
      for target in next do
        match ← incoming[target]? with
        | some known => guard (known == after)
        | none =>
          incoming := incoming.set! target (some after)
          todo := target :: todo
      visit fuel todo incoming
  let states ← visit sites.size [0] ((Array.replicate sites.size none).set! 0 (some []))
  guard (decide (ScalarFlowValid raw features states method.code))
  return states

/-- Decode a single entry method and the seven framework methods reached with a non-null
message. The caller must resolve its constructor through the two pinned runtime slices. -/
def rangeImage? (item : MethodEvidence) (pc : Nat)
    (profile : FeatureProfile) (environment : LayoutEnvironment) : Option RangeImage := do
  guard (supportsProfile profile && item.arguments.isEmpty)
  let original := item.body
  let source := item.original
  let body ← original.bindConstructor? source pc rangeDependencies
    ⟨[], RangeCtor.definition, ⟨coreLibraryScope⟩⟩
  let code ← (checkBody body source []).toOption
  let raw := { source with code := code.code, initLocals := code.initLocals }
  -- Every entry to this newobj must load the message immediately before the allocation.
  let prior ← raw.code[pc - 1]?
  guard (pc > 0 && prior.opcode == 0x72 && !(branchTargets raw.code).contains pc)
  -- This single-entry image supplies only the range constructor at the selected call site.
  guard (raw.code.zipIdx.all fun (site, index) =>
    match site.operand with | .call _ => index == pc | _ => true)
  let runtime := coreBytes.map Prod.snd
  let table : List SpecializedMethod := ⟨[], raw, ⟨original.metadata.own.assembly.identity⟩⟩ ::
    (runtime.map (⟨[], ·, ⟨coreLibraryScope⟩⟩) ++ [rangeResourceImport])
  let boundLinks := links table raw
  let entry ← Method.ofBody? profile environment boundLinks item.reachable body raw []
  let closed ← instantiateMethod environment.rawLayouts raw []
  let storage ← closedArguments environment.rawLayouts closed
  let scalars ← callerScalars? closed item.featureStates entry
  let caller := { item with
    original := raw, body, closed, parameterInput := storage, links := boundLinks,
    scalarStates := scalars }
  let constructors ← coreBytes.mapM fun (evidence, method) =>
    Method.ofBody? .scalar {} (links table method)
      (List.replicate method.code.length true) evidence method []
  return ⟨caller, entry :: constructors, raw :: runtime, rangeResourceImport⟩

end CIL.Runtime.Net11WinX64
