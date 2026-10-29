import CIL.Extraction.Features
import Std.Data.TreeSet.Lemmas
import Lean.Elab.Tactic.BuiltinTactic

/-!
# Exact vector calls and opaque vector locals

`DivisionIntrinsicsValid` checks selected hardware calls used by vectorized division and
lane-independent portable integer vector calls. Each covered call requires exact raw metadata
and the matching emitted intrinsic, available under the method's profile. Other intrinsic
families retain their existing extraction checks.

`Vector128.CreateScalarUnsafe` leaves the upper half of its result unspecified, so a
method that uses it keeps eligible `Vector128<ulong>` locals as opaque whole values rather
than bytes; `OpaqueLocalsValid` fixes that set from the raw body.

Signature strings below use string gaps, so each literal is one unbroken identity.
-/

namespace CIL.Extraction

/-- Each admitted intrinsic: owner class, method name, full signature, emitted intrinsic and
    arity. -/
private def divisionSignatures : List (String × String × String × Intrinsic × Nat) := [
  ("System.Runtime.Intrinsics.X86.Avx2", "And",
    "System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
      System.Runtime.Intrinsics.X86.Avx2::And(\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>)",
    .avx2 .band, 2),
  ("System.Runtime.Intrinsics.X86.Avx2", "Or",
    "System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
      System.Runtime.Intrinsics.X86.Avx2::Or(\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>)",
    .avx2 .bor, 2),
  ("System.Runtime.Intrinsics.X86.Avx2", "Xor",
    "System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
      System.Runtime.Intrinsics.X86.Avx2::Xor(\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>)",
    .avx2 .bxor, 2),
  ("System.Runtime.Intrinsics.X86.Avx2", "AndNot",
    "System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
      System.Runtime.Intrinsics.X86.Avx2::AndNot(\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>)",
    .avx2 .andNot, 2),
  ("System.Runtime.Intrinsics.X86.Avx2", "ShiftLeftLogical",
    "System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
      System.Runtime.Intrinsics.X86.Avx2::ShiftLeftLogical(\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
      System.Runtime.Intrinsics.Vector128`1<System.UInt64>)",
    .avx2 .shl64Count, 2),
  ("System.Runtime.Intrinsics.X86.Avx2", "ShiftRightLogical",
    "System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
      System.Runtime.Intrinsics.X86.Avx2::ShiftRightLogical(\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
      System.Runtime.Intrinsics.Vector128`1<System.UInt64>)",
    .avx2 .shr64Count, 2),
  ("System.Runtime.Intrinsics.X86.Avx512F", "CompareLessThan",
    "System.Runtime.Intrinsics.Vector512`1<System.UInt64> \
      System.Runtime.Intrinsics.X86.Avx512F::CompareLessThan(\
      System.Runtime.Intrinsics.Vector512`1<System.UInt64>,\
      System.Runtime.Intrinsics.Vector512`1<System.UInt64>)",
    .avx512 .ltu512, 2),
  ("System.Runtime.Intrinsics.X86.Avx512F", "CompareGreaterThan",
    "System.Runtime.Intrinsics.Vector512`1<System.UInt64> \
      System.Runtime.Intrinsics.X86.Avx512F::CompareGreaterThan(\
      System.Runtime.Intrinsics.Vector512`1<System.UInt64>,\
      System.Runtime.Intrinsics.Vector512`1<System.UInt64>)",
    .avx512 .gtu512, 2),
  ("System.Runtime.Intrinsics.X86.Avx512DQ", "MoveMask",
    "System.Int32 \
      System.Runtime.Intrinsics.X86.Avx512DQ::MoveMask(\
      System.Runtime.Intrinsics.Vector512`1<System.UInt64>)",
    .avx512DQ .moveMask512, 1),
  ("System.Runtime.Intrinsics.Vector512", "Create",
    "System.Runtime.Intrinsics.Vector512`1<System.UInt64> \
      System.Runtime.Intrinsics.Vector512::Create(\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>,\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>)",
    .vector .combine256, 2),
  ("System.Runtime.Intrinsics.Vector128", "CreateScalarUnsafe",
    "System.Runtime.Intrinsics.Vector128`1<System.UInt64> \
      System.Runtime.Intrinsics.Vector128::CreateScalarUnsafe(System.UInt64)",
    .vector .createScalarUnsafe64, 1),
  ("System.Runtime.Intrinsics.X86.Avx2", "ShiftLeftLogical",
    "System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
      System.Runtime.Intrinsics.X86.Avx2::ShiftLeftLogical(\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)",
    .avx2 .shl64, 2),
  ("System.Runtime.Intrinsics.X86.Avx2", "ShiftRightLogical",
    "System.Runtime.Intrinsics.Vector256`1<System.UInt64> \
      System.Runtime.Intrinsics.X86.Avx2::ShiftRightLogical(\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)",
    .avx2 .shr64, 2),
  ("System.Runtime.Intrinsics.X86.Avx512DQ", "MoveMask",
    "System.Int32 \
      System.Runtime.Intrinsics.X86.Avx512DQ::MoveMask(\
      System.Runtime.Intrinsics.Vector256`1<System.UInt64>)",
    .avx512DQ .moveMask64, 1)]

/-- `Vector{width}<ulong>` with exact scopes. -/
private def divisionVector (width : String) : TypeExpr :=
  .apply (.constructor intrinsicsScope ("System.Runtime.Intrinsics.Vector" ++ width ++ "`1"))
    (.atom runtimeScope "System.UInt64")

/-- The return and parameter types each admitted intrinsic's call site must declare. -/
private def divisionCallTypes : Intrinsic → Option (TypeExpr × List TypeExpr)
  | .avx2 .band | .avx2 .bor | .avx2 .bxor | .avx2 .andNot =>
    some (divisionVector "256", [divisionVector "256", divisionVector "256"])
  | .avx2 .shl64Count | .avx2 .shr64Count =>
    some (divisionVector "256", [divisionVector "256", divisionVector "128"])
  | .avx2 .shl64 | .avx2 .shr64 =>
    some (divisionVector "256", [divisionVector "256", .atom runtimeScope "System.Byte"])
  | .avx512 .ltu512 | .avx512 .gtu512 =>
    some (divisionVector "512", [divisionVector "512", divisionVector "512"])
  | .avx512DQ .moveMask512 => some (.atom runtimeScope "System.Int32", [divisionVector "512"])
  | .avx512DQ .moveMask64 => some (.atom runtimeScope "System.Int32", [divisionVector "256"])
  | .vector .combine256 => some (divisionVector "512", [divisionVector "256", divisionVector "256"])
  | .vector .createScalarUnsafe64 =>
    some (divisionVector "128", [.atom runtimeScope "System.UInt64"])
  | _ => none

/-- Lane-independent integer operations share vector semantics at either supported width. -/
private def portableVectorOperation (name : String) (width : Nat) :
    Option (Intrinsic × Nat) :=
  match name with
  | "op_BitwiseAnd" => some (.vector (.band width), 2)
  | "op_BitwiseOr" => some (.vector (.bor width), 2)
  | "op_ExclusiveOr" => some (.vector (.bxor width), 2)
  | "op_OnesComplement" => some (.vector (.bnot width), 1)
  | "op_Equality" | "EqualsAll" => some (.vector (.equalsAll width), 2)
  | "get_Zero" => some (.vector (.zero width), 0)
  | "get_AllBitsSet" => some (.vector (.ones width), 0)
  | _ => none

/-- Exact portable vector calls retain their integer element, width, types and generic identity. -/
private def portableVectorIntrinsic (instruction : RawInstruction) : Option (Intrinsic × Nat) := do
  if instruction.opcode != 40 then none else pure ()
  let .call site := instruction.operand | none
  if site.hasThis || !site.returnsValue || site.ownerArgumentCount != 0 then none else pure ()
  let isStatic := site.name == "EqualsAll"
  let vector ← if isStatic then
      match site.declaringType, site.typeArguments with
      | .atom scope owner, [element] =>
        if scope != intrinsicsScope then none
        else some (TypeExpr.apply (.constructor scope (owner ++ "`1")) element)
      | _, _ => none
    else if site.typeArguments.isEmpty then some site.declaringType else none
  let bytes ← integerVectorWidth vector
  if bytes != 16 && bytes != 32 then none else pure ()
  let (intrinsic, arity) ← portableVectorOperation site.name (bytes * 8)
  let .apply (.constructor _ owner) (.atom _ element) := vector | none
  let staticOwner := "System.Runtime.Intrinsics.Vector" ++ toString (bytes * 8)
  let parameterName := owner ++ (if isStatic then "<!!0>" else "<!0>")
  let equality := site.name == "op_Equality" || isStatic
  let result := if equality then TypeExpr.atom runtimeScope "System.Boolean" else vector
  let resultName := if equality then "System.Boolean" else parameterName
  let declaringName := if isStatic then staticOwner else owner ++ "<" ++ element ++ ">"
  let signature := resultName ++ " " ++ declaringName ++ "::" ++ site.name ++ "(" ++
    String.intercalate "," (List.replicate arity parameterName) ++ ")"
  if site.parameterCount != arity || site.parameterTypes != List.replicate arity vector ||
      site.returnType != result || site.target != .external (intrinsicsScope ++ "::" ++ signature)
    then none else some (intrinsic, arity)

/-- Owner names reserve portable vector calls even when their metadata is malformed. -/
private def portableVectorOwner (owner : String) : Bool :=
  owner == "System.Runtime.Intrinsics.Vector128" ||
  owner == "System.Runtime.Intrinsics.Vector256" ||
  owner.startsWith "System.Runtime.Intrinsics.Vector128`1" ||
  owner.startsWith "System.Runtime.Intrinsics.Vector256`1"

/-- The intrinsic and arity of an exact admitted call, including its generic types and identity. -/
def divisionIntrinsic (instruction : RawInstruction) : Option (Intrinsic × Nat) :=
  portableVectorIntrinsic instruction <|> do
  if instruction.opcode != 40 then none else
  let .call site := instruction.operand | none
  if site.hasThis || !site.returnsValue || !site.typeArguments.isEmpty then none else
  let (_, _, _, intrinsic, arity) ←
    divisionSignatures.find? fun (owner, name, signature, _, arity) =>
      site.name == name && site.parameterCount == arity &&
      site.declaringType == .atom intrinsicsScope owner &&
      site.target == .external (intrinsicsScope ++ "::" ++ signature)
  let (returnType, parameterTypes) ← divisionCallTypes intrinsic
  if site.returnType != returnType || site.parameterTypes != parameterTypes then none else
  return (intrinsic, arity)

/-- Checking names and arities first preserves the original admitted-signature lookup and metadata
    checks, without any assumptions on the raw instruction. -/
theorem divisionIntrinsic_eq_original (instruction : RawInstruction) :
    divisionIntrinsic instruction = (portableVectorIntrinsic instruction <|> do
      if instruction.opcode != 40 then none else
      let .call site := instruction.operand | none
      if site.hasThis || !site.returnsValue || !site.typeArguments.isEmpty then none else
      let (_, _, _, intrinsic, arity) ←
        divisionSignatures.find? fun (owner, name, signature, _, arity) =>
          site.declaringType == .atom intrinsicsScope owner && site.name == name &&
          site.parameterCount == arity &&
          site.target == .external (intrinsicsScope ++ "::" ++ signature)
      let (returnType, parameterTypes) ← divisionCallTypes intrinsic
      if site.returnType != returnType || site.parameterTypes != parameterTypes then none else
      return (intrinsic, arity)) := by
  simp only [divisionIntrinsic, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
#print axioms divisionIntrinsic_eq_original

/-- The exact UTF-8 bytes of an identity, including non-ASCII metadata. -/
private def identityBytes (identity : String) : List UInt8 :=
  identity.toByteArray.data.toList

/-- Signature bytes materialized once; the kernel checks their equality to the signature table. -/
private def divisionSignatureBytes : List (String × String × List UInt8) := by
  run_tac do
    let expression ← Lean.Elab.Term.elabTerm
      (← `(divisionSignatures.map fun (owner, name, signature, _, _) =>
        (owner, name, identityBytes signature))) none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← Lean.instantiateMVars expression
    let values ← unsafe Lean.Meta.evalExpr (List (String × String × List UInt8))
      (← Lean.Meta.inferType expression) expression
    Lean.Elab.Tactic.closeMainGoal `divisionSignatureBytes (Lean.toExpr values)

set_option maxRecDepth 4096 in
/-- The materialized bytes contain exactly the original signatures and owner/name metadata. -/
private theorem divisionSignatureBytes_eq : divisionSignatureBytes =
    divisionSignatures.map (fun (owner, name, signature, _, _) =>
      (owner, name, identityBytes signature)) := by
  decide +kernel
#print axioms divisionSignatureBytes_eq

/-- Remove an exact byte prefix, rejecting mismatches and truncated identities. -/
private def stripIdentityPrefix : List UInt8 → List UInt8 → Option (List UInt8)
  | [], bytes => some bytes
  | first :: expected, actual :: bytes =>
    if first == actual then stripIdentityPrefix expected bytes else none
  | _, _ => none

/-- Prefix removal succeeds exactly for the original prefix followed by the returned bytes. -/
private theorem stripIdentityPrefix_eq (expected bytes suffix : List UInt8) :
    stripIdentityPrefix expected bytes = some suffix ↔ bytes = expected ++ suffix := by
  induction expected generalizing bytes with
  | nil => simp [stripIdentityPrefix]
  | cons first expected ih =>
    cases bytes with
    | nil => simp [stripIdentityPrefix]
    | cons actual bytes =>
      by_cases equal : first = actual
      · subst actual
        simp [stripIdentityPrefix, ih]
      · simp [stripIdentityPrefix, equal, beq_iff_eq, Ne.symm equal]
#print axioms stripIdentityPrefix_eq

/-- The unqualified signature of an external target under the exact intrinsic scope. -/
private def intrinsicSignature (target : MethodId) : Option (List UInt8) :=
  match target with
  | .managed _ => none
  | .external identity =>
    stripIdentityPrefix (identityBytes (intrinsicsScope ++ "::")) (identityBytes identity)

/-- Removing the common scope preserves exact external identity equality. -/
private theorem intrinsicSignature_matches (target : MethodId) (signature : String) :
    (intrinsicSignature target == some (identityBytes signature)) =
      (target == .external (intrinsicsScope ++ "::" ++ signature)) := by
  apply Bool.eq_iff_iff.mpr
  cases target with
  | managed token => simp [intrinsicSignature, beq_iff_eq]
  | external identity =>
    simp only [intrinsicSignature, beq_iff_eq, stripIdentityPrefix_eq, MethodId.external.injEq]
    simp only [identityBytes]
    rw [← ByteArray.toList_data_append, ← String.toByteArray_append, Array.toList_inj]
    constructor
    · intro equal
      exact String.toByteArray_inj.mp (ByteArray.ext equal)
    · intro equal
      cases equal
      rfl
#print axioms intrinsicSignature_matches

/-- Split one metadata identity separator without decoding byte-backed strings. -/
private def splitIdentityOwner : List UInt8 → List UInt8 × List UInt8
  -- ASCII ':' separates the assembly, owner and member identities.
  | 58 :: 58 :: tail => ([], tail)
  | head :: tail =>
    let (owner, member) := splitIdentityOwner tail
    (head :: owner, member)
  | [] => ([], [])

/-- Family recognition uses both structured metadata and the independently supplied target. -/
private def portableVectorFamily (instruction : RawInstruction) : Bool :=
  match instruction.operand with
  | .call site =>
    let owner := match site.declaringType with
      | .atom _ owner | .apply (.constructor _ owner) _ => owner
      | _ => ""
    (portableVectorOwner owner && (portableVectorOperation site.name 128).isSome) ||
      match intrinsicSignature site.target with
      | some signature =>
        let (signatureOwner, member) := splitIdentityOwner signature
        -- ASCII space ends the return type; '<' begins type arguments and '(' begins parameters.
        let owner := (signatureOwner.reverse.takeWhile (· != 32)).reverse.takeWhile (· != 60)
        let name := member.takeWhile (· != 40)
        (["System.Runtime.Intrinsics.Vector128", "System.Runtime.Intrinsics.Vector256",
          "System.Runtime.Intrinsics.Vector128`1", "System.Runtime.Intrinsics.Vector256`1"].any
          (fun expected => owner == identityBytes expected)) &&
        (["op_BitwiseAnd", "op_BitwiseOr", "op_ExclusiveOr", "op_OnesComplement", "op_Equality",
          "EqualsAll", "get_Zero", "get_AllBitsSet"].any
          (fun expected => name == identityBytes expected))
      | none => false
  | _ => false

/-- A call that resembles an admitted entry by identity, or by owner and name; such a call
    must then match an entry exactly. -/
private def divisionCallFamily (instruction : RawInstruction) : Bool :=
  portableVectorFamily instruction || match instruction.operand with
  | .call site => match intrinsicSignature site.target with
    | none => divisionSignatures.any fun (owner, name, _, _, _) =>
        site.name == name && match site.declaringType with
          | .atom _ declared => declared == owner
          | _ => false
    | some signature => divisionSignatureBytes.any fun (owner, name, expected) =>
        (some signature == some expected) ||
        site.name == name && match site.declaringType with
          | .atom _ declared => declared == owner
          | _ => false
  | _ => false

/-- Sharing scope removal preserves family recognition by either full identity or owner/name. -/
private theorem divisionCallFamily_eq_original (instruction : RawInstruction) :
    divisionCallFamily instruction = (portableVectorFamily instruction ||
      match instruction.operand with
      | .call site => divisionSignatures.any fun (owner, name, signature, _, _) =>
          site.target == .external (intrinsicsScope ++ "::" ++ signature) ||
          site.name == name && match site.declaringType with
            | .atom _ declared => declared == owner
            | _ => false
      | _ => false) := by
  cases operand : instruction.operand <;> simp only [divisionCallFamily, operand]
  rename_i site
  cases signature : intrinsicSignature site.target <;>
    simp [divisionSignatureBytes_eq, List.any_map, Function.comp_def,
      ← intrinsicSignature_matches, signature]
#print axioms divisionCallFamily_eq_original

/-- The intrinsic and arity of an emitted admitted intrinsic. -/
def emittedDivisionIntrinsic : Op → Option (Intrinsic × Nat)
  | .intrinsic intrinsic arity => match intrinsic with
    | .avx2 .band | .avx2 .bor | .avx2 .bxor | .avx2 .andNot
    | .avx2 .shl64Count | .avx2 .shr64Count | .avx2 .shl64 | .avx2 .shr64
    | .avx512 .ltu512 | .avx512 .gtu512
    | .avx512DQ .moveMask512 | .avx512DQ .moveMask64 | .vector .combine256
    | .vector .createScalarUnsafe64
    | .vector (.band _) | .vector (.bor _) | .vector (.bxor _) | .vector (.bnot _)
    | .vector (.equalsAll _) | .vector (.zero _) | .vector (.ones _) => some (intrinsic, arity)
    | _ => none
  | _ => none

/-- An emitted division intrinsic must match the raw call and be available. Other emitted
    operations must not replace a call in the admitted family, including malformed calls. -/
private def divisionSiteMatches (profile : FeatureProfile) (raw : RawInstruction)
    (emitted : Op) : Bool :=
  match emittedDivisionIntrinsic emitted with
  | none => !divisionCallFamily raw
  | some expected => match divisionIntrinsic raw with
    | none => false
    | some actual => decide (actual = expected) && Intrinsic.available profile expected.1

/-- Dispatching on the emitted operation preserves every original site check, including
    malformed raw metadata, arity mismatches and unavailable intrinsics. -/
private theorem divisionSiteMatches_eq (profile : FeatureProfile) (raw : RawInstruction)
    (emitted : Op) :
    divisionSiteMatches profile raw emitted =
      ((if divisionCallFamily raw || (emittedDivisionIntrinsic emitted).isSome then
        (divisionIntrinsic raw).isSome &&
          decide (divisionIntrinsic raw = emittedDivisionIntrinsic emitted)
       else true) &&
      match emittedDivisionIntrinsic emitted with
      | some (intrinsic, _) => Intrinsic.available profile intrinsic
      | none => true) := by
  cases emittedResult : emittedDivisionIntrinsic emitted with
  | none =>
    cases rawResult : divisionIntrinsic raw <;> cases family : divisionCallFamily raw <;>
      simp [divisionSiteMatches, emittedResult, family]
  | some expected =>
    rcases expected with ⟨intrinsic, arity⟩
    cases rawResult : divisionIntrinsic raw <;>
      simp [divisionSiteMatches, emittedResult, rawResult]

#print axioms divisionSiteMatches_eq

/-- The profile is valid, the three lists have equal length, and at every live pc a
    resembling call or an emitted admitted intrinsic requires an exact match between the two,
    and every emitted one is available under the profile. -/
def DivisionIntrinsicsValid (closed : RawMethod) (reachable : List Bool) (method : Method) :
    Prop :=
  method.profile.Valid ∧ closed.code.length = reachable.length ∧
    closed.code.length = method.code.length ∧
  all3 (fun raw live emitted => !live || divisionSiteMatches method.profile raw emitted)
    closed.code reachable method.code = true

/-- The optimized validator is equivalent to the original signature-family, exact-call
    and availability rules for all inputs, including unequal certificate lengths. -/
theorem DivisionIntrinsicsValid_iff_original (closed : RawMethod) (reachable : List Bool)
    (method : Method) :
    DivisionIntrinsicsValid closed reachable method ↔
    let classify := fun instruction : RawInstruction => (portableVectorIntrinsic instruction <|> do
      if instruction.opcode != 40 then none else
      let .call site := instruction.operand | none
      if site.hasThis || !site.returnsValue || !site.typeArguments.isEmpty then none else
      let (_, _, _, intrinsic, arity) ←
        divisionSignatures.find? fun (owner, name, signature, _, arity) =>
          site.declaringType == .atom intrinsicsScope owner && site.name == name &&
          site.parameterCount == arity &&
          site.target == .external (intrinsicsScope ++ "::" ++ signature)
      let (returnType, parameterTypes) ← divisionCallTypes intrinsic
      if site.returnType != returnType || site.parameterTypes != parameterTypes then none else
      return (intrinsic, arity))
    let family := fun instruction : RawInstruction =>
      portableVectorFamily instruction || match instruction.operand with
      | .call site => divisionSignatures.any fun (owner, name, signature, _, _) =>
          site.target == .external (intrinsicsScope ++ "::" ++ signature) ||
          site.name == name && match site.declaringType with
            | .atom _ declared => declared == owner
            | _ => false
      | _ => false
    method.profile.Valid ∧ closed.code.length = reachable.length ∧
    closed.code.length = method.code.length ∧
    all3 (fun raw live emitted => !live ||
    (if family raw || (emittedDivisionIntrinsic emitted).isSome then
      (classify raw).isSome && decide (classify raw = emittedDivisionIntrinsic emitted)
     else true) &&
    match emittedDivisionIntrinsic emitted with
    | some (intrinsic, _) => Intrinsic.available method.profile intrinsic
    | none => true) closed.code reachable method.code = true := by
  simp only [DivisionIntrinsicsValid, divisionSiteMatches_eq, divisionIntrinsic_eq_original,
    divisionCallFamily_eq_original]

#print axioms DivisionIntrinsicsValid_iff_original

instance (closed : RawMethod) (reachable : List Bool) (method : Method) :
    Decidable (DivisionIntrinsicsValid closed reachable method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Whether a raw local is the whole-vector type eligible for opaque storage. -/
private def opaqueLocalType : Option TypeExpr → Bool
  | some (.apply (.constructor scope "System.Runtime.Intrinsics.Vector128`1")
      (.atom elementScope "System.UInt64")) =>
    scope == intrinsicsScope && elementScope == runtimeScope
  | _ => false

/-- Every eligible local, in index order; addresses are taken by `ldloca` (18 or 0xFE0D). -/
def opaqueLocalIndices (closed : RawMethod) : List Nat :=
  let addressed := Std.TreeSet.ofList (closed.code.filterMap fun instruction =>
    if instruction.opcode == 18 || instruction.opcode == 65037 then localIndex instruction else none)
  ((closed.locals.zipIdx).filter fun (type, index) =>
    opaqueLocalType (some type) && !addressed.contains index).map Prod.snd

/-- Indexed opaque-local discovery agrees with direct local lookup and address membership. -/
theorem opaqueLocalIndices_eq_scan (closed : RawMethod) :
    opaqueLocalIndices closed = (List.range closed.locals.length).filter (fun index =>
      (match (closed.locals[index]? : Option TypeExpr) with
      | some (.apply (.constructor scope "System.Runtime.Intrinsics.Vector128`1")
          (.atom elementScope "System.UInt64")) =>
        scope == intrinsicsScope && elementScope == runtimeScope
      | _ => false) && !(closed.code.filterMap (fun instruction =>
        if instruction.opcode == 18 || instruction.opcode == 65037 then localIndex instruction
        else none)).contains index) := by
  simp only [opaqueLocalIndices, Std.TreeSet.contains_ofList]
  rw [List.range_eq_range', ← List.zipIdx_map_snd 0 closed.locals, List.filter_map]
  congr 1
  apply List.filter_congr
  intro entry present
  have found := List.mem_zipIdx_iff_getElem?.mp present
  simp only [Function.comp_def, found]
  rfl

#print axioms opaqueLocalIndices_eq_scan
/-- Every claimed opaque local has the emitted whole-vector slot kind. -/
private def opaqueKindsValid (method : Method) : Bool :=
  let kinds := FlowIndex.ofList method.localKinds
  method.opaqueVectorLocals.all fun index => kinds.get? index == some .vector128

/-- No emitted address operation exposes an opaque local's unspecified bytes. -/
private def opaqueAddressesValid (method : Method) : Bool :=
  let slots := Std.TreeSet.ofList method.opaqueVectorLocals
  method.code.all fun operation => match operation with
    | .localAddr index => !slots.contains index
    | _ => true
/-- The opaque locals are exactly the eligible ones when the method uses
    `CreateScalarUnsafe` and none otherwise; each is a 128-bit vector slot whose address the
    emitted code never takes. -/
def OpaqueLocalsValid (closed : RawMethod) (method : Method) : Prop :=
  method.opaqueVectorLocals = (if method.code.any (fun op =>
    match op with
    | .intrinsic (.vector .createScalarUnsafe64) _ => true
    | _ => false) then opaqueLocalIndices closed else []) ∧
  opaqueKindsValid method = true ∧ opaqueAddressesValid method = true

/-- Indexed opaque-local checks preserve the original kind and no-address obligations. -/
theorem OpaqueLocalsValid_iff_scan (closed : RawMethod) (method : Method) :
    OpaqueLocalsValid closed method ↔
      method.opaqueVectorLocals = (if method.code.any (fun op => match op with
        | .intrinsic (.vector .createScalarUnsafe64) _ => true
        | _ => false) then opaqueLocalIndices closed else []) ∧
      method.opaqueVectorLocals.all (fun index => method.localKinds[index]? == some .vector128) =
        true ∧
      method.code.all (fun operation => match operation with
        | .localAddr index => !(index ∈ method.opaqueVectorLocals)
        | _ => true) = true := by
  simp only [OpaqueLocalsValid, opaqueKindsValid, opaqueAddressesValid,
    FlowIndex.get?_ofList, Std.TreeSet.contains_ofList, List.contains_eq_mem]

#print axioms OpaqueLocalsValid_iff_scan
instance (closed : RawMethod) (method : Method) : Decidable (OpaqueLocalsValid closed method) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end CIL.Extraction
