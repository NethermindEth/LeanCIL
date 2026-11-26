import CIL.Extraction.DecodedMethod
import Tests.Support.RawDecoding

/-! Decoder, operand binding and execution checks for the eight Unsafe block overloads. -/

namespace Tests.UnsafeBlocks
open CIL CIL.Extraction

/-- A MemberRef for a block helper as it occurs in the example assembly. -/
private def site (name : String) (key : MetadataName) (copy pointer : Bool) : CallSite :=
  let byte := TypeExpr.primitive .byte
  let address := if pointer then TypeExpr.pointer .void else .byref byte
  let addressText := if pointer then "System.Void*" else "System.Byte&"
  let second := if copy then addressText else "System.Byte"
  let owner := "System.Runtime.CompilerServices.Unsafe"
  let types := s!"{addressText},{second},System.UInt32"
  let parameters := [address, if copy then address else byte, .primitive .uint32]
  let method : MethodRef :=
    { owner := .atom runtimeScope owner .classType, name := key, hasThis := false,
      genericArity := 0, returnType := .void, parameters }
  { method, name, declared := { convention := 0, parameters },
    target := .external s!"{runtimeScope}::System.Void {owner}::{name}({types})",
    typeArguments := [], parameterCount := 3, returnsValue := false }

/-- The live instruction reconstructed from the raw call. -/
private def decoded (call : CallSite) :=
  let raw : RawMethod :=
    { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
      attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
      initLocals := true, maxStack := 3, genericParameters := [], code := [⟨0, 40, .call call⟩] }
  (decodeRaw .scalar {} [] [true] raw []).map Method.code

/-- Each overload with the copy or fill operation and alignment required by its declaration. -/
private def cases : List (CallSite × MemoryOp) := [false, true].flatMap fun pointer =>
  [(site "CopyBlock" name!"CopyBlock" true pointer, .copyBlock 8),
   (site "CopyBlockUnaligned" name!"CopyBlockUnaligned" true pointer, .copyBlock 1),
   (site "InitBlock" name!"InitBlock" false pointer, .initBlock 8),
   (site "InitBlockUnaligned" name!"InitBlockUnaligned" false pointer, .initBlock 1)]

/-- The decoder keeps each call and the interpreter resolves its exact operation. -/
theorem block_emission : cases.all (fun (call, operation) =>
    decide (decoded call = .ok [.call call.method {}]) &&
    runtimeModel {} .call call.method == some (.memory operation)) = true := by decide +kernel

#print axioms block_emission

/-- A malformed identity, closed signature, declaration or external operand emits a call hole. -/
theorem block_refusals : cases.all (fun (call, _) =>
    let word := TypeExpr.primitive .uint32
    let invalid : List CallSite := [
      { call with
        method.owner := .atom "Fixture" "System.Runtime.CompilerServices.Unsafe" .classType },
      { call with method.name := name!"Other" }, { call with name := "Other" },
      { call with method.hasThis := true }, { call with method.genericArity := 1 },
      { call with method.parameters := call.method.parameters.set 0 (.byref word) },
      { call with method.returnType := word }, { call with declared.convention := 0x10 },
      { call with typeArguments := [word] },
      { call with parameterCount := 2 }, { call with returnsValue := true },
      { call with ownerArgumentCount := 1 }]
    let other := cases.find? fun (site, _) =>
      site.name == call.name && site.method.parameters != call.method.parameters
    other.any fun (overload, _) =>
      let crossed := [{ call with target := overload.target },
        { call with declared := overload.declared }]
      (invalid ++ crossed).all (fun changed => decide (decoded changed = liveHoleAt 0 40))) =
    true := by
  decide +kernel

#print axioms block_refusals

end Tests.UnsafeBlocks
