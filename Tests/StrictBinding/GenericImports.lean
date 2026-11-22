import StrictBinding.GenericImports

/-! Reject ambiguous contract sidecar members and substitutions of an audited closure. -/

namespace Tests.StrictBinding.GenericImports
open CIL _root_.StrictBinding

private def image (text : String) : ImageBytes :=
  ImageBytes.ofBytes (text.toUTF8.data.toList.map UInt8.toNat)

private def lookup (document : String) : Option String := do
  let root ← ContractSidecar.read (image document)
  let entry ← ContractSidecar.member root "X<T>"
  ContractSidecar.text entry "contractConstant"

example : lookup (r#"{"exports":[{"identity":"X\u003CT\u003E","contractConstant":"C.id"}]}"#) =
    some "C.id" := by decide +kernel
example : lookup (r#"{"exports":[{"identity":"X<T>","contractConstant":"C.id","contract\u0043onstant":"C.other"}]}"#) =
    none := by decide +kernel
example : lookup (r#"{"exports":[{"identity":"X<T>"},{"identity":"X<T>","contractConstant":"C.other"}]}"#) =
    none := by decide +kernel
example : (ContractSidecar.read (image "{\"exports\":[]}{}")).isNone := by decide +kernel
example : (ContractSidecar.read (image "{\"n\":01}")).isNone := by decide +kernel

private def sidecar := image <|
  "{\"schema\":1,\"formatVersion\":2,\"isReferenceAssembly\":false,\"assemblyIdentity\":\"P\"," ++
  "\"implementationSha256\":\"I\",\"interfaceDigest\":\"D\",\"exports\":[{\"identity\":\"X<T>\"," ++
  "\"profiles\":[\"scalar\"],\"parameterCount\":1,\"hasThis\":false,\"returnsValue\":true," ++
  "\"visibility\":\"public\",\"kind\":\"method\",\"contractConstant\":\"C.id\",\"closureDigest\":\"A\"}]}"

private def publication : StrictBinding.GenericImports.Publication :=
  ⟨"X<T>", "P", "I", "D", "scalar", "C.id", "A", sidecar⟩

private def slot : ImportSlot :=
  { identity := "X<T>", closureDigest := "A", parameterCount := 1, hasThis := false, returnsValue := true }

example : StrictBinding.GenericImports.exportMatches publication slot = true := by decide +kernel
example : StrictBinding.GenericImports.exportMatches { publication with contractName := "C.copy" } slot =
    false := by decide +kernel
example : StrictBinding.GenericImports.exportMatches { publication with closureDigest := "B" }
    { slot with closureDigest := "B" } = false := by decide +kernel

end Tests.StrictBinding.GenericImports