import CIL.Extraction.Translation
import CIL.Extraction.ImportLayouts
import CIL.Extraction.LayoutProjection

namespace Tests.ImportedLayouts
open CIL CIL.Extraction

def runtime : String := "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"
def library : String := "Library, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"
def word : TypeExpr := .atom runtime "System.UInt64"
def owner : TypeExpr := .atom library "Library.Methods"
def pair : TypeExpr := .atom library "Library.Pair"

def privateRaw : RawLayout := {
  identity := library ++ "::Library.Private", explicit := false,
  packing := 0, declaredSize := 0, fields := [⟨.unsigned32, none⟩] }
def leafRaw : RawLayout := {
  identity := library ++ "::Library.Leaf", explicit := false,
  packing := 0, declaredSize := 0, fields := [⟨.unsigned64, none⟩, ⟨.unsigned64, none⟩] }
def pairRaw : RawLayout := {
  identity := library ++ "::Library.Pair", explicit := false,
  packing := 0, declaredSize := 0, fields := [⟨.aggregate 0, none⟩, ⟨.unsigned64, none⟩] }
def publicRaw : List RawLayout := [leafRaw, pairRaw]
def artifactRaw : List RawLayout := [privateRaw, leafRaw,
  { pairRaw with fields := [⟨.aggregate 1, none⟩, ⟨.unsigned64, none⟩] }]
def privateLayout : ComputedLayout := ⟨⟨4, [⟨0, 4, false⟩]⟩, 4⟩
def leafLayout : ComputedLayout := ⟨⟨16, [⟨0, 8, false⟩, ⟨8, 8, false⟩]⟩, 8⟩
def pairLayout : ComputedLayout := ⟨⟨24, [⟨0, 16, true⟩, ⟨16, 8, false⟩]⟩, 8⟩
def publicComputed : Array ComputedLayout := #[leafLayout, pairLayout]
def artifactComputed : Array ComputedLayout := #[privateLayout, leafLayout, pairLayout]

theorem private_first_projection :
    LayoutProjectionValid artifactRaw artifactComputed publicRaw publicComputed [1, 2] .scalar := by decide +kernel
#print axioms private_first_projection

theorem rejection_1 : ¬ LayoutProjectionValid artifactRaw artifactComputed publicRaw publicComputed [0, 2] .scalar := by decide +kernel
#print axioms rejection_1
theorem rejection_2 : ¬ LayoutProjectionValid artifactRaw artifactComputed artifactRaw publicComputed [1, 2] .scalar := by decide +kernel
#print axioms rejection_2
theorem rejection_3 : ¬ LayoutProjectionValid artifactRaw artifactComputed
    [leafRaw, { pairRaw with fields := [⟨.aggregate 1, none⟩, ⟨.unsigned64, none⟩] }]
    publicComputed [1, 2] .scalar := by decide +kernel
#print axioms rejection_3
theorem rejection_4 : ¬ LayoutProjectionValid artifactRaw artifactComputed publicRaw
    #[leafLayout, { pairLayout with alignment := 4 }] [1, 2] .scalar := by decide +kernel
#print axioms rejection_4

def catalog : ImportLayoutCatalog := ⟨publicRaw, publicRaw, publicComputed⟩
def copySignature : ImportSignature := ⟨owner, "Copy", [], .void, [.byref pair, .byref pair]⟩
def copySlot : ImportSlot := {
  identity := library ++ "::Copy", closureDigest := "digest",
  parameterCount := 2, hasThis := false, returnsValue := false,
  signature := some copySignature, layouts := catalog }
def copySite : CallSite := {
  declaringType := owner, name := "Copy", target := .external copySlot.identity,
  typeArguments := [], parameterCount := 2, hasThis := false, returnsValue := false,
  returnType := .void, parameterTypes := [.byref pair, .byref pair] }

theorem imported_pair_valid : ImportedLayoutsValid [copySlot] .scalar := by decide +kernel
#print axioms imported_pair_valid
theorem imported_pair_call : validateImportCall [] [copySlot] 40 copySite copySlot.identity 0 2 = true := by decide +kernel
#print axioms imported_pair_call

theorem rejection_5 : ¬ ImportedLayoutsValid [{ copySlot with layouts := { catalog with actual := [] } }] .scalar := by decide +kernel
#print axioms rejection_5
theorem rejection_6 : ¬ ImportedLayoutsValid [{ copySlot with layouts := { catalog with published :=
    [leafRaw, { pairRaw with packing := 1 }] } }] .scalar := by decide +kernel
#print axioms rejection_6
theorem rejection_7 : ¬ ImportedLayoutsValid [{ copySlot with layouts := { catalog with computed :=
    #[leafLayout, { pairLayout with alignment := 4 }] } }] .scalar := by decide +kernel
#print axioms rejection_7
theorem rejection_8 : ¬ ImportedLayoutsValid [{ copySlot with layouts := ⟨[leafRaw, leafRaw], [leafRaw, leafRaw],
    #[leafLayout, leafLayout]⟩ }] .scalar := by decide +kernel
#print axioms rejection_8
theorem rejection_9 : validateImportCall [] [{ copySlot with signature := none, layouts := {} }]
    40 copySite copySlot.identity 0 2 = false := by decide +kernel
#print axioms rejection_9
theorem rejection_10 : validateImportCall [] [copySlot] 40 { copySite with parameterTypes := [.byref pair] }
    copySlot.identity 0 2 = false := by decide +kernel
#print axioms rejection_10
theorem rejection_11 : validateImportCall [] [copySlot] 40
    { copySite with parameterTypes := [.byref (.atom "Other" "Library.Pair"), .byref pair] }
    copySlot.identity 0 2 = false := by decide +kernel
#print axioms rejection_11

def identitySignature : ImportSignature := ⟨owner, "Identity", [word], word, [word]⟩
def identitySlot : ImportSlot := {
  identity := library ++ "::Identity<UInt64>", closureDigest := "digest",
  parameterCount := 1, hasThis := false, returnsValue := true, signature := some identitySignature }
def identitySite : CallSite := {
  declaringType := owner, name := "Identity", target := .external identitySlot.identity,
  typeArguments := [word], parameterCount := 1, hasThis := false, returnsValue := true,
  returnType := word, parameterTypes := [word] }

theorem closed_generic_valid : ImportedLayoutsValid [identitySlot] .scalar := by decide +kernel
#print axioms closed_generic_valid
theorem closed_generic_call :
    validateImportCall [] [identitySlot] 40 identitySite identitySlot.identity 0 1 = true := by decide +kernel
#print axioms closed_generic_call

theorem rejection_12 : validateImportCall [] [identitySlot] 40 { identitySite with typeArguments := [.atom runtime "System.UInt32"] }
    identitySlot.identity 0 1 = false := by decide +kernel
#print axioms rejection_12
theorem rejection_13 : validateImportCall [] [identitySlot] 40 { identitySite with typeArguments := [.parameter 0] }
    identitySlot.identity 0 1 = false := by decide +kernel
#print axioms rejection_13
theorem rejection_14 : validateImportCall [] [{ identitySlot with signature := none }] 40 identitySite
    identitySlot.identity 0 1 = false := by decide +kernel
#print axioms rejection_14
theorem rejection_15 : ¬ ImportedLayoutsValid [{ identitySlot with signature := some { identitySignature with arguments := [.parameter 0] } }] .scalar := by decide +kernel
#print axioms rejection_15
theorem rejection_16 : ¬ ImportedLayoutsValid [{ identitySlot with signature := some { identitySignature with owner := .apply (.constructor library "Library.Generic`1") word } }] .scalar := by decide +kernel
#print axioms rejection_16
theorem rejection_17 : ¬ ImportedLayoutsValid [{ copySlot with signature := some { copySignature with parameters := [pair, .byref pair] } }] .scalar := by decide +kernel
#print axioms rejection_17

theorem complete_certificate_valid : TranslationValid [] #[] [] [identitySlot] [] := by decide +kernel
#print axioms complete_certificate_valid

theorem complete_certificate_rejects_open_argument :
    ¬ TranslationValid [] #[] []
      [{ identitySlot with signature := some { identitySignature with arguments := [.parameter 0] } }] [] := by
  decide +kernel
#print axioms complete_certificate_rejects_open_argument

theorem complete_certificate_rejects_changed_layout :
    ¬ TranslationValid [] #[] [] [{ copySlot with layouts := { catalog with actual := [] } }] [] := by
  decide +kernel
#print axioms complete_certificate_rejects_changed_layout

end Tests.ImportedLayouts
