import Tests.MetadataBuilder

/-!
# A hand-built world of two pinned assemblies

`T` carries the operands under test: references to `System.Runtime`, a call into `Lib`, an
instance and a static field, a generic method specification, a string, a locals signature and a
standalone call signature. `Lib` defines the class `Lib.Box` that `T` calls into. Tests
check each operand against the slices, then change one fact and assert the exact error.
-/

namespace Tests.MetadataWorld

open CIL CIL.Extraction Tests.MetadataBuilder
/-- The `Lib` assembly: a class `Lib.Box` with one instance field and one static method, whose
    base `System.Object` is named through its own reference to `System.Runtime`. -/
def libWorld : Step Unit := do
  let runtimeName ← string "System.Runtime"
  let objectName ← string "Object"
  let systemName ← string "System"
  let moduleName ← string "<Module>"
  let boxName ← string "Box"
  let libName ← string "Lib"
  let valueName ← string "value"
  let getName ← string "Get"
  let publicKeyToken ← blob [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A]
  let _ ← row Table.assemblyRef [10, 0, 0, 0, 0, publicKeyToken, runtimeName, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let _ ← row Table.typeRef [1 * 4 + 2, objectName, systemName]
  let _ ← row Table.typeDef [0, moduleName, 0, 0, 1, 1]
  let box ← row Table.typeDef [1, boxName, libName, 1 * 4 + 1, 1, 1]
  let fieldSignature ← blob [0x06, 0x08]
  let field ← row Table.field [0x0006, valueName, fieldSignature]
  let getSignature ← blob [0x00, 0x00, 0x08]
  let get ← row Table.methodDef [0x2050, 0, 0x0096, getName, getSignature, 1]
  link linkDeclaring field 1 box
  link linkDeclaring get 1 box
  -- The struct `Lib.Pair`, which extends `System.ValueType` through a reference of its own.
  let pairName ← string "Pair"
  let valueTypeName ← string "ValueType"
  let valueTypeRef ← row Table.typeRef [1 * 4 + 2, valueTypeName, systemName]
  let _ ← row Table.typeDef [0x101, pairName, libName, (valueTypeRef - 0x01000000) * 4 + 1, 2, 2]

/-- The tokens of the `T` world that the tests name. -/
structure OwnTokens where
  objectRef : Nat
  consoleRef : Nat
  boxRef : Nat
  writeLine : Nat
  getRef : Nat
  idRef : Nat
  idSpec : Nat
  countField : Nat
  totalField : Nat
  main : Nat
  localsSignature : Nat
  hello : Nat
  indirect : Nat
  extra : Nat
  /-- The reference to the struct `Lib.Pair`. -/
  pairRef : Nat

/-- The `T` assembly: the references and members its operands name. -/
def ownWorld : Step OwnTokens := do
  let runtimeName ← string "System.Runtime"
  let libName ← string "Lib"
  let objectName ← string "Object"
  let consoleName ← string "Console"
  let systemName ← string "System"
  let boxName ← string "Box"
  let moduleName ← string "<Module>"
  let programName ← string "Program"
  let countName ← string "count"
  let totalName ← string "total"
  let mainName ← string "Main"
  let writeLineName ← string "WriteLine"
  let getName ← string "Get"
  let idName ← string "Id"
  let publicKeyToken ← blob [0xB0, 0x3F, 0x5F, 0x7F, 0x11, 0xD5, 0x0A, 0x3A]
  let _ ← row Table.assemblyRef [10, 0, 0, 0, 0, publicKeyToken, runtimeName, 0, 0]
  let _ ← row Table.assemblyRef [1, 0, 0, 0, 0, 0, libName, 0, 0]
  modify fun builder => { builder with corlib := 1 }
  let objectRef ← row Table.typeRef [1 * 4 + 2, objectName, systemName]
  let consoleRef ← row Table.typeRef [1 * 4 + 2, consoleName, systemName]
  let boxRef ← row Table.typeRef [2 * 4 + 2, boxName, libName]
  let _ ← row Table.typeDef [0, moduleName, 0, 0, 1, 1]
  let program ← row Table.typeDef [1, programName, 0, 1 * 4 + 1, 1, 1]
  let intField ← blob [0x06, 0x08]
  let countField ← row Table.field [0x0006, countName, intField]
  let totalField ← row Table.field [0x0016, totalName, intField]
  let mainSignature ← blob [0x00, 0x00, 0x01]
  let main ← row Table.methodDef [0x2050, 0, 0x0096, mainName, mainSignature, 1]
  let writeLineSignature ← blob [0x00, 0x01, 0x01, 0x08]
  let writeLine ← row Table.memberRef [2 * 8 + 1, writeLineName, writeLineSignature]
  let getSignature ← blob [0x00, 0x00, 0x08]
  let getRef ← row Table.memberRef [3 * 8 + 1, getName, getSignature]
  let idSignature ← blob [0x10, 0x01, 0x01, 0x1E, 0x00, 0x1E, 0x00]
  let idRef ← row Table.memberRef [2 * 8 + 1, idName, idSignature]
  let instantiation ← blob [0x0A, 0x01, 0x09]
  let idSpec ← row Table.methodSpec [(idRef - 0x0A000000) * 2 + 1, instantiation]
  let localsBlob ← blob [0x07, 0x01, 0x0B]
  let localsSignature ← row Table.standAloneSig [localsBlob]
  let hello ← userString [104, 105]
  let indirectBlob ← blob [0x00, 0x01, 0x01, 0x08]
  let indirect ← row Table.standAloneSig [indirectBlob]
  link linkDeclaring countField 0 program
  link linkDeclaring totalField 0 program
  link linkDeclaring main 0 program
  link linkDefinition boxRef 1 (tokenOf Table.typeDef 2)
  link linkDefinition getRef 1 (tokenOf Table.methodDef 1)
  let pairName ← string "Pair"
  let pairRef ← row Table.typeRef [2 * 4 + 2, pairName, libName]
  link linkDefinition pairRef 1 (tokenOf Table.typeDef 3)
  pure { pairRef := pairRef, objectRef := objectRef, consoleRef := consoleRef, boxRef := boxRef,
         writeLine := writeLine, getRef := getRef, idRef := idRef, idSpec := idSpec,
         countField := countField, totalField := totalField, main := main,
         localsSignature := localsSignature, hello := 0x70000000 + hello,
         indirect := indirect, extra := 0 }

/-- The own slice and its tokens. -/
def own : MetadataSlice × OwnTokens :=
  build ownWorld (bytesOf "T") "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

/-- The `Lib` slice. -/
def lib : MetadataSlice :=
  (build libWorld (bytesOf "Lib") "Lib, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null").1

def tokens : OwnTokens := own.2

/-- The 32-bit and 64-bit unsigned types as the extractor writes them. -/
def int32 : TypeExpr := .atom runtimeScope "System.Int32"
def uint32 : TypeExpr := .atom runtimeScope "System.UInt32"
def uint64 : TypeExpr := .atom runtimeScope "System.UInt64"

def libScope : String := "Lib, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

/-- `System.Console.WriteLine(int)`: an external static call. -/
def writeLineSite : CallSite :=
  { declaringType := .atom runtimeScope "System.Console", name := "WriteLine",
    target := .external (runtimeScope ++ "::System.Void System.Console::WriteLine(System.Int32)"),
    typeArguments := [], parameterCount := 1, hasThis := false, returnsValue := false,
    returnType := .void, parameterTypes := [int32] }

/-- `Lib.Box.Get()`: a managed call into the other assembly. -/
def getSite : CallSite :=
  { declaringType := .atom libScope "Lib.Box", name := "Get", target := .managed 0x06000001,
    typeArguments := [], parameterCount := 0, hasThis := false, returnsValue := true,
    returnType := int32, parameterTypes := [] }

/-- `System.Console.Id<uint>(!!0)`: an external generic method. -/
def idSite : CallSite :=
  { declaringType := .atom runtimeScope "System.Console", name := "Id",
    target := .external (runtimeScope ++ "::!!0 System.Console::Id(!!0)"),
    typeArguments := [uint32], parameterCount := 1, hasThis := false, returnsValue := true,
    returnType := uint32, parameterTypes := [uint32] }

/-- The count and total fields of `T.Program`. -/
def countOperand : RawOperand := .field (.atom "T, Version=1.0.0.0, Culture=neutral, \
  PublicKeyToken=null" "Program") 0 int32 false

/-- The identity of the assembly `T`. -/
def ownIdentity : String :=
  "T, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null"

end Tests.MetadataWorld
