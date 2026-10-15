import CIL.Extraction.Parameters

open CIL CIL.Extraction

namespace Tests.ExtractionParameters

def raw : RawArguments := {
  arguments := List.replicate 4 (.field .unsigned32)
  locals := [.field .unsigned64]
  code := [.load 0, .store 3, .address 1, .load 3] }
def reachable : List Bool := [true, true, true, true]
def method : Method := {
  code := [.arg 0, .setLocal 2, .localAddr 1, .local 2]
  locals := [.i64 0], localKinds := [.word64]
  parameterHomes := [(1, .word32), (3, .word32)]
  returnsValue := true }

example : requiredHomeIndices raw reachable = [1, 3] := by decide
example : ParameterHomesValid #[] raw reachable method := by decide
example : validateParameterHomes #[] raw reachable { method with parameterHomes := [] } = false := by decide
example : validateParameterHomes #[] raw reachable
    { method with parameterHomes := [(3, .word32), (1, .word32)] } = false := by decide
example : validateParameterHomes #[] raw reachable
    { method with code := [.arg 0, .setLocal 2, .localAddr 1, .arg 3] } = false := by decide
example : validateParameterHomes #[] raw reachable
    { method with code := [.arg 0, .setLocal 1, .localAddr 1, .local 2] } = false := by decide
example : validateParameterHomes #[] raw reachable
    { method with localKinds := [.word32] } = false := by decide
example : validateParameterHomes #[] raw reachable
    { method with locals := [] } = false := by decide
example : validateParameterHomes #[] raw [true, true, true] method = false := by decide
example : validateArgumentOp raw reachable .other true (.local 2) = false := by decide
example : validateArgumentOp raw reachable .other true (.arg 0) = false := by decide
example : validateParameterHomes #[] { raw with code := [.load 0, .store 9, .address 1, .load 3] }
    reachable method = false := by decide

-- Dead argument stores create no home; their emitted site must actually be unsupported.
def pruned : RawArguments := {
  arguments := [.field .unsigned32], locals := [], code := [.store 0, .load 0] }
example : ParameterHomesValid #[] pruned [false, true]
    { code := [.unsupported "pruned", .arg 0], locals := [], returnsValue := true } := by decide
example : validateParameterHomes #[] pruned [false, true]
    { code := [.setLocal 0, .arg 0], locals := [], returnsValue := true } = false := by decide

end Tests.ExtractionParameters
