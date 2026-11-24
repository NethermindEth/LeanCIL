import CIL.Runtime.Net11WinX64.RangeConstructor
import CIL.Safety.LiteralImage
import CIL.Safety.Execution

/-! Entry execution derived from a package's checked translation. The deployment target selects
which runtime definitions are available to bind a folded constructor. -/

namespace CIL.Extraction

/-- Runtime bodies available when entering a package. -/
inductive RuntimeTarget where
  | portable
  | net11WinX64
  deriving DecidableEq

/-- A checked program with the method bodies whose literals the loader must intern. -/
inductive ProgramEntry where
  | translated (program : Program) (originals : List RawMethod)
  | range (image : Runtime.Net11WinX64.RangeImage)

def ProgramEntry.methods : ProgramEntry → Program
  | .translated program _ => program
  | .range image => image.methods

def ProgramEntry.originals : ProgramEntry → List RawMethod
  | .translated _ originals => originals
  | .range image => image.originals

/-- Load the original operands from empty caller storage before execution. -/
def ProgramEntry.initialMemory (entry : ProgramEntry) (budget : Option Nat := none) :=
  Safety.LiteralImage.initialMemory entry.originals budget

/-- Invoke the root method. The outer result reports image loading. -/
def ProgramEntry.invoke (entry : ProgramEntry) (fuel : Nat) (args : List Safety.Value)
    (budget : Option Nat := none) :=
  (entry.initialMemory budget).map (Safety.invoke entry.methods fuel 0 args)

/-- Live external exception constructor operands in the original checked method. -/
private def exceptionSites (item : MethodEvidence) : List Nat :=
  (item.original.code.zip item.reachable).zipIdx.filterMap fun ((op, live), pc) => do
    guard (live && op.opcode == 0x73)
    let .call site := op.operand | none
    let _ ← exceptionConstructor? site
    return pc

/-- Recover the entry from the same program and evidence as the audited translation theorem.
A folded throw requires the target runtime's actual constructor. An unavailable definition or
an open package returns none. The original fold cannot supply an execution result here. -/
def TranslationValid.entry {rawLayouts layouts pins platform evidence imports program}
    (_ : TranslationValid rawLayouts layouts pins platform evidence imports program)
    (target : RuntimeTarget) : Option ProgramEntry := do
  guard imports.isEmpty
  if target == .net11WinX64 then
    guard (program.all fun method => Runtime.Net11WinX64.supportsProfile method.profile)
  let sites := evidence.zipIdx.flatMap fun (item, index) =>
    (exceptionSites item).map (index, ·)
  match sites with
  | [] =>
    guard (!program.any fun method => method.code.any fun op => op matches .throw (some _))
    return .translated program (evidence.map (·.original))
  | [(0, pc)] =>
    guard (target == .net11WinX64)
    let [item] := evidence | none
    let [method] := program | none
    return .range (← Runtime.Net11WinX64.rangeImage? item.body item.original pc
      method.profile method.environment)
  | _ => none

/-- Execute the audited root for the chosen deployment. None means the checked entry could
not bind its runtime dependencies. -/
def TranslationValid.invoke {rawLayouts layouts pins platform evidence imports program}
    (certificate : TranslationValid rawLayouts layouts pins platform evidence imports program)
    (target : RuntimeTarget) (fuel : Nat) (args : List Safety.Value) (budget : Option Nat := none) :=
  (certificate.entry target).map (fun entry => entry.invoke fuel args budget)

end CIL.Extraction
