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
  | range (image : ManagedPackage)

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

/-- Recover the entry from the same program and evidence as the audited translation theorem.
A folded throw requires the target runtime's actual constructor. An unavailable definition or
an open package returns none. The original fold cannot supply an execution result here. -/
def TranslationValid.entry {rawLayouts layouts pins platform evidence imports program declarations}
    (_ : TranslationValid rawLayouts layouts pins platform evidence imports program declarations)
    (target : RuntimeTarget) : Option ProgramEntry := do
  guard imports.isEmpty
  if target == .net11WinX64 then
    guard (program.all fun method => Runtime.Net11WinX64.supportsProfile method.profile)
  -- A bundled CoreLib implementation belongs to its selected runtime even when every call is closed.
  let usesCoreLib := evidence.tail.any fun item => item.assembly.identity == coreLibraryAssembly
  if !declarations.isEmpty || usesCoreLib then
    guard (target == .net11WinX64)
    guard (!program.any fun method => method.code.any fun op => op matches .throw (some _))
    let root :: definitions := evidence.zip program | none
    return .range ⟨root, definitions, declarations⟩
  let sites := evidence.zipIdx.flatMap fun (item, index) =>
    (Runtime.Net11WinX64.ConstructorSource.ofEvidence item).sites.map (index, ·)
  match sites with
  | [] =>
    guard (!program.any fun method => method.code.any fun op => op matches .throw (some _))
    return .translated program (evidence.map (·.original))
  | [(0, pc)] =>
    guard (target == .net11WinX64)
    let [item] := evidence | none
    let [method] := program | none
    let package ← Runtime.Net11WinX64.constructorImage?
      (.ofEvidence item) pc method.profile method.environment
    return .range (← Runtime.Net11WinX64.checkPackage? package method.environment pins platform).val
  | _ => none

/-- Execute the audited root for the chosen deployment. None means the checked entry could
not bind its runtime dependencies. -/
def TranslationValid.invoke {rawLayouts layouts pins platform evidence imports program declarations}
    (certificate : TranslationValid rawLayouts layouts pins platform evidence imports program declarations)
    (target : RuntimeTarget) (fuel : Nat) (args : List Safety.Value) (budget : Option Nat := none) :=
  (certificate.entry target).map (fun entry => entry.invoke fuel args budget)

end CIL.Extraction
