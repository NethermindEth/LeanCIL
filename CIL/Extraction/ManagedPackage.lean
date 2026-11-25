import CIL.Extraction.Translation

/-! Validation of an executable method table with physically bound managed declarations.
A declaration supplies a call target's identity and signature. Execution and feature-flow
validation receive no implementation or return-value facts for that slot. -/

namespace CIL.Extraction

/-- The first row is the package entry. Declarations occupy the slots after the executable rows. -/
structure ManagedPackage where
  root : MethodEvidence × Method
  definitions : List (MethodEvidence × Method)
  declarations : List MethodEvidence

/-- Executable rows in the order used by managed calls. -/
def ManagedPackage.rows (package : ManagedPackage) := package.root :: package.definitions

/-- The program executed from the package entry. -/
def ManagedPackage.methods (package : ManagedPackage) : Program := package.rows.map Prod.snd

/-- Original method bodies whose literals must be loaded before invocation. -/
def ManagedPackage.originals (package : ManagedPackage) := package.rows.map (·.1.original)

/-- The root's decoded method and metadata evidence. -/
def ManagedPackage.caller (package : ManagedPackage) := package.root.1

/-- The shared call-resolution table, including managed declarations after the last local body. -/
def ManagedPackage.lookup (package : ManagedPackage) :=
  callableEvidence (package.rows.map Prod.fst) package.declarations

/-- Check every executable method against the same lookup, assembly pins and platform. -/
def ManagedPackage.rowValid (environment : LayoutEnvironment) (pins : List AssemblyPin)
    (platform : PlatformTable) (table : List MethodEvidence)
    (row : MethodEvidence × Method) : Bool :=
  decide (MethodEvidenceValid environment.rawLayouts environment.layouts pins platform
    table [] row.1 row.2)

/-- Validate the method table, its global storage, and the declarations used in call resolution. -/
def ManagedPackage.checked (package : ManagedPackage) (environment : LayoutEnvironment)
    (pins : List AssemblyPin) (platform : PlatformTable) : Bool :=
  let methods := package.methods
  let table := package.lookup
  package.rows.all (rowValid environment pins platform table) &&
    (decide (LayoutsValid environment.rawLayouts environment.layouts (programArchitecture methods)) &&
    decide (StaticValuesValid methods) &&
    decide (StaticIdentitiesValid methods (package.rows.map (·.1.body))) &&
    AttributionValid (bodyOwners table) &&
    callCatalogValid environment.rawLayouts pins platform (package.rows.map Prod.fst)
      package.declarations)

/-- Rows that each pass `rowValid` against `table` are checked methods for that table. -/
theorem MethodsChecked.of_rows {environment : LayoutEnvironment} {pins platform}
    {table : List MethodEvidence} (rows : List (MethodEvidence × Method))
    (checked : rows.all (ManagedPackage.rowValid environment pins platform table) = true) :
    MethodsChecked environment.rawLayouts environment.layouts pins platform table []
      (rows.map Prod.fst) (rows.map Prod.snd) := by
  induction rows with
  | nil => exact .nil
  | cons head tail ih =>
    obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp checked
    exact .cons (of_decide_eq_true first) (ih rest)

#print axioms MethodsChecked.of_rows

/-- A successful package check supplies the usual per-method translation proof, with every
executable slot checked against the exact table that includes the declared call targets. -/
theorem ManagedPackage.methodsChecked {package : ManagedPackage} {environment pins platform}
    (valid : package.checked environment pins platform = true) :
    MethodsChecked environment.rawLayouts environment.layouts pins platform package.lookup []
      (package.rows.map Prod.fst) package.methods :=
  MethodsChecked.of_rows package.rows (Bool.and_eq_true_iff.mp valid).1

#print axioms ManagedPackage.methodsChecked

/-- The ordinary extraction validator certifies the executable program with its declarations. -/
theorem ManagedPackage.translationValid {package : ManagedPackage} {environment pins platform}
    (valid : package.checked environment pins platform = true) :
    TranslationValid environment.rawLayouts environment.layouts pins platform
      (package.rows.map Prod.fst) [] package.methods package.declarations := by
  have global := (Bool.and_eq_true_iff.mp valid).2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at global
  obtain ⟨⟨⟨⟨layout, statics⟩, identities⟩, attribution⟩, catalog⟩ := global
  exact translation_of_methods layout statics (by simpa only [List.map_map, Function.comp_def] using identities)
    (by simp [ImportedLayoutsValid]) (by simp [ImportedLocalLayoutsBound]) attribution catalog (package.methodsChecked valid)

#print axioms ManagedPackage.translationValid

end CIL.Extraction
