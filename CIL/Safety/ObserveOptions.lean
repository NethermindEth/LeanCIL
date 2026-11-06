import Lean

/-!
# Observer options

The two options that turn on `CIL.Observe`: `trace.CIL.step` for the step trace and
`cil.diagnostics` for failure records. They are registered with the stepping tactics, so a proof
can set them without importing the observer; a linter here then warns at each place one is set
that it has no effect until the file imports `CIL.Observe`. The tactics never read either option.
-/

namespace CIL.Safety

open Lean Elab Command

initialize registerTraceClass `CIL.step

/-- Whether `CIL.Observe` logs a `FailureRecord` for each failure of a LeanCIL tactic. -/
register_option cil.diagnostics : Bool := {
  defValue := false
  descr := "log a machine-readable record of where each LeanCIL tactic failed or stopped"
}

/-- The options only `CIL.Observe` acts on, with what each one shows. -/
def observerOptions : List (Name × String) :=
  [(`trace.CIL.step, "traces each step a LeanCIL tactic takes"),
   (`cil.diagnostics, "records where each LeanCIL tactic failed or stopped")]

/-- The observer's linter, whose presence means the file imports `CIL.Observe`. -/
def observerName : Name := `CIL.Safety.observer

/-- Warns at each observer option a command sets while `CIL.Observe` is not imported, since the
    option would otherwise do nothing silently; nothing when the observer is imported. -/
def observerImportHint : Linter where
  name := `CIL.Safety.observerImportHint
  run := fun stx => do
    if (← getEnv).contains observerName then return
    for (option, shows) in observerOptions do
      if let some place := stx.find? fun node => node.isIdent && node.getId == option then
        logWarningAt place m!"`{option}` {shows} only in a file that imports `CIL.Observe`; \
          add `import CIL.Observe` to this file"

initialize addLinter observerImportHint

end CIL.Safety
