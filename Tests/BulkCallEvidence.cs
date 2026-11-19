partial class Program
{
    // Each checked example retains its call and obtains the expected memory operation from its model fact.
    static string BulkCallEvidence(int method, int pc, string operation) => $$"""

        namespace BulkEvidence
        open CIL CIL.Extraction Extracted
        /-- The retained call at this pc executes the specified memory operation on every stack. -/
        theorem call_step (args : List Safety.Value) (frame : Safety.Frame)
            (stack : List Safety.Value) (memory : Safety.Memory) :
            match method{{method}}.code[{{pc}}]? with
            | some (Instruction.call target prefixes) =>
              Safety.step method{{method}} (.call target prefixes) {{pc}} args frame stack memory =
                Safety.step method{{method}} (.memory ({{operation}})) {{pc}} args frame stack memory
            | _ => False := by
          exact Safety.step_call_memory method{{method}} {{pc}} args frame memory
            (prefixes := {}) rfl method{{method}}_model{{pc}} rfl stack
        #print axioms call_step
        /-- A live call binds the raw declaration and rejects a substituted memory instruction. -/
        theorem call_operand :
            (match method{{method}}Closed.code[{{pc}}]? with
            | some raw => match raw.operand with
              | .call site =>
                let agrees := fun operand emitted =>
                  runtimeCatalog.siteAgrees environment profile operand emitted none true
                let forged := { raw with operand := .call { site with declared.convention := 0 } }
                let call := Instruction.call site.method {}
                agrees raw call && !agrees forged call && !agrees raw (.memory ({{operation}}))
              | _ => false
            | none => false) = true := by decide +kernel
        #print axioms call_operand
        end BulkEvidence

        """;
}
