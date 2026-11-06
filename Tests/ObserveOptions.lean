import CIL

/-!
# Observer options without the observer

A proof that sets an option of `CIL.Observe` without importing it is told to import it, at the
place it sets the option, instead of getting no output or Lean's unknown-option error.
-/

/--
warning: `trace.CIL.step` traces each step a LeanCIL tactic takes only in a file that imports
`CIL.Observe`; add `import CIL.Observe` to this file
-/
#guard_msgs (whitespace := lax) in
set_option trace.CIL.step true in
example : True := trivial

/--
warning: `cil.diagnostics` records where each LeanCIL tactic failed or stopped only in a file
that imports `CIL.Observe`; add `import CIL.Observe` to this file
-/
#guard_msgs (whitespace := lax) in
example : True := by
  set_option cil.diagnostics true in
  trivial

-- A command that sets neither option is not warned about.
#guard_msgs in
example : True := trivial
