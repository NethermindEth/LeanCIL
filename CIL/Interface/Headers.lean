import Lean

/-! Source import headers parsed without executing interface declarations. -/

namespace CIL.Interface
open Lean

/-- Parse source headers with Lean's parser, retaining module-system import forms and comments. -/
def writeSourceHeaders (input : String) : IO Unit := do
  let sources : Array String ←
    IO.ofExcept <| (Json.parse (← IO.FS.readFile input)).bind fromJson?
  for source in sources do
    let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext source input)
    if messages.hasErrors then
      throw (IO.userError "Invalid contract interface import header")
    let `(Parser.Module.header| $[module]? $[prelude]? $imports*) := header
      | throw (IO.userError "Invalid contract interface header")
    let mut names : Array Json := #[]
    for imported in imports do
      let `(Parser.Module.import| $[public]? $[meta]? import $[all]? $name) := imported
        | throw (IO.userError "Invalid contract interface import")
      names := names.push (Json.str name.getId.toString)
    IO.println (Json.arr names).compress

end CIL.Interface
