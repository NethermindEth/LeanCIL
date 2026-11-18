import CIL.OleanAudit

/-! Counts decoded key bytes hashed by the audit as a single JSON object grows. -/

/-- Counts the bytes passed to the string hash, including any calls during bucket growth. -/
private unsafe def countingHash (bytes : IO.Ref Nat) (key : String) : UInt64 := unsafeBaseIO do
  bytes.modify (fun total => total + key.utf8ByteSize)
  return hash key

/-- Every key is hashed once, even when later insertions resize the containing object. -/
private unsafe def checkHashCost : IO Unit := do
  let longKey := String.ofList (List.replicate 65536 'x')
  let mut excess := false
  for count in [8, 128, 2048] do
    let keys := longKey :: (List.range count).map (fun index => s!"k{index}")
    let members := keys.map (fun key => (Lean.Json.str key).compress ++ ":0")
    let source := "{" ++ ",".intercalate members ++ "}"
    let expected := keys.foldl (fun total key => total + key.utf8ByteSize) 0
    let bytes <- IO.mkRef 0
    IO.ofExcept (@LeanCILAudit.checkRequestKeys { hash := countingHash bytes } source)
    let actual <- bytes.get
    IO.println s!"{count} short keys: hashed {actual} bytes for {expected} key bytes"
    excess := excess || actual != expected
  if excess then throw (IO.userError "A request key was hashed again during insertion")
  let collision := @LeanCILAudit.checkRequestKeys { hash := fun _ => 0 }
    "{\"a\":0,\"b\":1,\"a\":2}"
  if let .error message := collision then
    if message.endsWith "Duplicate JSON key: a" then return
  throw (IO.userError "Colliding keys must match by their decoded text")

#eval checkHashCost
