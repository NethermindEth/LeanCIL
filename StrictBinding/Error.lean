/-!
# Audit errors

The reasons a strict binding check can fail. Every check in `StrictBinding` returns
`Except AuditError`, so a rejected image, container or body names the fact that did not hold.
Payloads are numbers (offsets, tokens, relative virtual addresses) so a test can compare an
error exactly.
-/

namespace StrictBinding

/-- Why the PE container of an image does not decode or does not map a relative virtual address. -/
inductive PeError where
  /-- The file does not start with the `MZ` signature. -/
  | notDos
  /-- The `PE\0\0` signature is missing at this file offset. -/
  | badSignature (offset : Nat)
  /-- The optional header magic is neither PE32 (`0x10B`) nor PE32+ (`0x20B`). -/
  | badMagic (magic : Nat)
  /-- The optional header has no CLI header data directory. -/
  | noCliHeader
  /-- The CLI header is shorter than 72 bytes or does not state its own size. -/
  | badCliHeader
  /-- No section holds `count` bytes at the relative virtual address. -/
  | unmappedRva (rva count : Nat)
  /-- More than one section holds the relative virtual address. -/
  | ambiguousRva (rva : Nat)
  /-- The metadata root is missing, malformed or lacks the `#~` stream. -/
  | badMetadataRoot
  /-- A stream header names a stream twice or one the audit does not read. -/
  | badStream
  deriving DecidableEq, Repr

/-- Why the table stream of an image does not decode or does not contain a token. -/
inductive TableError where
  /-- The `#~` header or its tables do not fit inside the stream. -/
  | badTableStream
  /-- A table above `0x2C` is present, so row sizes cannot be computed. -/
  | unsupportedTables (valid : Nat)
  /-- The table stream has pointer or edit-and-continue tables, which index other tables
      indirectly, so row sizes and positions are not computed from the target table alone. -/
  | pointerTables (valid : Nat)
  /-- The heap size flags set a bit the audit does not know. -/
  | unsupportedHeapSizes (flags : Nat)
  /-- The metadata tables have no such column. -/
  | noSuchColumn (table column : Nat)
  /-- A heap key or the entry it names is outside the heap. -/
  | outsideHeap (key : Nat)
  /-- A string heap entry is not well-formed UTF-8. -/
  | invalidUtf8
  deriving DecidableEq, Repr

/-- Why a binding fact does not hold. -/
inductive AuditError where
  /-- The image constant has the wrong chunk count, an oversized chunk or nonzero padding. -/
  | malformedImage
  /-- A read of `count` bytes at `offset` leaves the image. -/
  | outsideImage (offset count : Nat)
  | pe (error : PeError)
  | tables (error : TableError)
  /-- The token names a row the tables do not have. -/
  | tokenOutOfScope (token : Nat)
  /-- A body is bound to a token that is not a MethodDef token. -/
  | notMethodDef (token : Nat)
  /-- The MethodDef row of the token has no IL body. -/
  | noIlBody (token : Nat)
  /-- The bytes at the mapped position of the row's relative virtual address are not the body. -/
  | bodyMismatch (token rva offset : Nat)
  /-- The Assembly row does not spell the identity the image is pinned under. -/
  | identityMismatch (identity : String)
  /-- No pinned image has this identity. -/
  | unpinned (identity : String)
  /-- Two pinned images have the same identity. -/
  | duplicateImage (identity : String)
  deriving DecidableEq, Repr

/-- Whether a check succeeded; the proposition of each audited theorem is `ok check = true`. -/
def ok {α : Type} : Except AuditError α → Bool
  | .ok _ => true
  | .error _ => false

end StrictBinding
