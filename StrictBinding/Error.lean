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
  /-- An unflagged public key token has a nonzero width other than eight bytes. -/
  | invalidPublicKeyToken (length : Nat)
  deriving DecidableEq, Repr

/-- The part of a type definition claim that its TypeDef row does not have. -/
inductive TypeDefPart where
  | typeName
  | typeNamespace
  /-- The row's visibility or the stated NestedClass row does not give the claimed nesting. -/
  | nesting
  /-- The row's flags and base type give another kind. -/
  | kind
  /-- The row's field list or the next row's does not bound the claimed Field rows. -/
  | fields
  /-- The `Extends` column does not name the claimed base row, or that row has other names. -/
  | base
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
  /-- The row number exceeds the three bytes available below the table byte. -/
  | rowOverflow (table row : Nat)
  /-- A body is bound to a token that is not a MethodDef token. -/
  | notMethodDef (token : Nat)
  /-- The MethodDef row of the token has no IL body. -/
  | noIlBody (token : Nat)
  /-- The bytes at the mapped position of the row's relative virtual address are not the body. -/
  | bodyMismatch (token rva offset : Nat)
  /-- A FieldRVA or ClassLayout row names an absent or repeated Field or TypeDef. -/
  | invalidDataTableKey (table row key : Nat)
  /-- The static sites do not match the program counters recorded by the body decoder. -/
  | staticSiteMismatch (method : Nat)
  /-- The static site of a decoded method has no corresponding field in the evidence. -/
  | unresolvedStaticField (method pc : Nat)
  /-- A field, its RVA or its mapped file position does not permit the claimed data access. -/
  | invalidFieldData (token : Nat)
  /-- The slice does not identify the platform scope of its primitive types. -/
  | invalidObjectScope (identity : String)
  /-- The platform image lacks a unique public, baseless System.Object class. -/
  | invalidObjectDefinition (identity : String)
  /-- A physical field declared by System.Object lacks the Static flag. -/
  | objectInstanceField (identity : String) (field : Nat)
  /-- The claimed static data differs from the bytes at the field's mapped RVA. -/
  | fieldDataMismatch (token rva offset : Nat)
  /-- The Assembly row does not spell the identity the image is pinned under. -/
  | identityMismatch (identity : String)
  /-- No pinned image has this identity. -/
  | unpinned (identity : String)
  /-- Two pinned images have the same identity. -/
  | duplicateImage (identity : String)
  /-- The carried table stream header of the assembly pinned under `identity` is not the image's
      header through its last row count, or does not decode to the carried decoded header. -/
  | headerMismatch (identity : String)
  /-- The carried row of the token is not the image's row under the carried heap numbering. -/
  | rowMismatch (token : Nat)
  /-- The carried entry with this key is not the entry of the image at the offset the key names. -/
  | heapMismatch (heap key : Nat)
  /-- Two row cells of one offset hold different keys, two of different offsets hold one key, a
      carried entry has a key no row cell holds, a row key has no carried entry, a key is not
      below the omitted-entry marker, or the carried entries of the heap do not ascend by key. -/
  | heapNumbering (heap key : Nat)
  /-- TypeDef row `row` does not have this part of the claimed type definition. -/
  | typeDefMismatch (row : Nat) (part : TypeDefPart)
  /-- Row `row` of `table` has a key below the key of the row before it. -/
  | unsortedTable (table row : Nat)
  deriving DecidableEq, Repr

/-- Whether a check succeeded; the proposition of each audited theorem is `ok check = true`. -/
def ok {α : Type} : Except AuditError α → Bool
  | .ok _ => true
  | .error _ => false

end StrictBinding
