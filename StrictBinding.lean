import StrictBinding.Image
import StrictBinding.Sha256
import StrictBinding.Sha1
import StrictBinding.Pe
import StrictBinding.Tables
import StrictBinding.Identity
import StrictBinding.Dump
import StrictBinding.Bind
import StrictBinding.Evidence

/-!
# Strict binding audit

Kernel-checked facts that bind an extraction to the assembly file it was read from, for the
opt-in `leancil audit-binding` command. A consumer states the SHA-256 digest of the file; the
audit proves that the digest of an image constant equals it, decodes the PE container and the
metadata tables from the same constant, and checks claims of the extraction against the bytes at
positions it computes itself. This library is not part of `CIL`: no certified module imports it,
and the default `verify`, `check` and `extract` flow never reads it.
-/
