# Certified library distribution

CI uploads the complete certified library as one `certified-library.tar.zst` file with
artifact compression disabled. The packer streams all regular files, including the hidden
`.lake` tree, through zstd level 6 with two workers. Hard-linked files are stored as independent
file contents; no native executable, proof artifact or source is omitted.

The producer prints the archive SHA256 in its job log. Donor selection obtains that digest
from the same successful job as the manifest digest; suite jobs receive both through producer
outputs. Restoration checks the archive digest before decompression, rejects traversal paths,
links, special entries and duplicate paths, then checks the manifest digest before publishing
the restored directory. File executable permissions are preserved. Existing library source,
toolchain, file-hash and independent replay checks still run afterward.

Older raw-directory artifacts remain usable when their producer has no archive digest. An
archive without its trusted digest cannot take this compatibility path. A failed donor restore
permits fresh preparation; a failed suite restore fails the suite. Main still republishes a
certified library even when it reused a donor.

A real Linux library containing 2,443 files measured:

| Transport | Bytes | Restore |
| --- | ---: | ---: |
| Previous artifact ZIP | 260,653,000 | 3.524 s |
| C# tar/zstd packer | 220,550,345 | 1.497 s |

The C# packer took 3.153 s. All 2,443 restored files matched their original SHA256 and Unix
permissions. Pack/restore measurements include `dotnet` process startup and archive hashing;
the final all-file comparison is outside those measurements. They exclude compiling the C#
file app, which CI additionally performs. Network transfer and whole-job improvements remain
to be measured in CI; the payload itself is 40.1 MB (15.4%) smaller per download.

The Linux regression checks cover complete payloads, hidden files, executable permissions,
hard-link contents, source symlink rejection, missing/wrong digests, truncated compressed
streams, legacy raw artifacts, traversal, tar links/devices and duplicate entries. Every unsafe
tar has a valid manifest and must fail for its specific unsafe entry, not a missing manifest.
