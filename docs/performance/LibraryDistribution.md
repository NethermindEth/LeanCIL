# Certified library distribution

<!-- audience: maintainers -->

This page describes the format in which CI passes the certified library between jobs, and how
to measure packing and restoring it. Read it before changing
`scripts/CertifiedLibraryArchive.cs` or the library steps of the verification workflow.
[CI operation](../CI.md) describes which runs may donate a library.

## Format

CI uploads the complete certified library as one `certified-library.tar.zst` file with artifact
compression disabled. The packer streams all regular files, including the hidden `.lake` tree,
through `zstd -T2 -6`. Hard-linked files are stored as independent file contents; no native
executable, proof artifact or source is omitted. Unix permission bits are stored and restored.

The producer prints the archive SHA256 in its job log. Donor selection reads that digest from
the same successful job as the manifest digest; suite jobs receive both through producer
outputs. Restoration:

1. checks the archive digest before decompression;
2. rejects traversal paths, links, special entries and duplicate paths;
3. checks the manifest digest before publishing the restored directory.

The library's source, toolchain and file-hash checks run afterward, followed by kernel replay
unless the producer ran reviewed producer code.

A raw-directory artifact is accepted only when its producer logged no archive digest; it is
checked against the manifest digest alone. An archive without its trusted digest is rejected. A
failed donor restore permits fresh preparation; a failed suite restore fails the suite. Main
republishes a certified library even when it reused a donor.

## Measuring

`zstd` must be on the path. Pack a prepared library, then restore it to a new directory:

```sh
dotnet run --file scripts/LibraryArchive.cs -c Release -- pack <library> <new archive> <manifest-sha256>
dotnet run --file scripts/LibraryArchive.cs -c Release -- restore <directory holding the archive> \
  <new destination> <manifest-sha256> <archive-sha256>
```

`<manifest-sha256>` is the SHA256 of the library's `cache-manifest.json`. `pack` prints the
archive digest that `restore` takes; the archive must be named `certified-library.tar.zst` and
lie outside the library. `restore` prints three lines, `Library restore authentication:`,
`Library restore extraction:` and `Library restore publication:`, each with its seconds. Time
each command as a whole for figures comparable with those below, and build the file app once
beforehand so compilation is excluded.

The reference figures are for a Linux library of 2,443 files:

| Measure | Figure |
| --- | ---: |
| Archive bytes | 220,550,345 |
| Pack | 3.153 s |
| Restore | 1.497 s |

Both times include `dotnet` process startup and archive hashing. They exclude network transfer.
A restore is correct when every restored file has the SHA256 and Unix permissions of its
original.

## Regression tests

```sh
dotnet run --file scripts/TestLibraryArchive.cs -c Release
```

The tests cover complete payloads, hidden files, executable permissions, hard-link contents,
source symlink rejection, missing and wrong digests, truncated compressed streams, raw-directory
artifacts, traversal, tar links and devices, and duplicate entries. Every unsafe tar has a valid
manifest and must fail for its specific unsafe entry, not for a missing manifest. The hard-link
and source symlink cases run on Linux only.
