# Lean toolchain distribution

The preparation job installs the pinned Lean toolchain once and publishes the complete
installation, Elan launchers and settings. Each suite checks the archive and toolchain-file
hashes against the producer's outputs before extracting or executing anything. The immutable
artifact identity, executable permissions, hardlinks and symlinks are unchanged.

The workflow uses `zstd -T2 -6` and `tar --zstd`. Zstandard is included
in the [Ubuntu 24.04 runner image](https://github.com/actions/runner-images/blob/main/images/ubuntu/Ubuntu2404-Readme.md).
No installation files are removed. Native compilation, kernel replay and ordinary Lean/Lake
commands retain the same files; artifact upload still disables redundant ZIP compression.

## Measurements

The measured Linux x64 installation was compressed under Ubuntu 24.04 in WSL on a
Ryzen 9 9950X. Both archives decoded
to the same SHA-256 hash. Timed reads and writes used the Linux filesystem, excluding the
initial download and Windows-to-Linux copy. The final pair ran without other proof builds.

| Measurement | gzip -1 | zstd -T2 -6 |
| --- | ---: | ---: |
| Archive bytes | 965,567,071 | 724,623,552 |
| Compression | 21.45s | 10.79s |
| Decompression to `/dev/null` | 11.38s | 2.49s |

The archive is 25% smaller, saving about 15.9 GB across 66 downloads at the measured sizes.
This is a byte-count reduction, not a prediction of hosted network speed. Local decompression
is 78% faster; CI must establish the complete job savings, including transfer and filesystem
extraction. A full `tar --zstd` restore took 7.89s and the restored Lean and Lake executables
reported the pinned version successfully.

The Linux smoke check also preserves executable modes, hardlinks and symlinks, and verifies
that a corrupt archive or incorrect toolchain pin fails before extraction or execution.
