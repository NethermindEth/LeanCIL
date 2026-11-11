# Lean toolchain distribution

<!-- audience: maintainers -->

This page describes how CI passes the installed Lean toolchain from the preparation job to the
suite jobs, and how to measure the archive. Read it before changing the toolchain steps of
`.github/workflows/verification.yml`. Every suite job downloads and restores this archive, so
its size and restore time are paid once per job.

## Format

The preparation job installs the pinned Lean toolchain once and archives the complete
installation with the Elan launchers and settings. No installation file is removed, so native
compilation, kernel replay and ordinary Lean and Lake commands find the same files. Executable
permissions, hard links and symlinks are preserved. Artifact upload disables ZIP compression.

Each suite job checks the archive and the `lean-toolchain` file against the SHA256 hashes in the
producer's outputs before extracting or executing anything.

The archive is a tar stream compressed by `zstd -T2 -6` and restored by `tar --zstd`. Zstandard
is part of the
[Ubuntu 24.04 runner image](https://github.com/actions/runner-images/blob/main/images/ubuntu/Ubuntu2404-Readme.md).

## Measuring

On Linux, with the toolchain installed by Elan under `$HOME/.elan`, time the workflow's pack and
restore commands and a decompression to `/dev/null`, reading and writing a Linux file system:

```sh
prefix="$(lean --print-prefix)"
toolchain="${prefix#"$HOME/"}"
time (tar -C "$HOME" -cf - .elan/bin .elan/settings.toml "$toolchain" \
  | zstd -T2 -6 -q > lean-toolchain.tar.zst)
time zstd -d -q -c lean-toolchain.tar.zst > /dev/null
mkdir restored && time tar --zstd -xf lean-toolchain.tar.zst --no-same-owner -C restored
ELAN_HOME="$PWD/restored/.elan" restored/.elan/bin/lean --version
```

Check the size with `wc -c lean-toolchain.tar.zst`. The workflow hashes the compressed archive
and never the decoded stream. When you change the compressor or level, compare
`zstd -d -c <archive> | sha256sum` before and after by hand; the tar stream must be identical.

The reference figures are for the Linux x64 installation of Lean 4.35.0, on Ubuntu 24.04 under
WSL on an AMD Ryzen 9 9950X, with no other build running:

| Measure | Figure |
| --- | ---: |
| Archive bytes | 724,623,552 |
| Compression | 10.79 s |
| Decompression to `/dev/null` | 2.49 s |
| Full `tar --zstd` restore | 7.89 s |

The times were measured locally. They do not include the artifact transfer, which depends on
the hosted runner's network.
