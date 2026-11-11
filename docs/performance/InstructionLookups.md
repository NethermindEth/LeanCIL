# Instruction lookup equations

<!-- audience: maintainers -->

What the lookup equations of a method cost, and how to check that the cost stays linear in the
method's length. Read it before changing `cil_instruction_equations`, `CIL.CodeSuffix` or the
form in which the extractor and the template emitter write a method's code.

## What must hold

`cil_instruction_equations body` states one `@[cil_code ↓]` equation per instruction,
`body_instruction{pc} : (body xs).code[pc]? = some op`; see
[binding proofs](../PROOFS-BINDING.md) for its use. It names the suffix of the code list at
every 16th instruction (`body_suffix{start}`), proves each named suffix from the one before it
with `CIL.CodeSuffix.advance` (`body_suffix{start}_placed`), and proves each equation from the
suffix that starts its block with `CIL.CodeSuffix.lookup`. No proof walks more than 16 cells of
the code list, so the equations cost time linear in the method's length, about 6,400 heartbeats
each. The equations depend on `propext` alone.

Three properties keep that cost:

- An equation is never proved against the whole code list. Such a proof (`rfl`) walks `pc`
  cells, so a method's equations cost quadratic time: 96,000 heartbeats per equation at 502
  instructions and 749,000 at 4,002.
- The command builds its declarations as terms. The same suffixes and proofs written out as
  source take 58,000 heartbeats per equation to parse and elaborate.
- A generated template reports the axioms of its last equation alone. That proof reaches every
  named suffix and so every instruction, and each report walks all it reaches: one report per
  equation costs 399 million heartbeats at 4,002 instructions, where the 4,002 equations
  themselves cost 27 million.

The `set_option maxRecDepth` emitted in `Extracted.lean` and `Templates.lean` is 4096, or 16 per
instruction of the longest method when that is more, because Lean compiles and compares a code
list one nested cell per instruction. At a fixed 4096, a method of 2,002 instructions fails to
compile.

## The `lookups` suite

```sh
dotnet run --file scripts/Test.cs -- --suite lookups
```

The suite (`Tests/LookupScaling.cs`) extracts one method, `word = word * y + x;` repeated, at
about 500 and about 2,000 instructions, and compiles three files at each length: the
extraction, its code as a body with a parameter under `cil_instruction_equations`, and its
generated template. Heartbeats are read by `IO.getNumHeartbeats` at the end of each file, less
the heartbeats of a file that holds the imports alone. Each file prints one line:

```text
PASS compiling an extracted method costs <n> heartbeats per instruction at 502 instructions and <n> at 2002, <ratio> times as many
```

The suite fails when a ratio exceeds 1.25. Linear equations measure 0.99 for the extraction and
1.01 for the body and the template; equations proved against the whole list measure 3.09 for the
extraction and about 3.7 for the body. A ratio that rises toward 1.25 means some proof or
elaboration step walks the code list again. The suite also fails when a `cil_lookup` at a
computed pc costs more than 1.25 times as much per case at 16 repeated segments as at 4.

## Reference figures

Windows, 32 cores, Lean 4.35.0, one method of `word = word * y + x;` repeated at the scalar
profile. Each file was compiled with `-DElab.async=false`, and heartbeats come from
`IO.getNumHeartbeats` at the end of the file; they repeat to within a few hundred between runs.
CPU seconds were taken while other builds ran and compare only within one session.

The extraction, `Extracted.lean` with its certificate. "Without equations" is the same file
without the `cil_instruction_equations` command:

| Instructions | Heartbeats | Without equations | Per equation | CPU | `.olean` bytes |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 250 | 64,133,492 | 62,534,629 | 6,395 | 7.6 s | 2,628,408 |
| 502 | 120,915,482 | 117,695,162 | 6,415 | 13.6 s | 5,111,408 |
| 1,002 | 234,316,408 | 227,875,207 | 6,428 | 26.8 s | 10,029,288 |
| 2,002 | 463,305,964 | 450,395,121 | 6,449 | 58.3 s | 19,872,280 |
| 4,002 | 928,770,174 | 902,897,844 | 6,465 | 137.9 s | 39,566,040 |

The certificate without equations costs 225,000 to 250,000 heartbeats per instruction at every
size, so the whole file is linear in heartbeats and the equations are under 3% of it. Its CPU
time per instruction still rises from 0.029 s at 2,002 instructions to 0.034 s at 4,002, which
the equations do not account for.

The method's code as a hand-written definition followed by the command, and the output of
`leancil templates` over the scalar and `x64-v3` extractions, compiled as emitted. "Per
equation" subtracts the same file without the command:

| Instructions | Body, heartbeats | Per equation | CPU | Template, heartbeats | Per equation | CPU |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 250 | 7,826,637 | 6,382 | 2.6 s | 7,819,437 | 6,687 | 2.5 s |
| 502 | 10,942,760 | 6,409 | 2.7 s | 11,018,590 | 6,708 | 2.8 s |
| 1,002 | 17,166,259 | 6,422 | 3.1 s | 17,408,327 | 6,719 | 3.0 s |
| 2,002 | 29,736,979 | 6,445 | 3.5 s | 30,313,695 | 6,744 | 3.7 s |
| 4,002 | 55,088,087 | 6,462 | 5.1 s | 56,321,127 | 6,758 | 5.1 s |

A change is a regression when heartbeats per equation rise with the instruction count. Compare
whole-file heartbeats at one size only between two trees on one toolchain; a difference of a few
hundred is noise.
