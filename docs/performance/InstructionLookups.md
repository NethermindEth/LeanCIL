# Instruction lookup equations

<!-- audience: maintainers -->

`cil_instruction_equations body` states one `@[cil_code ↓]` equation per instruction of a method
body, `body_instruction{pc} : (body xs).code[pc]? = some op`, which the stepping tactics rewrite
with. The extractor writes the command after each `method{n}` of `Extracted.lean`, the template
emitter after each generated template, and a hand-written body calls it itself. The command names
the suffix of the code list at every 16th instruction (`body_suffix{start}`), proves each named
suffix from the one before it with `CIL.CodeSuffix.advance` (`body_suffix{start}_placed`), and
proves each equation from the suffix that starts its block with `CIL.CodeSuffix.lookup`. No proof
walks more than 16 cells of the code list, so the equations of a method cost time linear in its
length. The equations depend on `propext` alone.

Proving each equation by `rfl` against the whole list walks `pc` cells of it. At 1,002
instructions Lean's profiler attributes 41.6 s of elaboration, 14.5 s of type checking and 31.5 s
of attribute application to equations proved that way.

The command builds its declarations as terms. The same suffixes and proofs written out in
`Extracted.lean` take 58,000 heartbeats per equation to parse and elaborate, where the command
takes 6,400.

The `set_option maxRecDepth` emitted in `Extracted.lean` and `Templates.lean` is 4096, or 16 per
instruction of the longest method when that is more, because Lean compiles and compares a code
list one nested cell per instruction.

## Extracted methods

The fixture is one extracted method, `word = word * y + x;` repeated, at the scalar profile.
Each file was compiled with `lean -o` on a 32-core Windows machine under Lean 4.35.0 while other
builds ran, so the tables report CPU seconds rather than elapsed time. Heartbeats come from
`IO.getNumHeartbeats` at the end of the file with `-DElab.async=false`; they repeat to within
a few hundred between runs. "By `rfl`" is the same file with every equation written out and
proved by `rfl`; "written suffixes" writes out the suffix definitions and proofs the command
declares; "no equations" omits the command and leaves the certificate.

CPU seconds compare within one session only. The first two CPU columns come from one session and
the last two from a later one.

| Instructions | By `rfl`, CPU | Written suffixes, CPU | Written suffixes, later CPU | Command, CPU |
| ---: | ---: | ---: | ---: | ---: |
| 250 | 18.4 s | 13.7 s | 9.4 s | 7.6 s |
| 502 | 44.3 s | 25.3 s | 17.8 s | 13.6 s |
| 1,002 | 121.4 s | 47.9 s | 35.9 s | 26.8 s |
| 2,002 | 426.0 s | 99.6 s | 72.0 s | 58.3 s |
| 4,002 | 1,562.8 s | 219.1 s | 158.6 s | 137.9 s |

| Instructions | By `rfl`, `.olean` bytes | Written suffixes, `.olean` bytes | Command, `.olean` bytes |
| ---: | ---: | ---: | ---: |
| 250 | 2,604,232 | 2,667,104 | 2,628,408 |
| 502 | 5,063,800 | 5,189,584 | 5,111,408 |
| 1,002 | 9,936,296 | 10,185,664 | 10,029,288 |
| 2,002 | 19,686,600 | 20,184,752 | 19,872,280 |
| 4,002 | 39,196,360 | 40,190,512 | 39,566,040 |

The `rfl` rows at 2,002 and 4,002 instructions needed `maxRecDepth` raised by hand to 16384 and
65536; at a fixed 4096 the raw method definitions fail to compile.

| Instructions | By `rfl`, heartbeats | Written suffixes, heartbeats | Command, heartbeats | No equations, heartbeats |
| ---: | ---: | ---: | ---: | ---: |
| 250 | 149,774,266 | 77,145,205 | 64,133,492 | 62,534,629 |
| 502 | 450,789,237 | 147,110,105 | 120,915,482 | 117,695,162 |
| 1,002 | 1,518,136,028 | 286,640,403 | 234,316,408 | 227,875,207 |
| 2,002 | 5,529,331,245 | 567,951,213 | 463,305,964 | 450,395,121 |
| 4,002 | not measured | 1,137,991,270 | 928,770,174 | 902,897,844 |

| Instructions | Per equation, written suffixes | Per equation, command |
| ---: | ---: | ---: |
| 250 | 58,442 | 6,395 |
| 502 | 58,595 | 6,415 |
| 1,002 | 58,648 | 6,428 |
| 2,002 | 58,719 | 6,449 |
| 4,002 | 58,744 | 6,465 |

The certificate without equations costs 225,000 to 250,000 heartbeats per instruction at every
size, so the whole file is linear in heartbeats and the equations are under 3% of it. Its CPU
time per instruction still rises from 0.029 s at 2,002 instructions to 0.034 s at 4,002 (57.9 s
and 135.0 s), which the equations do not account for.

Small extractions:

| Method | Instructions | By `rfl`, heartbeats | Written suffixes, heartbeats | Command, heartbeats |
| --- | ---: | ---: | ---: | ---: |
| `Arithmetic::Add` | 4 | 9,653,980 | 9,702,083 | 9,528,412 |
| `StaticVirtualDefaults::SpendRefunding` and its four callees | 37 | 109,674,829 | 109,842,893 | 108,070,129 |
| `BinarySpans::TryReadBig` | 126 | 120,008,174 | 102,920,999 | 96,240,822 |

## Hand-written bodies and generated templates

The body is the fixture method's code as a definition followed by `cil_instruction_equations`;
the template is `leancil templates` over the scalar and `x64-v3` extractions of the method,
compiled as emitted. "By `rfl`" is the command proving each equation by `Eq.refl` against the
whole list, and for the template also one `#print axioms` per equation; those template rows at
2,002 and 4,002 instructions needed `maxRecDepth` raised by hand. "Per equation" subtracts the
same file without the command.

| Instructions | Body by `rfl`, CPU | Body, CPU | Template by `rfl`, CPU | Template, CPU |
| ---: | ---: | ---: | ---: | ---: |
| 250 | 3.6 s | 2.6 s | 3.9 s | 2.5 s |
| 502 | 5.9 s | 2.7 s | 6.0 s | 2.8 s |
| 1,002 | 13.4 s | 3.1 s | 14.3 s | 3.0 s |
| 2,002 | 45.7 s | 3.5 s | 47.0 s | 3.7 s |
| 4,002 | 160.0 s | 5.1 s | 157.3 s | 5.1 s |

| Instructions | Body by `rfl`, heartbeats | Body, heartbeats | Per equation by `rfl` | Per equation |
| ---: | ---: | ---: | ---: | ---: |
| 250 | 18,539,930 | 7,826,637 | 49,236 | 6,382 |
| 502 | 56,039,171 | 10,942,760 | 96,243 | 6,409 |
| 1,002 | 200,637,321 | 17,166,259 | 189,527 | 6,422 |
| 2,002 | 769,775,815 | 29,736,979 | 376,095 | 6,445 |
| 4,002 | 3,027,594,441 | 55,088,087 | 749,218 | 6,462 |

| Instructions | Template by `rfl`, heartbeats | Template, heartbeats | Per equation by `rfl` | Per equation |
| ---: | ---: | ---: | ---: | ---: |
| 250 | 19,053,923 | 7,819,437 | 51,626 | 6,687 |
| 502 | 57,538,797 | 11,018,590 | 99,378 | 6,708 |
| 1,002 | 205,190,961 | 17,408,327 | 194,128 | 6,719 |
| 2,002 | 784,830,234 | 30,313,695 | 383,625 | 6,744 |
| 4,002 | 3,081,237,144 | 56,321,127 | 762,609 | 6,758 |

A template reports the axioms of its last equation alone. That proof reaches every named suffix
and so every instruction, and each report walks all it reaches: one report per equation costs
399 million heartbeats at 4,002 instructions, where the template's 4,002 equations cost
27 million.

## Other shapes

Two other proof shapes were measured on the 1,002-instruction file and not kept. A balanced tree
of the instructions with a logarithmic lookup compiled in the same time and size as written
suffixes (10.5 s against 10.1 s for the method and its equations alone) and needs a new inductive
type with its own correctness proof. One checked table of all lookups with each equation
projected from it took 242.7 s, twice the `rfl` time, since projection `pc` walks `pc` conjuncts.

## The `lookups` suite

The `lookups` suite extracts the fixture at 502 and 2,002 instructions and compiles three files
at each length: the extraction, its code as a body with a parameter under
`cil_instruction_equations`, and its generated template. It fails when the longer file of a
pair costs more than 1.25 times the heartbeats per instruction of the shorter one. It measures
0.99 times for the extraction and 1.01 times for the body and the template; equations proved
by `rfl` measure 3.09 times for the extraction, and the body's `rfl` rows above come to 3.7
times.
