# Instruction lookup equations

<!-- audience: maintainers -->

`Extracted.lean` states one `@[cil_code ↓]` equation per instruction,
`method{n}_instruction{pc} : method{n}.code[pc]? = some op`, which the stepping tactics rewrite
with. The extractor names the suffix of the code list at every 16th instruction
(`method{n}_suffix{start}`), proves each named suffix from the one before it with
`CIL.CodeSuffix.advance`, and proves each equation from the suffix that starts its block with
`CIL.CodeSuffix.lookup`. No proof walks more than 16 cells of the code list, so the equations of
a method cost time linear in its length. The equations depend on `propext` alone.

`cil_instruction_equations`, which a hand-written body calls and the template emitter writes
after each generated template, declares the same suffixes and proofs for its body:
`body_suffix{start}`, `body_suffix{start}_placed` and `body_instruction{pc}`, each over the
body's parameters. It builds the proof terms directly, so an equation costs it about 6,400
heartbeats where the extractor's written equation costs 58,000 to elaborate.

Proving each equation by `rfl` against the whole list walks `pc` cells of it. At 1,002
instructions Lean's profiler attributes 41.6 s of elaboration, 14.5 s of type checking and 31.5 s
of attribute application to equations proved that way.

The emitted `set_option maxRecDepth` is 4096, or 16 per instruction of the longest method when
that is more, because Lean compiles and compares a code list one nested cell per instruction.

## Measurements

The fixture is one extracted method, `word = word * y + x;` repeated, at the scalar profile.
Each file was compiled with `lean -o` on a 32-core Windows machine under Lean 4.35.0 while other
builds ran, so the table reports CPU seconds rather than elapsed time. Heartbeats come from
`IO.getNumHeartbeats` at the end of the file with `-DElab.async=false`; they repeat to within
a few hundred between runs. "By `rfl`" is the same file with every equation proved by `rfl` and
no suffixes; "no equations" omits the equations and suffixes and leaves the certificate.

| Instructions | By `rfl`, CPU | Suffixes, CPU | By `rfl`, `.olean` bytes | Suffixes, `.olean` bytes |
| ---: | ---: | ---: | ---: | ---: |
| 250 | 18.4 s | 13.7 s | 2,604,232 | 2,667,104 |
| 502 | 44.3 s | 25.3 s | 5,063,800 | 5,189,584 |
| 1,002 | 121.4 s | 47.9 s | 9,936,296 | 10,185,664 |
| 2,002 | 426.0 s | 99.6 s | 19,686,600 | 20,184,752 |
| 4,002 | 1,562.8 s | 219.1 s | 39,196,360 | 40,190,512 |

The `rfl` rows at 2,002 and 4,002 instructions needed `maxRecDepth` raised by hand to 16384 and
65536; at the fixed 4096 the raw method definitions fail to compile.

| Instructions | By `rfl`, heartbeats | Suffixes, heartbeats | No equations, heartbeats | Per equation, suffixes |
| ---: | ---: | ---: | ---: | ---: |
| 250 | 149,774,266 | 77,016,166 | 62,404,088 | 58,448 |
| 502 | 450,789,237 | 146,981,270 | 117,564,713 | 58,599 |
| 1,002 | 1,518,136,028 | 286,512,352 | 227,744,739 | 58,650 |
| 2,002 | 5,529,331,245 | 567,822,803 | 450,264,647 | 58,720 |
| 4,002 | not measured | 1,137,863,847 | 902,767,340 | 58,745 |

The certificate without equations costs 225,000 to 250,000 heartbeats per instruction at every
size, so the whole file is linear in heartbeats. Its CPU time per instruction still rises from
0.040 s at 2,002 instructions to 0.050 s at 4,002 (80.6 s and 198.6 s), which the equations do
not account for.

Small extractions keep their cost:

| Method | Instructions | By `rfl`, heartbeats | Suffixes, heartbeats |
| --- | ---: | ---: | ---: |
| `Arithmetic::Add` | 4 | 9,653,980 | 9,688,391 |
| `StaticVirtualDefaults::SpendRefunding` and its four callees | 37 | 109,674,829 | 109,829,219 |
| `BinarySpans::TryReadBig` | 126 | 120,008,174 | 102,907,340 |

## The command and generated templates

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
of the instructions with a logarithmic lookup compiled in the same time and size as the suffixes
(10.5 s against 10.1 s for the method and its equations alone) and needs a new inductive type
with its own correctness proof. One checked table of all lookups with each equation projected
from it took 242.7 s, twice the `rfl` time, since projection `pc` walks `pc` conjuncts.

## The `lookups` suite

The `lookups` suite extracts the fixture at 502 and 2,002 instructions and compiles three files
at each length: the extraction, its code as a body with a parameter under
`cil_instruction_equations`, and its generated template. It fails when the longer file of a
pair costs more than 1.25 times the heartbeats per instruction of the shorter one. It measures
0.99 times for the extraction and 1.01 times for the body and the template; `rfl` proofs
measure 3.09 times for the extraction, and the body's `rfl` rows above come to 3.7 times.
