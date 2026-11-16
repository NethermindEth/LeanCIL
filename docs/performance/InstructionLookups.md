# Instruction lookup equations

<!-- audience: maintainers -->

This page describes what the lookup equations of a method cost, and how to check that the cost
stays linear in the method's length. Read it before changing `cil_instruction_equations`,
`CIL.CodeSuffix` or the form in which the extractor and the template emitter write a method's
code.

## Cost properties

[Binding proofs](../PROOFS-BINDING.md#instruction-equations-for-parametric-bodies) describes the
equations and the suffix declarations of `cil_instruction_equations`. The command proves each
named suffix from the one before it with `CIL.CodeSuffix.advance` and each equation from the
suffix that starts its block with `CIL.CodeSuffix.lookup`. No proof walks more than 16 cells of
the code list, so each equation costs about 6,400 heartbeats at any method length. The equations
depend on `propext` alone.

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

The suite fails when a ratio exceeds 1.15. Linear equations measure 0.99 for the extraction and
1.01 for the body and the template; equations proved against the whole list measure 3.09 for the
extraction and about 3.7 for the body. A ratio that rises toward 1.15 means some proof or
elaboration step walks the code list again. The suite also fails when a `cil_lookup` at a
computed pc costs more than 1.15 times as much per case at 16 repeated segments as at 4.

The suite also measures `decide +kernel` on two `CIL.TypeIdentity` values whose names are 20 or 80
characters long and differ only in their last character, less the same statement closed with
`sorry`. A name is one code, so the decision costs about 7,500 heartbeats for equal names and
8,300 for unequal ones at either length; one enclosing type adds about 2,500. The suite fails when the 80-character case costs more
than 1.05 times the 20-character case or when either costs more than 9,500 heartbeats. This
check takes about 5 seconds.

Exception decisions compare `CIL.ExceptionType` constructors. The equality, inequality,
CLR mapping and optional outcome rows each allow 2,000 to 9,500 kernel heartbeats. Using
`applicationException` instead of `format` may increase the cost by at most 1.05 times.

The suite also measures `decide +kernel` on one `add` of an int32 offset to a native method
table of 16, 64 and 256 entries, less the same statement closed with `sorry`. Each table and its
static storage are definitions outside the decision, so the proof of `MethodTable.counted` is
checked once there and not in the measured statement. The step reads `MethodTable.entryCount`,
not the entries, and costs about 24,700 heartbeats at each size; geometry checks that read
`targets.size` cost 29,500, 41,800 and 90,900. The suite fails when the cost at 64 or 256 entries
exceeds 1.15 times the cost at 16.

The same files measure `loadNativeTable` of the table's first and of its last entry. The load
bounds the entry index by `MethodTable.entryCount`, so the first entry costs about 27,400
heartbeats at each size; a bound read from `targets[index]?`, which walks the array to its size,
costs 30,100, 42,700 and 92,800. Reading entry i still walks i cells of the literal array, which
the kernel holds as a list, so the last entry costs 36,000, 63,700 and 174,300, about 576
heartbeats per index at each size. The suite fails when the first entry's cost at 64 or 256
entries exceeds 1.15 times the cost at 16, or when the last entry's cost beyond the first's,
divided by its index, does. Run these rows alone with
`dotnet run --file Tests/LookupScaling.cs -- --native-table-only`.

The suite also measures `decide +kernel` on the name clause of the call and field operand checks,
`MetadataName.spells`, for names of 20, 80 and 320 bytes that share all but their last byte, less
the same statements closed with `sorry`. The clause reads the name's code back into bytes: about
41,300, 151,400 and 589,600 heartbeats, or 2,070, 1,890 and 1,840 per byte. The suite fails when
the cost per byte grows more than 1.15 times from one length to the next. Run this row alone with
`dotnet run --file Tests/LookupScaling.cs -- --metadata-name-only`.

The suite also measures `decide +kernel` on runtime model lookups of the first, middle and last
entry of a table of 16 and of 256 entries, less the same statements closed with `sorry`.
`model_table%` writes the table as a literal balanced tree keyed by method name code, so a lookup
walks at most four more levels in the larger table and compares one method reference at the leaf:
about 67,100 and 69,000 heartbeats for the first entry, 65,400 at both sizes for the middle entry,
which is the root, and 67,000 and 69,200 for the last. A scan of the entries would make the last
entry cost more. The suite fails when any position costs more than 1.05 times as much at 256
entries as at 16. The same file measures `ModelsAgree` over methods of 8, 32 and 128 live call
sites, each calling a distinct modelled method: about 212,000, 687,100 and 2,593,900 heartbeats, or
26,500, 21,500 and 20,300 per site. The suite fails when the cost per site grows more than 1.15
times from one count to the next. Run these rows alone with
`dotnet run --file Tests/LookupScaling.cs -- --model-table-only`.

The suite also measures `cil_kernel_rfl` on `CIL.Safety.indirectTarget`, the selection of a
`calli` body, for a pointer whose owner is 64, 256 or 1,024 bytes long and a catalog whose second
entry holds the same owner, less the same statement closed with `sorry`. The kernel compares
the owners byte by byte, at 8,300 to 8,900 heartbeats per byte: 572,000, 2,165,000 and 8,533,000
heartbeats. The suite fails when the cost grows more than 1.1 times as fast as the length from one
size to the next. Run this row alone with
`dotnet run --file Tests/LookupScaling.cs -- --indirect-target-only`.

The suite also checks the kernel heartbeats of `ScalarFlowValid` on generated bodies of 128, 256
and 512 array element addresses, each followed by a branch, with and without a `readonly.`
prefix, less the heartbeats of stating the same certificate. It fails when the cost per address
at 256 or 512 exceeds 1.15 times the cost at 128. The readonly rule reads neighbouring
instructions from a `FlowIndex` and branch destinations from a `Std.TreeSet`, both built once
per body, and measures 1.02 for plain and 1.09 for prefixed addresses. A rule that scans the body
at each address measures 2.6 for plain and 3.4 for prefixed addresses without the branches.

It also checks the kernel heartbeats per instruction of `ScalarFlowValid` on generated bodies of
128, 256 and 512 locals, each stored once and then loaded or addressed once, less the heartbeats
of stating the same certificate. Integer locals take a constant and are popped after a load or
after `ldloca`; native-int locals take a method
address and are consumed by `calli`, which makes each a pointer local. For the pointer locals it
also checks `closedArguments`. The suite fails when the cost per instruction at 256 or 512 locals
exceeds 1.25 times the cost at 128. The scalar check and fold discovery read local types from a
`FlowIndex` and pointer locals from a `Std.TreeSet`, built once per body, as does the closed
argument storage. They measure 1.01 for loaded, 1.12 for addressed and 1.08 for pointer locals,
and 1.20 for the closed argument storage, whose set lookups cost the logarithm of the locals.
Checks that walk the locals list or the pointer local list at each site measure 1.33, 1.54, 1.62
and 2.33.

The suite also checks the kernel heartbeats of `FeatureFlowValid` on generated bodies of 256, 1,024
and 4,096 instructions that cycle `ldloc.s`, `stloc.s`, `ldloca.s` and `pop` over four `int32`
locals, less the heartbeats of stating the same certificate. It fails when the cost per instruction
at 1,024 or 4,096 exceeds 1.25 times the cost at 256. A local load, store or address is checked by
its opcode and index, and the cost per instruction measures 1.00 at 1,024 and 1.05 at 4,096.

It checks `FeatureFlowValid` on bodies of 2,049 instructions over 16, 64 and 256 `int32` locals as
well. Each segment loads, stores and addresses a local, then addresses the argument and stores a
constant into it. A feature state lists only the locals that hold a known word, as (local index,
word) pairs in increasing index order, so none of these states holds a local fact. The suite fails
when the cost per instruction at 64 or 256 locals exceeds 1.25 times the cost at 16; it measures
1.01 at 64 and 1.02 at 256.

A last body over 64 `int32` locals stores zero into the first 4, 16 or 64 of them. Then, in each
of 128 rounds, it stores a new word into one of those locals in turn and loads it back, so each of
the 512 loop states holds every stored fact. Its certificate is written out as literal states, as
the extractor writes them. The suite subtracts the cost of the stores alone, whose states together
hold about the square of the facts, and fails when the increment from 16 to 64 facts exceeds 4.5
times the increment from 4 to 16. Linear growth in the facts gives four; at the measured cost per
fact, a quadratic term of one heartbeat per pair of facts in each state exceeds 4.5, and a check
that also compares every pair of facts in each state measures 10.6. Reads, stores and weakening
walk the known facts, and each fact's eligibility is a lookup in a balanced index built once per
body. The ratio measures 4.05, about 400 kernel heartbeats per fact per state, or about 13 million
for 64 facts over 512 states.

The suite embeds a hand-written body built with `Method.withCode` and its own link table, one call per segment, into an
extraction with a dead block after each return, at 512 and 2,048 calls, and reads the kernel
heartbeats to recheck the lemma `cil_embed` states. It fails when the heartbeats per call grow
more than 1.15 times. The recheck costs about 56,800 heartbeats per call at both sizes, 1.00
times; link reads whose cost grows with the square of the calls measure 1.29. The suite also
embeds a body whose head branches over its first block to its second into an extraction that
places the second block first, at 256 and 1,024 calls, under the same limit. Its pc map descends
once, and the link reads and code lookups start again from the head of the table and the code
there; it costs about 53,800 heartbeats per call at both sizes.

The suite declares `cil_resolution_facts` for methods of 8, 32 and 128 `int32` parameters, once
with no parameter homes and once with every other argument homed, and reads every argument's
`Method.argumentAccess` through the facts with `simp only [cil_code]`. The facts walk the parameter
types and homes once, from named 16-entry suffixes built as the code suffixes are. The suite fails
when the heartbeats per argument of the facts, or of the reads, grow more than 1.35 times from
one size to the next. The facts cost about 7,400, 8,400 and 8,400 heartbeats per argument without
homes and 8,300, 10,500 and 10,800 with homes; a size below one block walks fewer entries, which
accounts for the lower cost at 8. The reads cost 11,200 to 12,500 heartbeats per argument at every
size.

The suite also declares `cil_resolution_facts` for methods of 8, 32 and 128 static sites at even
pcs and reads every site's `Method.staticAt` through the facts, under the same 1.35 limit per
site. The facts cost about 5,500, 7,000 and 7,000 heartbeats per site, lower at 8 for the same
reason, and the reads 22,100 to 23,500 heartbeats per site at every size.

The suite also declares `cil_resolution_facts` for a method whose raw method names one struct
element type per layout, at 8, 32 and 128 layouts, and reads every element's
`Method.elementShape` through the facts with `simp only [cil_code]`. Each struct fact reads its
raw and computed layout entries from named 16-entry suffixes of the layout lists, declared once
for the environment constant. The suite fails when the heartbeats per element type of the facts,
or of the reads, grow more than 1.35 times from one size to the next. The facts cost about 8,700,
11,300 and 11,400 heartbeats per element type, and the reads 14,200, 13,100 and 14,000; a size
below one block walks fewer entries, which accounts for the lower cost of the facts at 8.
The suite also names 8 element types from 8, 32 and 128 sites, so that most sites repeat a type,
and fails when the total heartbeats of the facts, or of the reads, grow more than 1.35 times from
one site count to the next. The facts cost about 69,700, 71,200 and 77,200 heartbeats and the
reads 113,700 at every site count, since the facts state one shape per element type.
Run this row alone with `dotnet run --file Tests/LookupScaling.cs -- --element-shape-only`.

The suite declares `cil_field_shape` for 8, 32 and 128 `int32` fields of one struct and for 8,
32, 128 and 512 fields each in a struct of its own, and `cil_value_shape` for 8, 32, 128 and 512
struct types, and reads every operand's `Method.fieldShape` or `Method.valueShape` through the
facts with `simp only [cil_code]` from a 512-instruction body. It fails when the heartbeats per
operand of the facts, or of the reads, grow more than 1.35 times from one size to the next. The
first fact of an environment names 16-entry suffixes of its layout lists, about 517,000
heartbeats at 512 layouts, and each fact reads its struct's entries from the suffix that starts
the entry's block, so an entry further into its block costs about 750 heartbeats more. The
compiled resolver that proposes each shape evaluates the environment once. The field facts cost
about 269,000, 280,000 and 326,000 heartbeats per field in one struct, where each fact walks the
struct's field list to its index, and 269,000, 271,000, 272,000 and 272,000 with a struct per
field; most of a field fact is the kernel deciding the storage of the field's `int32` type. The
value facts cost about 13,300, 15,900, 16,000 and 16,100 heartbeats per type. Facts that walk the
layout lists to the struct instead cost 293,000, 313,000, 386,000 and 672,000 heartbeats per
field and 38,000, 58,000, 131,000 and 417,000 per type. The reads cost 11,100 to 14,700
heartbeats per operand at every size.

The suite locates a field of the furthest base on a fresh instance whose class has 2, 8 and 32
bases, and rejects a field whose owner is outside that lineage, deciding membership in the
lineage with `decide`. It fails when the heartbeats per base of either grow more than 1.35 times
from one size to the next. Rejecting costs about 146,400, 65,900 and 45,000 heartbeats per base
and locating 135,800, 69,300 and 51,100, so the total grows linearly with the bases. Run this row alone with
`dotnet run --file Tests/LookupScaling.cs -- --lineage-only`.

The suite decides `ManagedCallsValid` on bodies of 64, 256 and 1,024 call sites, each followed by a
`nop`, with the literal link table the extractor writes, and reads the heartbeats of that one
command. It fails when the heartbeats per call site grow more than 1.35 times from one size to the
next. The check reads each pc's link by one walk beside the code and costs about 10,900, 9,500 and
9,100 heartbeats per call site; a scan of the table at each pc costs 41,500 and 133,900 at 64 and
256 sites and exhausts a 16 GB memory limit at 1,024. Run this row alone with
`dotnet run --file Tests/LookupScaling.cs -- --call-check-only`.

The suite states and proves with `decodedProgram?_eq_some` that 8, 32 and 128 evidence records
decode to their methods, given one decoding fact per record, and reads the heartbeats of that one
command. It fails when the heartbeats per record grow more than 1.25 times from one size to the
next. The proof costs about 14,300, 13,000 and 14,200 heartbeats per record. Run this row alone
with `dotnet run --file Tests/LookupScaling.cs -- --decoded-program-only`.

## Reference figures

The figures were measured on Windows with 32 cores and Lean 4.35.0, on the suite's method at the
scalar profile. Each file was compiled with `-DElab.async=false`, and heartbeats, read as the
suite reads them, repeat to within a few hundred between runs.
CPU seconds were taken while other builds ran and compare only within one session.

The first table measures the extraction, `Extracted.lean` with its certificate. "Without
equations" is the same file without the `cil_instruction_equations` command:

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

The second table measures the method's code as a hand-written definition followed by the
command, and the output of `leancil templates` over the scalar and `x64-v3` extractions,
compiled as emitted. "Per equation" subtracts the same file without the command:

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
