# Runtime bit-boundary duplicate work

`Tests/RuntimeBits.cs` used distinct 64-bit source patterns, then narrowed them to each
runtime parameter type. Different source patterns could become identical byte, short or
32-bit arguments. The fixture now removes duplicates after conversion. It retains every
rotation count as supplied, including negative and out-of-width counts.

The generated Lean proposition sets before and after the change were compared for all
37 methods, including their exact runtime-derived expected results. Every distinct
proposition is retained, and the new lists contain no duplicates. There are 5,634 unique
comparisons instead of 7,200 comparisons containing repetitions:

| Argument width | Previous unary comparisons | Unique unary comparisons |
| --- | ---: | ---: |
| 8 bits | 192 | 24 |
| 16 bits | 192 | 48 |
| 32 bits | 192 | 96 |
| 64 bits | 192 | 192 |

The two 32-bit rotation methods each retain 169 distinct comparisons instead of 208.
Native-width and 64-bit rotation cases are unchanged. Universal rotation/logarithm
proofs, two wrong-implementation refutations and nine invalid-call rejections are
unchanged and pass.

An isolated Apple M4 run of the complete `dotnet run --file Tests/RuntimeBits.cs` fixture
with Lean 4.35.0 took 44.10 seconds before and 42.27 seconds after. This single pair is an
indicative 4% wall-time saving; the 21.75% reduction in repeated propositions is exact.
Bounded parallel proof shards and unchanged validation/replay overhead limit the total
wall-time gain. Code-style analyzer validation found no unnecessary imports; the shared
verification helper retains its existing unassigned-field warning.

A repeat run passed in 37.71 seconds. The variation reinforces that the exact
claim-count reduction is stronger evidence than a precise percentage from these timings.
