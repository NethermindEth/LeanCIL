/// <summary>A suite that runs one fixture script, in its own process and with its own cache.</summary>
internal sealed record IndependentSuite(string Name, string Script, string Description, string[]? Arguments = null);

/// <summary>
/// Every name <c>scripts/Test.cs --suite</c> accepts. The suite table in docs/VALIDATION.md must list
/// exactly these, and CI selection reads each suite's entry point from here.
/// </summary>
internal static class VerificationSuites
{
    /// <summary>The runner's own in-process checks, which also run when no suite is named.</summary>
    internal const string Core = "core";

    /// <summary>
    /// The suites whose verified outputs are proofs about extracted methods: examples and generated
    /// outlines. Proof cost measures each one's outputs, in the CI job that verified them.
    /// </summary>
    internal static readonly string[] ProofSuites =
    [
        Core, "loops", "outlines-control", "outlines-objects", "outlines-buffers", "structoutlines",
        "receiveroutlines", "wordreader", "savedwordreader"
    ];

    /// <summary>
    /// The directories under <c>artifacts</c> where each proof suite leaves its verified outputs. A
    /// name also covers the directory a run suffixes with a hexadecimal identifier. Proof cost takes a
    /// suite's rows from these alone and fails when a proof suite verifies an output outside them.
    /// </summary>
    internal static readonly Dictionary<string, string[]> ProofOutputs = new(StringComparer.Ordinal)
    {
        [Core] =
        [
            "Add", "AddModel", "Alias", "Calls", "CallsSummary", "CertificateReuse", "Choose", "ConsumerBatchA",
            "ConsumerBatchB", "ConsumerBatchContract", "ConsumerSupportUnion", "CountCallsSummary", "DecodedAdd",
            "Escape", "Hardware",
            "IdentitySummary", "InitializedTypes", "LargeStruct", "PastEnd", "ProofBindingFamilies", "RepeatedSummary",
            "StaticData", "Struct", "StructCopy", "SummaryCalls", "SupportExtractionCache", "VectorSummary",
            "VerificationReuse", "WrongAdd"
        ],
        ["loops"] = ["Loops", "WordArrayOutlines"],
        ["outlines-control"] = ["ProofOutlines/control"],
        ["outlines-objects"] = ["ProofOutlines/objects"],
        ["outlines-buffers"] = ["ProofOutlines/buffers"],
        ["structoutlines"] = ["StructOutlines"],
        ["receiveroutlines"] = ["ReceiverLoopOutlines"],
        ["wordreader"] = ["WordReaderOutlines"],
        ["savedwordreader"] = ["SavedWordReaderOutlines"]
    };

    /// <summary>The single-fixture suites in the order a full run executes them.</summary>
    internal static readonly IndependentSuite[] Independent =
    [
        new("templates", "Tests/ProfileTemplates.cs",
            "shared profile templates, exact instruction equations and checked bindings"),
        new("workspace", "Tests/ProofWorkspace.cs",
            "per-method editor extractions, watch refresh and ordinary fresh certification"),
        new("imports", "Tests/ContractImports.cs",
            "implementation-bound contract imports and conditional caller verification"),
        new("closures", "Tests/ProgramClosures.cs",
            "summaries proved over a method's closure, applied in programs that hold the closure at other " +
            "indices or its identical methods at one index, and refuted relocations onto other bytes or " +
            "differing bodies"),
        new("exceptionlint", "Tests/ExceptionLint.cs", "diagnostic XML exception drift without proof claims"),
        new("contracts", "Tests/UniversalContracts.cs",
            "universal checked contracts, caller memory preservation and incorrect implementations"),
        new("evidence", "Tests/ExtractionEvidence.cs",
            "independent extraction certificates, malformed evidence rejection, the metadata decoder's method " +
            "names against Cecil's and framework argument guards"),
        // Split from evidence so neither job approaches the CI timeout.
        new("dispatch", "Tests/DispatchEvidence.cs",
            "constrained and managed dispatch, constant calls, stack allocation and pinned compiler coverage"),
        new("loops", "Tests/Loops.cs",
            "cyclic control-flow validation, universal termination and negative contracts"),
        new("outlines-control", "Tests/ProofOutlines.cs",
            "control-flow and value proof outlines", ["--group", "control"]),
        new("outlines-objects", "Tests/ProofOutlines.cs",
            "object and reference-array proof outlines", ["--group", "objects"]),
        new("outlines-buffers", "Tests/ProofOutlines.cs",
            "word-array, span and array-field proof outlines", ["--group", "buffers"]),
        new("structoutlines", "Tests/StructOutlines.cs", "struct value and field proof outlines"),
        new("receiveroutlines", "Tests/ReceiverLoopOutlines.cs", "struct receiver loop proof outlines"),
        new("wordreader", "Tests/WordReaderOutlines.cs", "class helper and array-read component proofs"),
        new("savedwordreader", "Tests/SavedWordReaderOutlines.cs", "numeric local homes across class helper calls"),
        new("generics", "Tests/GenericMethods.cs",
            "C# and F# generic method specialization, provenance and rejection proofs"),
        new("blocks", "Tests/Blocks.cs", "block memory, alignment prefixes, runtime comparisons and safety faults"),
        new("unsafe", "Tests/UnsafeLayouts.cs",
            "layout-based Unsafe sizes, reference offsets and metadata validation"),
        new("math", "Tests/IntegerMath.cs", "integer Math helpers, BigMul, runtime faults and universal minimum"),
        new("intrinsics", "Tests/ExactIntrinsics.cs",
            "exact SIMD call signatures, byte shuffles, AES rounds, unspecified lanes, opaque locals, profile " +
            "rejection and the library of generated runtime comparisons"),
        new("divrem", "Tests/TupleDivision.cs",
            "X86Base.X64.DivRem and Math.DivRem through ValueTuple fields, divide faults and layout rejection"),
        new("fsharp", "Tests/FSharp.cs", "F# arithmetic, branches, calls, references and struct construction"),
        new("constructors", "Tests/Constructors.cs",
            "struct construction, initialized temporaries and constructor faults"),
        new("instance", "Tests/StructMethods.cs", "struct instance calls, managed this and constructor calls"),
        new("nested", "Tests/NestedStructs.cs", "nested struct layout, snapshots, copies and metadata validation"),
        new("enums", "Tests/Enums.cs", "integer enum storage, flags, runtime comparisons and metadata validation"),
        new("cli", "Tests/CliVerification.cs", "CLI proof verification and incorrect implementation rejection"),
        new("failures", "Tests/FailureReporting.cs",
            "failure reports that classify and locate each failed obligation"),
        new("integer", "Tests/IntegerOpcodes.cs",
            "integer opcode encodings, boundary cases and universal negation proofs"),
        new("narrow", "Tests/NarrowIntegers.cs",
            "narrow integer conversions, storage, method boundaries and rejection proofs"),
        new("primitive", "Tests/PrimitiveOperations.cs",
            "primitive memory, switch, sizeof and rejection proofs, and strings as opaque references"),
        new("division", "Tests/Division.cs", "integer division and remainder runtime comparisons and proofs"),
        new("checked", "Tests/CheckedArithmetic.cs", "checked integer arithmetic runtime comparisons and proofs"),
        new("conversions", "Tests/CheckedConversions.cs",
            "checked integer conversions runtime comparisons and proofs"),
        new("layout", "Tests/SequentialLayout.cs",
            "sequential struct layout, runtime offsets and metadata validation"),
        new("bits", "Tests/RuntimeBits.cs",
            "portable bit operations, endian reversal and runtime signature validation"),
        new("copy", "Tests/TypedCopy.cs", "typed copies, aliases, byte snapshots and rejection proofs"),
        new("arguments", "Tests/Arguments.cs", "argument assignment, addressing, aliases and lifetime proofs"),
        new("native", "Tests/NativeIntegers.cs", "native integer storage, arithmetic and runtime comparisons"),
        new("identity", "Tests/MethodIdentity.cs",
            "methods bound by signature or call shape that survive renumbering and renaming, and typed identity " +
            "display"),
        new("labels", "Tests/StructuralLabels.cs", "loop-head and call-site labels that survive inserted statements"),
        new("names", "Tests/DebugNames.cs", "PDB local names and source locations that never change extraction"),
        new("symbols", "Tests/ConsumerSymbols.cs",
            "consumer proofs naming PDB locals through helper modules, bound only where imported"),
        new("callers", "Tests/MethodContract.cs",
            "caller proofs that survive reimplemented helpers through their contracts"),
        new("construction", "Tests/ConstructContract.cs",
            "caller proofs that survive reimplemented constructors through their contracts"),
        new("outcomes", "Tests/OutcomeContract.cs",
            "outcome contracts that name exactly when each exception is thrown"),
        // Split from evidence: each fixture alone runs for minutes, so they take separate runners.
        new("scaling", "Tests/TranslationScaling.cs",
            "compositional certificate for a six-method call graph and its consumer replay, and the header and " +
            "per-method struct layout checks at a per-layout cost that does not grow with the table, and the " +
            "generic owner index library"),
        new("excluded", "Tests/ExcludedBranchScaling.cs",
            "hundreds of excluded and live sites at the default heartbeat budget"),
        new("lookups", "Tests/LookupScaling.cs",
            "lookup equations of extracted methods, hand-written bodies and templates, and the scalar " +
            "certificate of array element addresses, loaded and addressed integer locals and native-int locals " +
            "consumed by calli, the closed argument storage of those native-int locals, and the feature " +
            "certificate of local loads, stores and addresses, at a per-instruction cost that does not grow " +
            "with the method or with locals holding no known word and grows linearly with the known facts, " +
            "embeddings of bodies with many calls at a per-call kernel cost that does not grow with the calls, " +
            "type identity equality at a cost that does not grow with the name, the method name clause of the " +
            "call operand check and the encoding of a metadata name at a per-byte cost that does not grow with " +
            "the name, the bytes of a name stored as its bytes at a per-byte cost that does not grow with the " +
            "name and, with the name's definition, below the cost of the bytes of its literal, and one native " +
            "method table step and one load of its first entry at a kernel cost that " +
            "does not grow with the table's entries; the managed-call check of a body with many call sites at " +
            "a per-site cost that does not grow with the call sites; the call check and the evidence theorem of " +
            "a body with no call at a per-statement and a total cost that do not grow with the body; the proof " +
            "that 8, 32 and 128 evidence records decode to their methods at a per-record cost that does not grow " +
            "with the records; the closure of a method in a program at a cost per unit of methods times program " +
            "length plus link callees that does not grow with the methods, the callees or the program; the " +
            "argument facts of " +
            "cil_resolution_facts and the reads through them at a per-argument cost that does not grow with " +
            "the parameters, and its static site facts and the reads through them at a per-site cost that does " +
            "not grow with the sites; the program's static identity check at a per-site cost that grows less " +
            "than 1.35 times from 8 to 32 to 128 sites; the array element shape facts of " +
            "cil_resolution_facts and the reads " +
            "through them at a per-element-type cost that does not grow with the layouts or the sites naming " +
            "each type; a runtime model lookup at a kernel cost that does not grow with the model table, and " +
            "the runtime model agreement check at a per-site cost that does not grow with the call sites; the " +
            "shape facts of cil_field_shape and the reads through them at a per-field cost that grows less " +
            "than 1.35 times from 8 to 32 to 128 fields in one struct and from 8 to 32 to 128 to 512 fields in " +
            "a struct each, and the facts of cil_value_shape and their reads at a per-type cost that grows " +
            "less than 1.35 times from 8 to 32 to 128 to 512 struct types; locating a class field on an " +
            "instance, and rejecting a field whose owner is outside the instance's lineage, at a per-base cost " +
            "that grows less than 1.35 times from 2 to 8 to 32 bases; the kernel check of one body at a cost " +
            "independent of the methods and metadata rows of its extraction, and at a per-instruction cost that " +
            "does not grow with the string tokens of the body; the kernel's selection of a calli " +
            "body at a cost linear in the length of the pointer's owner; raw value opcode decoding and the " +
            "method decoded from a raw body at a per-instruction kernel cost that does not grow with the body, " +
            "and the method cil_decoded_method defines from that body at a per-instruction cost that does not " +
            "grow with the body; and the certificate index, feature getter, layout accumulation and " +
            "projection, and extraction home index libraries"),
        new("gates", "Tests/ProofGates.cs",
            "manifest project builds, extraction, named profiles, per-variant and templated proofs, " +
            "witness refutations, kernel statement comparison, binding catalogs, planned groups, " +
            "changed-source selection and mutation expectations"),
        new("stepping", "Tests/SteppingScaling.cs",
            "stepping of scalar, memory, hypotheses-in-scope and snapshot bodies with per-instruction work and " +
            "proof-size budgets and a per-hypothesis heartbeat limit"),
        new("assemblies", "Tests/MultiAssembly.cs",
            "bodies, layouts and generic instantiations from pinned referenced assemblies, attribution and " +
            "substitution rejection, the strict binding library and audit, and the checked-in strict binding " +
            "fixture module"),
        new("pool", "Tests/ItemPool.cs",
            "object pool reuse, creation, exhaustion, null-pool and free-list search proofs and the mutations " +
            "they reject"),
        new("blockers", "Tests/Blockers.cs", "admission reports with deduplicated blockers, call chains, " +
            "profile-excluded branches, runtime-async refusal, self-admission, the admitted hole corpus and the " +
            "self-admitted, example and fixture methods defined from their decoder"),
        new("audit", "Tests/OleanAudit.cs",
            "theorem audits of replayed oleans, deep certificate reuse, and rejection of changed images, " +
            "proofs, replay inputs and auditors"),
        new("docs", "Tests/DocSnippets.cs",
            "documentation Lean snippets, cited library names and documented commands against the library and tool")
    ];

    /// <summary>Every suite name: core, the single-fixture suites, then the export partitions.</summary>
    internal static string[] Names() =>
    [
        Core, .. Independent.Select(suite => suite.Name),
        .. ExportVerificationSuites.Plan().Select(entry => entry.Name)
    ];
}
