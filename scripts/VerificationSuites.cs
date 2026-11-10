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
            "Add", "AddModel", "Alias", "Calls", "Choose", "ConsumerBatchA", "ConsumerBatchB",
            "ConsumerSupportUnion", "Escape", "Hardware", "InitializedTypes", "LargeStruct", "PastEnd",
            "StaticData", "Struct", "StructCopy", "VerificationReuse", "WrongAdd"
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
        new("exceptionlint", "Tests/ExceptionLint.cs", "diagnostic XML exception drift without proof claims"),
        new("contracts", "Tests/UniversalContracts.cs",
            "universal checked contracts, caller memory preservation and incorrect implementations"),
        new("evidence", "Tests/ExtractionEvidence.cs",
            "independent extraction certificates and malformed evidence rejection"),
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
            "exact SIMD call signatures, byte shuffles, AES rounds, unspecified lanes, opaque locals and " +
            "profile rejection"),
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
        new("primitive", "Tests/PrimitiveOperations.cs", "primitive memory, switch, sizeof and rejection proofs"),
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
            "methods bound by signature or call shape that survive renumbering and renaming"),
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
            "compositional certificate for a six-method call graph and its consumer replay"),
        new("excluded", "Tests/ExcludedBranchScaling.cs",
            "hundreds of excluded and live sites at the default heartbeat budget"),
        new("lookups", "Tests/LookupScaling.cs",
            "lookup equations of extracted methods, hand-written bodies and templates at a per-instruction " +
            "cost that does not grow with the method"),
        new("gates", "Tests/ProofGates.cs",
            "manifest extraction, profiles, changed-source selection and mutation expectations"),
        new("assemblies", "Tests/MultiAssembly.cs",
            "bodies, layouts and generic instantiations from pinned referenced assemblies, attribution and " +
            "substitution rejection"),
        new("pool", "Tests/ItemPool.cs",
            "object pool reuse, creation, exhaustion, null-pool and free-list search proofs and the mutations " +
            "they reject"),
        new("blockers", "Tests/Blockers.cs", "admission reports with deduplicated blockers, call chains, " +
            "profile-excluded branches and self-admission"),
        new("audit", "Tests/OleanAudit.cs",
            "theorem audits of replayed oleans that proof elaborators, initializers and substituted artifacts " +
            "cannot forge"),
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
