-- Keep this order: it sets the order in which simp lemmas and instances from different
-- modules are tried in every consumer, so regrouping could change proof behaviour.

-- Reference semantics, feature profiles, method embeddings and extraction metadata
import CIL.AggregateMemory
import CIL.ExecutionLemmas
import CIL.Embedding.Basic
import CIL.Embedding.BaseStep
import CIL.Embedding.Tactic
import CIL.Features
import CIL.Imports
import CIL.InstructionEquations
import CIL.Instructions
import CIL.Layout
import CIL.Memory
import CIL.MemoryLemmas
import CIL.MethodBinding
import CIL.MethodIdentity
import CIL.StructuralLabels
import CIL.DebugNames
import CIL.ProfileEquivalence
-- Hardware intrinsics
import CIL.SIMD.AVX
import CIL.SIMD.AVX2
import CIL.SIMD.AVX512
import CIL.SIMD.AVX512DQ
import CIL.SIMD.AdvSimd
import CIL.SIMD.ArmBase
import CIL.SIMD.Availability
import CIL.SIMD.BMI1
import CIL.SIMD.BMI2
import CIL.SIMD.Evaluation256Lemmas
import CIL.SIMD.EvaluationLemmas
import CIL.SIMD.Incoming128
import CIL.SIMD.Intrinsics
import CIL.SIMD.LaneCarry
import CIL.SIMD.PackedLanes
import CIL.SIMD.SSE
import CIL.SIMD.Vector
import CIL.SIMD.VectorLemmas
import CIL.SIMD.X86Base
-- Checked interpreter: memory safety, contracts, composition and linking
import CIL.Safety.AccessAlignment
import CIL.Safety.AccessBelow
import CIL.Safety.AccessRequirements
import CIL.Safety.AccessSlices
import CIL.Safety.AllocationExtension
import CIL.Safety.ArgumentEquivalence
import CIL.Safety.ArgumentHomeValues
import CIL.Safety.AggregateHomeValues
import CIL.Safety.AggregateLocals
import CIL.Safety.ValueBitCasts
import CIL.Safety.ByteEncoding
import CIL.Safety.ByteRoundTrip
import CIL.Safety.BufferContents
import CIL.Safety.CallComposition
import CIL.Safety.Embedding.DeadLocals
import CIL.Safety.Embedding.Outcomes
import CIL.Safety.Embedding.Simulation
import CIL.Safety.Embedding.Suffix
import CIL.Safety.Embedding.Step
import CIL.Safety.Calling
import CIL.Safety.CallingTransport
import CIL.Safety.Certificate
import CIL.Safety.CertifiedContract
import CIL.Safety.CodeAt
import CIL.Safety.ConfinedSnapshots
import CIL.Safety.ConstructComposition
import CIL.Safety.ConstructContract
import CIL.Safety.ConstructSetup
import CIL.Safety.Equations
import CIL.Safety.Execution
import CIL.Safety.ExecutionTrace
import CIL.Safety.ExecutionAllocations
import CIL.Safety.ExecutionFrameOwnership
import CIL.Safety.ExecutionInvariants
import CIL.Safety.ExecutionLemmas
import CIL.Safety.ExecutionLifetime
import CIL.Safety.ExecutionPrefixes
import CIL.Safety.ExecutionStaticWorld
import CIL.Safety.Forwarders
import CIL.Safety.FrameAllocations
import CIL.Safety.FrameLemmas
import CIL.Safety.FrameMemoryBelow
import CIL.Safety.FrameOwnership
import CIL.Safety.FrameProgress
import CIL.Safety.FrameSetupLemmas
import CIL.Safety.FrameStaticWorld
import CIL.Safety.Frames
import CIL.Safety.FuelLemmas
import CIL.Safety.HomeProgress
import CIL.Safety.ImmutableMemory
import CIL.Safety.InstructionMemory
import CIL.Safety.InstructionMemoryLemmas
import CIL.Safety.InstructionReferences
import CIL.Safety.LiveState
import CIL.Safety.LiveValues
import CIL.Safety.LocalReferences
import CIL.Safety.Memory
import CIL.Safety.MemoryBelow
import CIL.Safety.MemoryLemmas
import CIL.Safety.MethodContract
import CIL.Safety.OutcomeContract
import CIL.Safety.RuntimeExceptions
import CIL.Safety.Imports
import CIL.Safety.Linking
import CIL.Safety.StepFlow
import CIL.Safety.RegionRun
import CIL.Safety.NegationReturn
import CIL.Safety.LocalSnapshots
import CIL.Safety.NumericHomes
import CIL.Safety.NumericLocalLoad
import CIL.Safety.NumericLocalStore
import CIL.Safety.NumericLocals
import CIL.Safety.ProfileCertificate
import CIL.Safety.ProfileContract
import CIL.Safety.ProfileEquivalence
import CIL.Safety.ReadCoverage
import CIL.Safety.Relocation
import CIL.Safety.RelocationAddress
import CIL.Safety.RelocationExecution
import CIL.Safety.ReturnArity
import CIL.Safety.ReturnMemory
import CIL.Safety.ReturnReferences
import CIL.Safety.RunReturnTrace
import CIL.Safety.RunningPrefixes
import CIL.Safety.ScalarBranch
import CIL.Safety.StaticInitialization
import CIL.Safety.StaticInstructionWorld
import CIL.Safety.StaticLifetime
import CIL.Safety.StaticMemory
import CIL.Safety.StaticMemoryBelow
import CIL.Safety.StaticMemoryLemmas
import CIL.Safety.StaticReferences
import CIL.Safety.StaticWorld
import CIL.Safety.StepAttribute
import CIL.Safety.StepComposition
import CIL.Safety.ValueSteps
import CIL.Safety.MemorySteps
import CIL.Safety.StepLiveState
import CIL.Safety.StepLocalReferences
import CIL.Safety.StepValues
import CIL.Safety.UnknownHomes
import CIL.Safety.WordFootprint
import CIL.Safety.WordFrameSetup
import CIL.Safety.WordHomes
import CIL.Safety.WordLocals
import CIL.Safety.WordMemory
import CIL.Safety.WordPrefix
import CIL.Safety.WordRoots
import CIL.Safety.WordSnapshotPreservation
import CIL.Safety.WordSnapshots
import CIL.Safety.WriteEffects
import CIL.Safety.TypedCopy
-- Mixed: symbolic execution, verification, extraction checks, interfaces, later results
import CIL.Semantics
import CIL.StepEquations
import CIL.SymbolicExecution
import CIL.Safety.SymbolicExecution
import CIL.Safety.LoopAutomation
import CIL.Safety.LoopContract
import CIL.Safety.LoopOutcome
import CIL.Types
import CIL.VectorMemory
import CIL.VectorMemoryLemmas
import CIL.Verification
import CIL.WideMultiply
import CIL.Safety.WideMultiply
import CIL.Safety.TupleDivision
import CIL.Extraction.LayoutProjection
import CIL.Extraction.Translation
import CIL.Safety.MemoryEquivalence
import CIL.Safety.FrameEquivalence
import CIL.Safety.ExecutionEquivalence
import CIL.Interface.Closure
import CIL.Safety.StaticLinking
import CIL.Interface.FullTransfer
import CIL.SIMD.UnspecifiedLanes

/-!
# LeanCIL

The root of the `CIL` library; importing `CIL` brings in every module listed above.

* `CIL.Types`, `CIL.Instructions`, `CIL.Layout` and `CIL.Memory`: values, opcodes, aggregate
  layouts and byte memory.
* `CIL.Semantics`: the reference interpreter (`CIL.step`, `CIL.run`, `CIL.invoke`), which
  `CIL.SymbolicExecution` steps by rewriting.
* `CIL.Features`, `CIL.SIMD.*` and `CIL.ProfileEquivalence`: hardware feature profiles, the
  intrinsic semantics, and when a result does not depend on the profile.
* `CIL.Safety.*`: the checked interpreter (`CIL.Safety.invoke`) over allocation-aware memory,
  with its invariants and certificates, method contracts, linking, and the stepping tactics
  of `CIL.Safety.SymbolicExecution`. State memory-safety claims against this interpreter.
* `CIL.Verification`: total-correctness specifications over the checked interpreter.
* `CIL.Embedding.*`, `CIL.Extraction.*`, `CIL.Imports`, `CIL.Interface.*` and the method
  identity and binding modules: what ties a proof to an extracted assembly, namely body
  embeddings, translation and layout checks, import slots and published contract interfaces.

`docs/PROOFS.md` explains how to write proofs and `docs/SOUNDNESS.md` what is trusted.
-/
