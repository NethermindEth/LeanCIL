import CIL.Extraction.DecodedMethod

/-!
Raw decoding that keeps the stage refusing a method. `Tests.decodeRaw` runs instantiation,
argument storage and `Method.ofClosed?` as `Method.ofRaw?` does, so a refusal test can state
the pc and opcode of a live hole and tell it apart from a refusal before closed decoding.
`Tests.DecodedFlow` pairs the scalar check with the code equation, which refuses a forged
emission at a site where the scalar check leaves the comparison to the decoder.
-/

namespace Tests

open CIL CIL.Extraction

/-- The stage that refuses a raw method: instantiation at its type arguments, the storage of
    its closed arguments and locals, or closed decoding with the decoder's own error. -/
inductive RawDecodeError where
  | instantiation
  | arguments
  | method (error : MethodDecodeError)
  deriving DecidableEq, Repr

/-- A decoding result with a decidable value is compared by its refusal or its value. -/
instance {α : Type} [DecidableEq α] : DecidableEq (Except RawDecodeError α)
  | .ok left, .ok right => decidable_of_iff (left = right) ⟨congrArg _, Except.ok.inj⟩
  | .error left, .error right =>
    decidable_of_iff (left = right) ⟨congrArg _, Except.error.inj⟩
  | .ok _, .error _ | .error _, .ok _ => isFalse (by intro equal; cases equal)

/-- The method `Method.ofRaw?` builds from a raw definition, or the stage that refuses it. -/
def decodeRaw (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (reachable : List Bool) (source : RawMethod)
    (arguments : List TypeExpr) : Except RawDecodeError Method :=
  match instantiateMethod environment.rawLayouts source arguments with
  | none => .error .instantiation
  | some closed =>
    match closedArguments environment.rawLayouts closed with
    | none => .error .arguments
    | some storage =>
      (Method.ofClosed? profile environment links reachable closed storage).mapError .method

/-- The scalar check together with the code equation extraction proves for every method: `code`
    is what the decoder gives `raw` at the pcs `features` reaches, with no layouts or links. -/
abbrev DecodedFlow (raw : RawMethod) (features : FeatureCertificate)
    (certificate : ScalarCertificate) (code : List Instruction) : Prop :=
  ScalarFlowValid raw features certificate code ∧
    code = methodCode .scalar {} [] (features.map Option.isSome) raw

/-- The refusal of closed decoding at the first live hole, at `pc` with raw `opcode`. -/
abbrev liveHoleAt {α : Type} (pc opcode : Nat) : Except RawDecodeError α :=
  .error (.method (.liveHole pc opcode))

/-- Forgetting the refusing stage gives exactly the raw decoder's result. -/
theorem decodeRaw_toOption (profile : FeatureProfile) (environment : LayoutEnvironment)
    (links : List (Nat × Link)) (reachable : List Bool) (source : RawMethod)
    (arguments : List TypeExpr) :
    (decodeRaw profile environment links reachable source arguments).toOption =
      Method.ofRaw? profile environment links reachable source arguments := by
  unfold decodeRaw Method.ofRaw?
  cases instantiateMethod environment.rawLayouts source arguments with
  | none => rfl
  | some closed =>
    cases stored : closedArguments environment.rawLayouts closed with
    | none => simp only [stored, bind, Option.bind]; rfl
    | some storage =>
      simp only [stored, bind, Option.bind]
      cases Method.ofClosed? profile environment links reachable closed storage <;> rfl

#print axioms decodeRaw_toOption

end Tests
