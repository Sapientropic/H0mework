import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.SourceNativeUniversalRootGrammar
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Lifecycle.Producer.SourceGeneratedProofCarryingPaidExitLifecycleMaximum

/-!
# M14 installed universal Society root grammar

The existing post-settlement source owns one sixteen-point classified trace.
Actual play and the full-capture search are restrictions of that same trace.
The actual continuation point is the source read consumed by the paid-exit
lifecycle maximum; the search point cannot write the actual ledger or choose
another next current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedUniversalSocietyRootGrammar

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementConsumer
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedPostSettlementSocietyFaceTrace
open M14EssentialAccessSectorRegression
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum

abbrev UniversalSocietyRootAt (oldVisit : OldVisit) (sourceIndex : Nat) :=
  ContributionCapacityPostSettlementRenewalRootAt oldVisit sourceIndex

def universalSocietyRootProjectionOfBearingFace :
    PostSettlementSocietyBearingFace →
      ContributionCapacityPostSettlementRenewalProjection
  | .ledger => .ledger
  | .renewal => .renewal
  | .birthBearerExit => .birthBearerExit
  | .bearerExerciseResponse => .bearerExerciseResponse
  | .bearerLeaveExecution => .bearerLeaveExecution
  | .bearerRoleIndependentContinuation => .bearerRoleIndependentContinuation
  | .essentialAccessTenure => .essentialAccessChannel tenureAuthority
  | .essentialAccessHealth => .essentialAccessChannel healthAuthority

/-- Every installed post-root projection is either the sole trace container
or one of the eight bearing normal forms.  Proof-bearing channel variants
collapse by proof irrelevance, not by a second registry. -/
theorem everyUniversalSocietyRootProjection_isGrammarOrBearing
    (projection : ContributionCapacityPostSettlementRenewalProjection) :
    projection = .installedSocietyGrammar ∨
      ∃ face : PostSettlementSocietyBearingFace,
        projection = universalSocietyRootProjectionOfBearingFace face := by
  cases projection with
  | ledger => exact Or.inr ⟨.ledger, rfl⟩
  | renewal => exact Or.inr ⟨.renewal, rfl⟩
  | birthBearerExit => exact Or.inr ⟨.birthBearerExit, rfl⟩
  | bearerExerciseResponse =>
      exact Or.inr ⟨.bearerExerciseResponse, rfl⟩
  | bearerLeaveExecution =>
      exact Or.inr ⟨.bearerLeaveExecution, rfl⟩
  | bearerRoleIndependentContinuation =>
      exact Or.inr ⟨.bearerRoleIndependentContinuation, rfl⟩
  | essentialAccessChannel channel =>
      cases channel with
      | tenure interest =>
          right
          refine ⟨.essentialAccessTenure, ?_⟩
          congr
      | health interest =>
          right
          refine ⟨.essentialAccessHealth, ?_⟩
          congr
  | installedSocietyGrammar => exact Or.inl rfl

/-- The lifecycle continuation successor occurrence (`index + 2`). -/
def universalSocietyVisitAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeTemporalVisitAt
      (UniversalSocietyRootAt oldVisit sourceIndex
        ).toAuthoritativeRoot.toLedgerRoot :=
  contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
    (index + 1 + 1)

/-- Recognition is fixed by the component installed before this root's
emitter.  No law, trace, branch or outcome is supplied at theorem time. -/
def universalSocietyRecognitionAt
    (oldVisit : OldVisit) (sourceIndex : Nat) :
    SourceNativeDependentFaceFamilyRecognitionAt
      (UniversalSocietyRootAt oldVisit sourceIndex) where
  law := postSettlementSocietyFamilyLaw oldVisit sourceIndex
  installation :=
    contributionCapacityPostSettlementSocietyGrammarInstallation oldVisit
      sourceIndex

/-- The installed trace itself fixes `actual` as the sole actual-authority
scenario.  This is read from the source-owned payload, not chosen by the
compiler caller. -/
theorem universalSocietyInstalledActualScenario_eq
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (universalSocietyRecognitionAt oldVisit sourceIndex
      ).installedActualScenarioAt
        (universalSocietyVisitAt oldVisit sourceIndex index) =
      PostSettlementSocietyScenario.actual :=
  (universalSocietyRecognitionAt oldVisit sourceIndex
    ).installedActualScenario_eq
      (universalSocietyVisitAt oldVisit sourceIndex index)

/-- Reusing this exact installed occurrence while relabelling search as the
actual-write owner is impossible. -/
theorem universalSocietyInstalledActualScenarioRelabel_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      ((universalSocietyRecognitionAt oldVisit sourceIndex
        ).ExactInstalledActualScenarioRelabelAt
          (universalSocietyVisitAt oldVisit sourceIndex index)) :=
  (universalSocietyRecognitionAt oldVisit sourceIndex
    ).installedActualScenarioRelabel_isEmpty
      (universalSocietyVisitAt oldVisit sourceIndex index)

def universalSocietyActualGrammarAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  sourceGeneratedUniversalRootGrammarAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index)
    PostSettlementSocietyScenario.actual

def universalSocietyFullCaptureSearchGrammarAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  sourceGeneratedUniversalRootGrammarAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index)
    PostSettlementSocietyScenario.fullCaptureSearch

def universalSocietyActualCompiledAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  compileUniversalSocietyRootGrammarAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index)
    PostSettlementSocietyScenario.actual

def universalSocietyFullCaptureSearchCompiledAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  compileUniversalSocietyRootGrammarAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index)
    PostSettlementSocietyScenario.fullCaptureSearch

def universalSocietyActualPassedAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (face : PostSettlementSocietyBearingFace) :
    SourceGeneratedPassedDependentFaceAuditAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) .actual where
  point := postSettlementSocietyPointAt oldVisit sourceIndex
    ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
      (universalSocietyVisitAt oldVisit sourceIndex index).current)
    .actual face
  scenarioExact := rfl
  passed := postSettlementSocietyFaceReadAt oldVisit sourceIndex
    ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
      (universalSocietyVisitAt oldVisit sourceIndex index).current) face

def universalSocietyExpectedActualPassedAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    List (SourceGeneratedPassedDependentFaceAuditAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) .actual) :=
  [.ledger, .renewal, .birthBearerExit, .bearerExerciseResponse,
    .bearerLeaveExecution, .bearerRoleIndependentContinuation,
    .essentialAccessTenure, .essentialAccessHealth].map
      (universalSocietyActualPassedAuditAt oldVisit sourceIndex index)

def universalSocietyFullCaptureSearchFailureAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedFailedDependentFaceAuditAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index)
      .fullCaptureSearch where
  point := postSettlementSocietyPointAt oldVisit sourceIndex
    ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
      (universalSocietyVisitAt oldVisit sourceIndex index).current)
    .fullCaptureSearch .bearerRoleIndependentContinuation
  scenarioExact := rfl
  failed := postSettlementFullCaptureFailedAt oldVisit sourceIndex
    ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
      (universalSocietyVisitAt oldVisit sourceIndex index).current)

theorem universalSocietyActualCompiler_isCanonical
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    universalSocietyActualCompiledAt oldVisit sourceIndex index =
      SourceNativeUniversalRootGrammarDispositionAt.canonical
        (universalSocietyExpectedActualPassedAt oldVisit sourceIndex index) := by
  rfl

theorem universalSocietyFullCaptureSearchCompiler_isFailed
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    universalSocietyFullCaptureSearchCompiledAt oldVisit sourceIndex index =
      SourceNativeUniversalRootGrammarDispositionAt.failed
        (universalSocietyFullCaptureSearchFailureAuditAt oldVisit sourceIndex
          index) := by
  rfl

theorem fullCaptureSearch_ne_actual :
    PostSettlementSocietyScenario.fullCaptureSearch ≠
      PostSettlementSocietyScenario.actual := by
  decide

theorem universalSocietyScenarioCompilers_shareOneTrace
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    universalSocietyActualCompiledAt oldVisit sourceIndex index =
        ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
          (universalSocietyVisitAt oldVisit sourceIndex index)).fold
            (sourceNativeUniversalRootGrammarAlgebraAt
              (universalSocietyRecognitionAt oldVisit sourceIndex)
              (universalSocietyVisitAt oldVisit sourceIndex index)
              .actual) ∧
      universalSocietyFullCaptureSearchCompiledAt oldVisit sourceIndex index =
        ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
          (universalSocietyVisitAt oldVisit sourceIndex index)).fold
            (sourceNativeUniversalRootGrammarAlgebraAt
              (universalSocietyRecognitionAt oldVisit sourceIndex)
              (universalSocietyVisitAt oldVisit sourceIndex index)
              .fullCaptureSearch) :=
  scenarioCompilers_shareInstalledTrace
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index) .actual
      .fullCaptureSearch

def universalSocietyActualContinuationPointAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :=
  postSettlementSocietyPointAt oldVisit sourceIndex
    ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
      (universalSocietyVisitAt oldVisit sourceIndex index).current)
    .actual .bearerRoleIndependentContinuation

def universalSocietyActualContinuationPassedAuditAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedPassedDependentFaceAuditAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) .actual :=
  universalSocietyActualPassedAuditAt oldVisit sourceIndex index
    .bearerRoleIndependentContinuation

theorem universalSocietyActualContinuation_entersCanonicalFold
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    universalSocietyActualCompiledAt oldVisit sourceIndex index =
        SourceNativeUniversalRootGrammarDispositionAt.canonical
          (universalSocietyExpectedActualPassedAt oldVisit sourceIndex index) ∧
      universalSocietyActualContinuationPassedAuditAt oldVisit sourceIndex
          index ∈
        universalSocietyExpectedActualPassedAt oldVisit sourceIndex index := by
  exact
    ⟨universalSocietyActualCompiler_isCanonical oldVisit sourceIndex index,
      by
        simp [universalSocietyActualContinuationPassedAuditAt,
          universalSocietyExpectedActualPassedAt]⟩

theorem universalSocietyActualContinuationRead_eq_lifecycle
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    postSettlementSocietyFaceReadAt oldVisit sourceIndex
        ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
          (universalSocietyVisitAt oldVisit sourceIndex index).current)
        .bearerRoleIndependentContinuation =
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorContinuationRootRead :=
  rfl

/-- The lifecycle maximum is consumed through the exact passed continuation
member of the actual fold.  This dependent carrier forbids a parallel
lifecycle sidecar detached from the installed trace. -/
structure SourceGeneratedPaidExitLifecycleFromActualContinuationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (passed : SourceGeneratedPassedDependentFaceAuditAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) .actual) : Type 32 where
  private mk ::
  passedInCanonicalFold : passed ∈
    universalSocietyExpectedActualPassedAt oldVisit sourceIndex index
  lifecycleMaximum : ProofCarryingPaidExitLifecycleMaximumAt oldVisit
    sourceIndex index
  continuationReadExact : HEq passed.passed
    lifecycleMaximum.continuation.successorContinuationRootRead

def sourceGeneratedPaidExitLifecycleFromActualContinuationAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedPaidExitLifecycleFromActualContinuationAt oldVisit
      sourceIndex index
      (universalSocietyActualContinuationPassedAuditAt oldVisit sourceIndex
        index) := by
  let lifecycle :=
    sourceGeneratedProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
      index
  exact
    { passedInCanonicalFold :=
        (universalSocietyActualContinuation_entersCanonicalFold oldVisit
          sourceIndex index).2
      lifecycleMaximum := lifecycle
      continuationReadExact := by
        change HEq
          (postSettlementSocietyFaceReadAt oldVisit sourceIndex
            ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
              (universalSocietyVisitAt oldVisit sourceIndex index).current)
            .bearerRoleIndependentContinuation)
          lifecycle.continuation.successorContinuationRootRead
        exact heq_of_eq
          (universalSocietyActualContinuationRead_eq_lifecycle oldVisit
            sourceIndex index) }

def universalSocietyExpectedGeneratedNextAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceNativeAuthoritativeRootCurrentAt (JointSettlementNAt oldVisit) :=
  ⟨PostSettlementRenewalVAt oldVisit,
    (UniversalSocietyRootAt oldVisit sourceIndex).toAuthoritativeRoot,
    contributionCapacityPostSettlementRenewalVisitAt oldVisit sourceIndex
      (index + 1 + 1 + 1)⟩

theorem universalSocietyGeneratedNext_exact
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    (universalSocietyActualGrammarAt oldVisit sourceIndex index).generatedNext =
      universalSocietyExpectedGeneratedNextAt oldVisit sourceIndex index :=
  rfl

structure SourceGeneratedUniversalSocietyRootGrammarAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 32 where
  private mk ::
  actualGrammar : SourceGeneratedUniversalRootGrammarAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index) .actual
  searchGrammar : SourceGeneratedUniversalRootGrammarAt
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index) .fullCaptureSearch
  actualCanonical :
    universalSocietyActualCompiledAt oldVisit sourceIndex index =
      SourceNativeUniversalRootGrammarDispositionAt.canonical
        (universalSocietyExpectedActualPassedAt oldVisit sourceIndex index)
  searchFailed :
    universalSocietyFullCaptureSearchCompiledAt oldVisit sourceIndex index =
      SourceNativeUniversalRootGrammarDispositionAt.failed
        (universalSocietyFullCaptureSearchFailureAuditAt oldVisit sourceIndex
          index)
  continuationEntersActualFold :
    universalSocietyActualCompiledAt oldVisit sourceIndex index =
        SourceNativeUniversalRootGrammarDispositionAt.canonical
          (universalSocietyExpectedActualPassedAt oldVisit sourceIndex index) ∧
      universalSocietyActualContinuationPassedAuditAt oldVisit sourceIndex
          index ∈
        universalSocietyExpectedActualPassedAt oldVisit sourceIndex index
  lifecycleFromActualContinuation :
    SourceGeneratedPaidExitLifecycleFromActualContinuationAt oldVisit
      sourceIndex index
      (universalSocietyActualContinuationPassedAuditAt oldVisit sourceIndex
        index)
  traceNodup :
    ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
      (universalSocietyVisitAt oldVisit sourceIndex index)).trace.Nodup
  actualNoDormant : ∀ face : PostSettlementSocietyBearingFace,
    ∃! point :
        (universalSocietyRecognitionAt oldVisit sourceIndex).PointAt
          (universalSocietyVisitAt oldVisit sourceIndex index),
      point ∈ ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
          (universalSocietyVisitAt oldVisit sourceIndex index)).trace ∧
        point.scenario = .actual ∧ point.face = face
  searchNoDormant : ∀ face : PostSettlementSocietyBearingFace,
    ∃! point :
        (universalSocietyRecognitionAt oldVisit sourceIndex).PointAt
          (universalSocietyVisitAt oldVisit sourceIndex index),
      point ∈ ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
          (universalSocietyVisitAt oldVisit sourceIndex index)).trace ∧
        point.scenario = .fullCaptureSearch ∧ point.face = face
  everyRootProjectionCovered : ∀ projection :
      ContributionCapacityPostSettlementRenewalProjection,
    projection = .installedSocietyGrammar ∨
      ∃ face : PostSettlementSocietyBearingFace,
        projection = universalSocietyRootProjectionOfBearingFace face
  searchHasNoActualWrite : IsEmpty
    (SourceNativeScenarioActualWriteAuthorityAt
      (postSettlementSocietyVocabulary oldVisit sourceIndex)
      .fullCaptureSearch)
  rootLedgerAndNext :
    let evolution := (UniversalSocietyRootAt oldVisit sourceIndex
      ).canonicalCausalAnswerAndNext
        (ULift.up (universalSocietyVisitAt oldVisit sourceIndex index))
    evolution.generated =
        (UniversalSocietyRootAt oldVisit sourceIndex
          ).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
            (universalSocietyVisitAt oldVisit sourceIndex index) ∧
      HEq (evolution.generated.projectionOutcome
          (universalSocietyRecognitionAt oldVisit sourceIndex).rootProjection)
        ((universalSocietyRecognitionAt oldVisit sourceIndex).installedFiberAt
          (universalSocietyVisitAt oldVisit sourceIndex index)) ∧
      HEq actualGrammar.wholeLedgerWriteBack
        ((UniversalSocietyRootAt oldVisit sourceIndex
          ).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
            (universalSocietyVisitAt oldVisit sourceIndex index).current) ∧
      evolution.nextCurrent = actualGrammar.generatedNext
  generatedNextExact : actualGrammar.generatedNext =
    universalSocietyExpectedGeneratedNextAt oldVisit sourceIndex index

def sourceGeneratedUniversalSocietyRootGrammarAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    SourceGeneratedUniversalSocietyRootGrammarAt oldVisit sourceIndex index := by
  let actual := universalSocietyActualGrammarAt oldVisit sourceIndex index
  let search :=
    universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
  let lifecycleFromActualContinuation :=
    sourceGeneratedPaidExitLifecycleFromActualContinuationAt oldVisit
      sourceIndex index
  exact
    { actualGrammar := actual
      searchGrammar := search
      actualCanonical :=
        universalSocietyActualCompiler_isCanonical oldVisit sourceIndex index
      searchFailed :=
        universalSocietyFullCaptureSearchCompiler_isFailed oldVisit sourceIndex
          index
      continuationEntersActualFold :=
        universalSocietyActualContinuation_entersCanonicalFold oldVisit
          sourceIndex index
      lifecycleFromActualContinuation := lifecycleFromActualContinuation
      traceNodup := postSettlementSocietyTrace_nodup oldVisit sourceIndex
        ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
          (universalSocietyVisitAt oldVisit sourceIndex index).current)
      actualNoDormant := fun face =>
        (universalSocietyRecognitionAt oldVisit sourceIndex
          ).scenario_face_exactlyOnce
            (universalSocietyVisitAt oldVisit sourceIndex index) .actual face
      searchNoDormant := fun face =>
        (universalSocietyRecognitionAt oldVisit sourceIndex
          ).scenario_face_exactlyOnce
            (universalSocietyVisitAt oldVisit sourceIndex index)
              .fullCaptureSearch face
      everyRootProjectionCovered :=
        everyUniversalSocietyRootProjection_isGrammarOrBearing
      searchHasNoActualWrite :=
        searchScenario_actualWriteAuthority_isEmpty
          (postSettlementSocietyVocabulary oldVisit sourceIndex)
          .fullCaptureSearch fullCaptureSearch_ne_actual
      rootLedgerAndNext := actual.rootLedgerAndNext_factorize
      generatedNextExact :=
        universalSocietyGeneratedNext_exact oldVisit sourceIndex index }

theorem sourceGeneratedUniversalSocietyRootGrammar_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let grammar :=
    sourceGeneratedUniversalSocietyRootGrammarAt oldVisit sourceIndex index
  fail_if_success exact grammar.branch
  fail_if_success exact grammar.trace
  fail_if_success exact grammar.payment
  fail_if_success exact grammar.consumer
  fail_if_success exact grammar.registry
  fail_if_success exact grammar.future
  trivial

end
end M14SourceGeneratedUniversalSocietyRootGrammar
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedUniversalSocietyRootGrammar.sourceGeneratedUniversalSocietyRootGrammarAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedUniversalSocietyRootGrammar.universalSocietyActualContinuation_entersCanonicalFold
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedUniversalSocietyRootGrammar.universalSocietyGeneratedNext_exact
