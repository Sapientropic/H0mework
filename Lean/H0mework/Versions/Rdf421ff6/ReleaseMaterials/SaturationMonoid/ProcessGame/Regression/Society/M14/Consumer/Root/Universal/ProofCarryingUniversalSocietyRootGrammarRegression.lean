import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Universal.NoGo.SourceGeneratedUniversalSocietyRootGrammarFailure
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.ProofCarryingEconomicSingleFoldRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Necessity.Lifecycle.ProofCarryingPaidExitLifecycleMaximumRegression

/-!
# Direct consumer of the installed universal Society root grammar

This sink consumes the generic one-trace fold theorem, the M14 actual and
full-capture restrictions, the real external-liability failure, the existing
economic lineage fold, and the paid-exit lifecycle maximum.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingUniversalSocietyRootGrammarRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementSocietyFaceTrace
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot
open M14SourceGeneratedContributionCapacityPostSettlementExternalLiability
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedUniversalSocietyRootGrammar
open M14SourceGeneratedUniversalSocietyRootGrammarFailure
open M14ProofCarryingEconomicSingleFoldRegression
open M14EconomicSingleFold
open M14ProofCarryingPaidExitLifecycleMaximumRegression

theorem universalSocietyInstalledAudit_eq_trace
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    sourceGeneratedDependentFaceAudit
        ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
          (universalSocietyVisitAt oldVisit sourceIndex index)) =
      ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
        (universalSocietyVisitAt oldVisit sourceIndex index)).trace :=
  sourceGeneratedDependentFaceAudit_eq_trace _

theorem universalSocietyActualCompiler_unique
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (candidate : RootedAccountedUnfolding
        ((universalSocietyRecognitionAt oldVisit sourceIndex).PointAt
          (universalSocietyVisitAt oldVisit sourceIndex index)) →
      SourceNativeUniversalRootGrammarDispositionAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)
        (universalSocietyVisitAt oldVisit sourceIndex index) .actual)
    (commutes : ∀ point branches,
      candidate (RootedAccountedUnfolding.occur point branches) =
        sourceNativeUniversalRootGrammarAlgebraAt
          (universalSocietyRecognitionAt oldVisit sourceIndex)
          (universalSocietyVisitAt oldVisit sourceIndex index) .actual point
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
        (universalSocietyVisitAt oldVisit sourceIndex index)) =
      universalSocietyActualCompiledAt oldVisit sourceIndex index :=
  compileUniversalSocietyRootGrammarAt_unique
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index) .actual candidate
      commutes

theorem universalSocietySearchCompiler_unique
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (candidate : RootedAccountedUnfolding
        ((universalSocietyRecognitionAt oldVisit sourceIndex).PointAt
          (universalSocietyVisitAt oldVisit sourceIndex index)) →
      SourceNativeUniversalRootGrammarDispositionAt
        (universalSocietyRecognitionAt oldVisit sourceIndex)
        (universalSocietyVisitAt oldVisit sourceIndex index)
          .fullCaptureSearch)
    (commutes : ∀ point branches,
      candidate (RootedAccountedUnfolding.occur point branches) =
        sourceNativeUniversalRootGrammarAlgebraAt
          (universalSocietyRecognitionAt oldVisit sourceIndex)
          (universalSocietyVisitAt oldVisit sourceIndex index)
            .fullCaptureSearch point
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
        (universalSocietyVisitAt oldVisit sourceIndex index)) =
      universalSocietyFullCaptureSearchCompiledAt oldVisit sourceIndex index :=
  compileUniversalSocietyRootGrammarAt_unique
    (universalSocietyRecognitionAt oldVisit sourceIndex)
    (universalSocietyVisitAt oldVisit sourceIndex index) .fullCaptureSearch
      candidate commutes

/-- Existing economic fold uniqueness is consumed directly, not reproved. -/
theorem economicSingleFold_remainsUnique
    (candidate : RootedAccountedUnfolding ExactEconomicAtom →
      EconomicFoldImage)
    (compatible : EconomicConstructorCompatible candidate)
    (occurrence : RootedAccountedUnfolding ExactEconomicAtom) :
    candidate occurrence = economicImage occurrence :=
  proofCarryingEconomicSingleFoldDirectConsumer
    |>.constructorCompatibleEvaluatorUnique candidate compatible occurrence

structure ProofCarryingUniversalSocietyRootGrammarCertificate : Prop where
  everyPositive : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty
      (SourceGeneratedUniversalSocietyRootGrammarAt oldVisit sourceIndex index)
  everyFailure : ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
    Nonempty
      (SourceGeneratedUniversalSocietyRootGrammarFailureAt oldVisit
        sourceIndex index)
  everyTraceHasSixteenUniquePoints :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
          (universalSocietyVisitAt oldVisit sourceIndex index)).trace.length =
          16 ∧
        ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
          (universalSocietyVisitAt oldVisit sourceIndex index)).trace.Nodup
  everyRootProjectionCovered :
    ∀ projection : ContributionCapacityPostSettlementRenewalProjection,
      projection = .installedSocietyGrammar ∨
        ∃ face : PostSettlementSocietyBearingFace,
          projection = universalSocietyRootProjectionOfBearingFace face
  everyInstalledAuditExact :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      sourceGeneratedDependentFaceAudit
          ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
            (universalSocietyVisitAt oldVisit sourceIndex index)) =
        ((universalSocietyRecognitionAt oldVisit sourceIndex).traceAt
          (universalSocietyVisitAt oldVisit sourceIndex index)).trace
  everyInstalledActualScenarioExact :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      (universalSocietyRecognitionAt oldVisit sourceIndex
        ).installedActualScenarioAt
          (universalSocietyVisitAt oldVisit sourceIndex index) =
        PostSettlementSocietyScenario.actual
  everyInstalledActualScenarioRelabelImpossible :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      IsEmpty
        ((universalSocietyRecognitionAt oldVisit sourceIndex
          ).ExactInstalledActualScenarioRelabelAt
            (universalSocietyVisitAt oldVisit sourceIndex index))
  everyActualBranchExact :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      universalSocietyActualCompiledAt oldVisit sourceIndex index =
        SourceNativeUniversalRootGrammarDispositionAt.canonical
          (universalSocietyExpectedActualPassedAt oldVisit sourceIndex index)
  everySearchBranchExact :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      universalSocietyFullCaptureSearchCompiledAt oldVisit sourceIndex index =
        SourceNativeUniversalRootGrammarDispositionAt.failed
          (universalSocietyFullCaptureSearchFailureAuditAt oldVisit
            sourceIndex index)
  everySearchContinuationPassEmpty :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      IsEmpty ((postSettlementSocietyVocabulary oldVisit sourceIndex).PassedAt
        ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
          (universalSocietyVisitAt oldVisit sourceIndex index).current)
        .fullCaptureSearch .bearerRoleIndependentContinuation)
  everyContinuationGeneratedByActualFold :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      universalSocietyActualContinuationPassedAuditAt oldVisit sourceIndex
          index ∈
        universalSocietyExpectedActualPassedAt oldVisit sourceIndex index
  everyContinuationReadFeedsLifecycle :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      postSettlementSocietyFaceReadAt oldVisit sourceIndex
          ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
            (universalSocietyVisitAt oldVisit sourceIndex index).current)
          .bearerRoleIndependentContinuation =
        (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).successorContinuationRootRead
  everyLifecycleGeneratedFromActualContinuation :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      Nonempty
        (SourceGeneratedPaidExitLifecycleFromActualContinuationAt oldVisit
          sourceIndex index
          (universalSocietyActualContinuationPassedAuditAt oldVisit
            sourceIndex index))
  everySearchFailureHasExternalLiability :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      Nonempty (PostSettlementGeneratedExternalLiabilityAt oldVisit
        sourceIndex (index + 1 + 1)
        (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex index
          ).exactEvent
        (universalSocietySearchActualExitAt oldVisit sourceIndex index))
  everySearchHasNoActualWrite :
    ∀ oldVisit : OldVisit, ∀ sourceIndex _index : Nat,
      IsEmpty (SourceNativeScenarioActualWriteAuthorityAt
        (postSettlementSocietyVocabulary oldVisit sourceIndex)
        .fullCaptureSearch)
  everySearchAuditPreservesActualWriteBack :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      let failure := sourceGeneratedUniversalSocietyRootGrammarFailureAt
        oldVisit sourceIndex index
      failure.auditDisposition.applyToActualWriteBack
          ((universalSocietyActualGrammarAt oldVisit sourceIndex index
            ).wholeLedgerWriteBack) =
        (universalSocietyActualGrammarAt oldVisit sourceIndex index
          ).wholeLedgerWriteBack
  everyActualSearchSameRootLedgerAndNext :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      (universalSocietyActualGrammarAt oldVisit sourceIndex index).exactEvent =
          (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex
            index).exactEvent ∧
        (universalSocietyActualGrammarAt oldVisit sourceIndex index
            ).wholeLedgerWriteBack =
          (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex
            index).wholeLedgerWriteBack ∧
        (universalSocietyActualGrammarAt oldVisit sourceIndex index
            ).generatedNext =
          (universalSocietyFullCaptureSearchGrammarAt oldVisit sourceIndex
            index).generatedNext
  everyGeneratedNextExact :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      (universalSocietyActualGrammarAt oldVisit sourceIndex index
        ).generatedNext =
        universalSocietyExpectedGeneratedNextAt oldVisit sourceIndex index
  everyFailedAxisNondeletable :
    ∀ oldVisit : OldVisit, ∀ sourceIndex index : Nat,
      let failure := sourceGeneratedUniversalSocietyRootGrammarFailureAt
        oldVisit sourceIndex index
      (¬ ExactFailedFaceResidualBearerDeletionAt failure.failureAudit.failed) ∧
        (¬ ExactFailedFaceSourceOwnershipDeletionAt
          failure.failureAudit.failed) ∧
        (¬ ExactFailedFaceConsumerDeletionAt failure.failureAudit.failed) ∧
        (¬ ExactFailedFaceDispositionDeletionAt failure.failureAudit.failed)
  economicSingleFold : ProofCarryingEconomicSingleFoldCertificate
  lifecycleMaximum : ProofCarryingPaidExitLifecycleMaximumCertificate

theorem proofCarryingUniversalSocietyRootGrammarDirectConsumer :
    ProofCarryingUniversalSocietyRootGrammarCertificate where
  everyPositive := fun oldVisit sourceIndex index =>
    ⟨sourceGeneratedUniversalSocietyRootGrammarAt oldVisit sourceIndex index⟩
  everyFailure := fun oldVisit sourceIndex index =>
    ⟨sourceGeneratedUniversalSocietyRootGrammarFailureAt oldVisit
      sourceIndex index⟩
  everyTraceHasSixteenUniquePoints := fun oldVisit sourceIndex index =>
    ⟨postSettlementSocietyTrace_length oldVisit sourceIndex
        ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
          (universalSocietyVisitAt oldVisit sourceIndex index).current),
      postSettlementSocietyTrace_nodup oldVisit sourceIndex
        ((UniversalSocietyRootAt oldVisit sourceIndex).emitted
          (universalSocietyVisitAt oldVisit sourceIndex index).current)⟩
  everyRootProjectionCovered :=
    everyUniversalSocietyRootProjection_isGrammarOrBearing
  everyInstalledAuditExact := universalSocietyInstalledAudit_eq_trace
  everyInstalledActualScenarioExact :=
    universalSocietyInstalledActualScenario_eq
  everyInstalledActualScenarioRelabelImpossible :=
    universalSocietyInstalledActualScenarioRelabel_isEmpty
  everyActualBranchExact := universalSocietyActualCompiler_isCanonical
  everySearchBranchExact :=
    universalSocietyFullCaptureSearchCompiler_isFailed
  everySearchContinuationPassEmpty := fun oldVisit sourceIndex index =>
    (sourceGeneratedUniversalSocietyRootGrammarFailureAt oldVisit sourceIndex
      index).failedPointCannotPass
  everyContinuationGeneratedByActualFold := fun oldVisit sourceIndex index =>
    (universalSocietyActualContinuation_entersCanonicalFold oldVisit
      sourceIndex index).2
  everyContinuationReadFeedsLifecycle :=
    universalSocietyActualContinuationRead_eq_lifecycle
  everyLifecycleGeneratedFromActualContinuation :=
    fun oldVisit sourceIndex index =>
      ⟨sourceGeneratedPaidExitLifecycleFromActualContinuationAt oldVisit
        sourceIndex index⟩
  everySearchFailureHasExternalLiability := fun oldVisit sourceIndex index =>
    ⟨universalSocietySearchExternalLiabilityAt oldVisit sourceIndex index⟩
  everySearchHasNoActualWrite := fun oldVisit sourceIndex index =>
    (sourceGeneratedUniversalSocietyRootGrammarFailureAt oldVisit sourceIndex
      index).searchNoActualWrite
  everySearchAuditPreservesActualWriteBack := fun oldVisit sourceIndex index =>
    (sourceGeneratedUniversalSocietyRootGrammarFailureAt oldVisit sourceIndex
      index).auditPreservesActualWriteBack
  everyActualSearchSameRootLedgerAndNext :=
    universalSocietyActualSearch_sameRootLedgerAndNext
  everyGeneratedNextExact := universalSocietyGeneratedNext_exact
  everyFailedAxisNondeletable := fun oldVisit sourceIndex index => by
    let failure := sourceGeneratedUniversalSocietyRootGrammarFailureAt
      oldVisit sourceIndex index
    exact
      ⟨failure.residualBearerDeletion_isFalse,
        failure.sourceOwnershipDeletion_isFalse,
        failure.consumerDeletion_isFalse,
        failure.dispositionDeletion_isFalse⟩
  economicSingleFold := proofCarryingEconomicSingleFoldDirectConsumer
  lifecycleMaximum := proofCarryingPaidExitLifecycleMaximumDirectConsumer

end
end M14ProofCarryingUniversalSocietyRootGrammarRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingUniversalSocietyRootGrammarRegression.proofCarryingUniversalSocietyRootGrammarDirectConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingUniversalSocietyRootGrammarRegression.universalSocietyActualCompiler_unique
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingUniversalSocietyRootGrammarRegression.economicSingleFold_remainsUnique
