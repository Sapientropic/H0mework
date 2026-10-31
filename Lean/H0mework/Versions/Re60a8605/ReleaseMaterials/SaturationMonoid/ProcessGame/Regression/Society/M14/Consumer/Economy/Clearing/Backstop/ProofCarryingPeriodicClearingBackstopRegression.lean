import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Clearing.Backstop.PeriodicClearingBackstopRenewal
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Clearing.Backstop.ProofCarryingSameRootClearingBackstopCoordinateRegression

/-!
# M14 direct consumer for clearing-backstop renewal at every visit

The fixed same-root coordinate is now consumed together with the depth-only
periodic backstop producer.  At each finite visit, the certificate preserves
both generated-next layers: the local responsibility process fulfills the
existing open `b` slot, while an actual bounded institutional reform writes
the root row and generates the next living-law visit.  These differently
typed nexts are never equated.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPeriodicClearingBackstopRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Renewal Revision
open Election Power Clearing Legislation
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression
open M4AutomaticFullFulfillmentRegression
open M9ProofCarryingRenewalInquiryRoot
open M14ClearingConsumerDeath
open M14SourceGeneratedClearingBackstopActivation
open M14SourceClearingBackstopRenewal
open M14SourceCommonClearingRenewal
open M14UBIPeriodicRootHistory
open M14PeriodicMandatePowerRenewal
open M14PeriodicCommonClearingRenewal
open M14PeriodicClearingBackstopRenewal
open M14ProofCarryingSameRootClearingBackstopCoordinateRegression

/-! ## Direct pointwise readouts -/

theorem periodicBackstopRootUpdateExact (depth : Nat) :
    let backstop :=
      sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
    backstop.rootOccurrence =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt (temporalVisitAt depth)) ∧
      clearingBackstopRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current) =
        (.inl ⟨backstop.installed.active,
            backstop.installed.payload⟩ :
          SourceNativeProjectionFiberAt
            clearingBackstopRecognition.law.toProjectionLaw PUnit.unit
            (jointRoot.emitted (temporalVisitAt depth).current)) ∧
      backstop.appliedReform.residualRow =
        backstop.installed.temporalSelectedRow ∧
      backstop.appliedReform.residualRow.sourceRow.CommutesWithWorld ∧
      Nonempty (RenewalResponsibilityConsumerAt
        backstop.installed.operationalAuthority) ∧
      backstop.appliedReform.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      backstop.installed.RootAnswerAndNextFactorizes ∧
      backstop.commonClearing.installed.RootAnswerAndNextFactorizes ∧
      backstop.commonClearing.pclInstalled.RootAnswerAndNextFactorizes ∧
      backstop.commonClearing.mandate.installed.RootAnswerAndNextFactorizes ∧
      backstop.appliedReform.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      backstop.appliedReform.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface ∧
      backstop.appliedReform.generatedNext.visit =
        temporalVisitAt (depth + 1) :=
  let backstop :=
    sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
  ⟨backstop.rootOccurrenceExact,
    backstop.componentOutcomeExact,
    backstop.selectedWriteExact,
    backstop.selectedWriteCommutes,
    ⟨backstop.rootConsumer⟩,
    backstop.wholeLedgerExact,
    backstop.rootFactorization,
    backstop.commonClearingRootFactorization,
    backstop.pclRootFactorization,
    backstop.mandateRootFactorization,
    backstop.generatedNextExact,
    backstop.lawSurfacePreserved,
    backstop.nextVisitExact⟩

theorem periodicBackstopAllProjectionAndActionAuthorityExact
    (depth : Nat) :
    let backstop :=
      sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
    jointClearingBackstopProjection ≠ jointCommonClearingProjection ∧
      jointClearingBackstopProjection ≠
        jointRouteOutageRestorationProjection ∧
      jointClearingBackstopProjection ≠
        jointEssentialServiceRestorationProjection ∧
      jointClearingBackstopProjection ≠ jointMandateProjection ∧
      jointClearingBackstopProjection ≠
        jointRecognitionWitnessProjection ∧
      jointClearingBackstopProjection ≠ jointUBIProjection ∧
      jointClearingBackstopProjection ≠ jointProofCarryingProjection ∧
      jointClearingBackstopProjection ≠ jointInquiryProjection ∧
      jointClearingBackstopProjection ≠ jointFailureProjection ∧
      backstop.installed.payload.disposition =
        sourceGeneratedClearingBackstopDisposition ∧
      backstop.commonClearing.installed.payload.disposition =
        sourceGeneratedCommonClearingDisposition ∧
      backstop.localActivation.edge = fulfillB :=
  let backstop :=
    sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
  ⟨backstop.projectionDistinct.1,
    backstop.projectionDistinct.2.1,
    backstop.projectionDistinct.2.2.1,
    backstop.projectionDistinct.2.2.2.1,
    backstop.projectionDistinct.2.2.2.2.1,
    backstop.projectionDistinct.2.2.2.2.2.1,
    backstop.projectionDistinct.2.2.2.2.2.2.1,
    backstop.projectionDistinct.2.2.2.2.2.2.2.1,
    backstop.projectionDistinct.2.2.2.2.2.2.2.2,
    backstop.sourceDispositionExact,
    backstop.commonClearing.dispositionExact,
    backstop.localEdgeExact⟩

/-! ## Prop-only certificate -/

structure ProofCarryingPeriodicClearingBackstopCertificateAt
    (depth : Nat) : Prop where
  sameRootCoordinate :
    ProofCarryingSameRootClearingBackstopCoordinateCertificate
  actual : Nonempty
    (SourceGeneratedProofCarryingPeriodicClearingBackstopAt depth)
  exactInstalledIndices :
    let backstop :=
      sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
    backstop.installed = installedClearingBackstopAt depth ∧
      backstop.commonClearing =
        sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth ∧
      backstop.commonClearing.pclInstalled =
        installedProofCarryingRenewalAt depth ∧
      backstop.commonClearing.mandate =
        periodicMandatePowerRenewalAt depth
  exactSourceImage :
    let backstop :=
      sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
    ∃ seed : partialBResidualConsumerCompiler.ExactActivationSeed,
      partialBResidualConsumerCompiler.consumerOfSeed seed =
          backstop.localActivation ∧
      backstop.installed.payload.sourceSeed = seed ∧
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = core.targetFace.state Lifecycle.actualEventGame.source ∧
          partialBResidualConsumerCompiler.activationAdmittedAt seed.1) ∧
      seed.occurrence partialBResidualConsumerCompiler = partialOccurrence ∧
      seed.openSettlement partialBResidualConsumerCompiler = partialOpenB ∧
      seed.activation partialBResidualConsumerCompiler =
        canonicalAClearingFace.counterpartyConsumer.event
  exactLocalActionAndNext :
    let backstop :=
      sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
    backstop.installed.payload.sourceSeed =
        sourceGeneratedClearingBackstopExactSeed ∧
      backstop.installed.payload.consumer =
        sourceClearingBackstopRestriction ∧
      backstop.installed.payload.disposition =
        sourceGeneratedClearingBackstopDisposition ∧
      backstop.localActivation =
        sourceGeneratedClearingBackstopActivation ∧
      sourceGeneratedClearingBackstopExactSeed.occurrence
          partialBResidualConsumerCompiler = partialOccurrence ∧
      sourceGeneratedClearingBackstopExactSeed.openSettlement
          partialBResidualConsumerCompiler = partialOpenB ∧
      (sourceGeneratedClearingBackstopExactSeed.openSettlement
        partialBResidualConsumerCompiler).leg = .b ∧
      sourceGeneratedClearingBackstopExactSeed.activatedConsumer
          partialBResidualConsumerCompiler = rawBackstopAdapter ∧
      backstop.localActivation.edge = fulfillB ∧
      backstop.localActivation.nextGeneratedState.current =
        fulfillB.target ∧
      backstop.localActivation.nextGeneratedState =
        (partialOccurrence.generatedState settlementCompiler).step
          M3FiniteExchangeFixture.P fulfillB ∧
      backstop.localActivation.nextGeneratedState.generated =
        .step (partialOccurrence.generatedState settlementCompiler).generated
          fulfillB ∧
      fulfillB.target.history =
        (partialOccurrence.current settlementCompiler).history ++
          [fulfillB.lifecycleEvent] ∧
      Nonempty (SourceOwnsResponsibilityIncidence
        M3FiniteExchangeFixture.V
        (M3FiniteExchangeFixture.P.boundarySource
          canonicalAClearingFace.counterpartyConsumer.event)
        partialOpenB.obligation) ∧
      Nonempty (AutomaticFullFulfillment.FulfilledSlotAt
        (exchangeLaw := exchangeLaw) exactExchangeSeed
        backstop.localActivation.nextGeneratedState.current (.b : Leg)) ∧
      IsEmpty (FulfilledExchangeLegAt settlementCompiler partialOccurrence
        (.b : Leg))
  sameVisitAuthority :
    let backstop :=
      sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
    backstop.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      backstop.installed.payload.sourceEntry =
        backstop.commonClearing.pclInstalled.payload.sourceEntry ∧
      backstop.installed.payload.sourceEntry =
        backstop.commonClearing.installed.payload.sourceEntry ∧
      backstop.installed.payload.sourceEntry =
        backstop.commonClearing.mandate.installed.payload.sourceEntry ∧
      HEq backstop.installed.payload.selectedRow
        backstop.commonClearing.pclInstalled.payload.selectedRow ∧
      HEq backstop.installed.payload.selectedRow
        backstop.commonClearing.installed.payload.selectedRow ∧
      HEq backstop.installed.payload.selectedRow
        backstop.commonClearing.mandate.installed.payload.selectedRow ∧
      HEq backstop.installed.payload.successor
        backstop.commonClearing.pclInstalled.payload.successor ∧
      HEq backstop.installed.payload.successor
        backstop.commonClearing.installed.payload.successor ∧
      HEq backstop.installed.payload.successor
        backstop.commonClearing.mandate.installed.payload.successor ∧
      HEq backstop.installed.operationalAuthority
        backstop.commonClearing.pclInstalled.operationalAuthority ∧
      HEq backstop.installed.operationalAuthority
        backstop.commonClearing.installed.operationalAuthority ∧
      HEq backstop.installed.operationalAuthority
        backstop.commonClearing.mandate.installed.operationalAuthority
  actualRootUpdate :
    let backstop :=
      sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
    backstop.rootOccurrence =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt (temporalVisitAt depth)) ∧
      clearingBackstopRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current) =
        (.inl ⟨backstop.installed.active,
            backstop.installed.payload⟩ :
          SourceNativeProjectionFiberAt
            clearingBackstopRecognition.law.toProjectionLaw PUnit.unit
            (jointRoot.emitted (temporalVisitAt depth).current)) ∧
      backstop.appliedReform.residualRow =
        backstop.installed.temporalSelectedRow ∧
      backstop.appliedReform.residualRow.sourceRow.CommutesWithWorld ∧
      Nonempty (RenewalResponsibilityConsumerAt
        backstop.installed.operationalAuthority) ∧
      backstop.appliedReform.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      backstop.installed.RootAnswerAndNextFactorizes ∧
      backstop.commonClearing.installed.RootAnswerAndNextFactorizes ∧
      backstop.commonClearing.pclInstalled.RootAnswerAndNextFactorizes ∧
      backstop.commonClearing.mandate.installed.RootAnswerAndNextFactorizes ∧
      backstop.appliedReform.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      backstop.appliedReform.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface ∧
      backstop.appliedReform.generatedNext.visit =
        temporalVisitAt (depth + 1)
  projectionAndActionAuthority :
    let backstop :=
      sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
    jointClearingBackstopProjection ≠ jointCommonClearingProjection ∧
      jointClearingBackstopProjection ≠
        jointRouteOutageRestorationProjection ∧
      jointClearingBackstopProjection ≠
        jointEssentialServiceRestorationProjection ∧
      jointClearingBackstopProjection ≠ jointMandateProjection ∧
      jointClearingBackstopProjection ≠
        jointRecognitionWitnessProjection ∧
      jointClearingBackstopProjection ≠ jointUBIProjection ∧
      jointClearingBackstopProjection ≠ jointProofCarryingProjection ∧
      jointClearingBackstopProjection ≠ jointInquiryProjection ∧
      jointClearingBackstopProjection ≠ jointFailureProjection ∧
      backstop.installed.payload.disposition =
        sourceGeneratedClearingBackstopDisposition ∧
      backstop.commonClearing.installed.payload.disposition =
        sourceGeneratedCommonClearingDisposition ∧
      backstop.localActivation.edge = fulfillB
  compilerControls :
    (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
        (activation.openSettlement residualConsumerCompiler).leg = .b) ∧
      (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
        activation.occurrence residualConsumerCompiler = partialOccurrence) ∧
      (¬ ∃ activation : partialBResidualConsumerCompiler.ExactActivationSeed,
        (activation.openSettlement
          partialBResidualConsumerCompiler).leg = .a) ∧
      (¬ ∃ activation : partialBResidualConsumerCompiler.ExactActivationSeed,
        activation.occurrence partialBResidualConsumerCompiler =
          openOccurrence) ∧
      (∀ activation : partialBResidualConsumerCompiler.ExactActivationSeed,
        activation = sourceGeneratedClearingBackstopExactSeed)
  occurrenceInjective : Function.Injective
    periodicClearingBackstopOccurrenceAt
  adjacentDistinct : periodicClearingBackstopOccurrenceAt depth ≠
    periodicClearingBackstopOccurrenceAt (depth + 1)
  noSingleEternity :
    ¬ ∃ occurrence : AnyPeriodicClearingBackstopOccurrence,
      ∀ index : Nat,
        periodicClearingBackstopOccurrenceAt index = occurrence

/-- Public direct consumer.  Its sole datum is the visit index `depth`; all
authority is read from the depth-only periodic producer and the fixed
same-root coordinate certificate. -/
theorem proofCarryingPeriodicClearingBackstopDirectConsumer (depth : Nat) :
    ProofCarryingPeriodicClearingBackstopCertificateAt depth where
  sameRootCoordinate :=
    proofCarryingSameRootClearingBackstopCoordinateDirectConsumer
  actual := every_generated_period_has_actual_clearingBackstop depth
  exactInstalledIndices := periodic_clearingBackstop_indices_exact depth
  exactSourceImage := periodic_clearingBackstop_exact_source_image depth
  exactLocalActionAndNext :=
    periodic_clearingBackstop_local_activation_exact depth
  sameVisitAuthority :=
    periodic_clearingBackstop_shared_root_authority_exact depth
  actualRootUpdate := periodicBackstopRootUpdateExact depth
  projectionAndActionAuthority :=
    periodicBackstopAllProjectionAndActionAuthorityExact depth
  compilerControls := oldAndBackstopCompilersRemainSeparated
  occurrenceInjective := periodicClearingBackstopOccurrenceAt_injective
  adjacentDistinct := adjacentClearingBackstopOccurrences_distinct depth
  noSingleEternity :=
    no_single_clearingBackstop_occurrence_carries_all_depths

theorem periodicBackstopDirectConsumerMouthHasNoAuthorityPremise
    (depth : Nat) : True := by
  let certificate :=
    proofCarryingPeriodicClearingBackstopDirectConsumer depth
  fail_if_success exact certificate.submittedActivation
  fail_if_success exact certificate.submittedInstalledCoordinate
  fail_if_success exact certificate.submittedRootNext
  fail_if_success exact certificate.coveragePremise
  fail_if_success exact certificate.completedFuture
  trivial

end
end M14ProofCarryingPeriodicClearingBackstopRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicClearingBackstopRegression.periodicBackstopRootUpdateExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicClearingBackstopRegression.periodicBackstopAllProjectionAndActionAuthorityExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicClearingBackstopRegression.proofCarryingPeriodicClearingBackstopDirectConsumer
