import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Legislation.ProofCarryingPolicyCoordinate
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M9.JointRoot.ProofCarryingRenewalInquiryRoot

/-!
# M14 direct consumer for the same-root clearing-backstop coordinate

The exact C5 residual-consumer occurrence is now the final pre-emitter
renewal coordinate of the literal M9/M13/M14 root.  This consumer checks both
authority layers without conflating them: the local process occurrence
generates `fulfillB` and its local whole-run next, while the installed root
coordinate separately factors through the fixed root occurrence and its
compiler-generated living next.

No periodic claim, second root, settlement occurrence, event, run, ledger,
registry, coverage table, or completed future is introduced here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingSameRootClearingBackstopCoordinateRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Renewal Clearing
open Legislation
open Lifecycle.Universal.FixedAdapter
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression
open M4AutomaticFullFulfillmentRegression
open M9ProofCarryingRenewalInquiryRoot
open M14ClearingConsumerDeath
open M14SourceGeneratedClearingBackstopActivation
open M14SourceClearingBackstopRenewal

/-! ## Exact installed source image -/

theorem installedClearingBackstopExact :
    Nonempty (SourceInstalledRenewalAt clearingBackstopRecognition jointVisit) ∧
      installedClearingBackstop.payload.sourceSeed =
        sourceGeneratedClearingBackstopExactSeed ∧
      installedClearingBackstop.payload.consumer =
        sourceClearingBackstopRestriction ∧
      installedClearingBackstop.payload.disposition =
        sourceGeneratedClearingBackstopDisposition ∧
      partialBResidualConsumerCompiler.consumerOfSeed
          installedClearingBackstop.payload.sourceSeed =
        sourceGeneratedClearingBackstopActivation :=
  ⟨⟨installedClearingBackstop⟩, rfl, rfl, rfl, rfl⟩

theorem installedClearingBackstopExactSourceProvenance :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = core.targetFace.state Lifecycle.actualEventGame.source ∧
        partialBResidualConsumerCompiler.activationAdmittedAt
          installedClearingBackstop.payload.sourceSeed.1 := by
  simpa only [installedClearingBackstop_seed_eq] using
    backstop_exact_source_provenance

/-! ## Local process action, kept distinct from the living-root next -/

def ClearingBackstopLocalActionContract : Prop :=
    sourceGeneratedClearingBackstopExactSeed.occurrence
          partialBResidualConsumerCompiler = partialOccurrence ∧
      sourceGeneratedClearingBackstopExactSeed.openSettlement
          partialBResidualConsumerCompiler = partialOpenB ∧
      (sourceGeneratedClearingBackstopExactSeed.openSettlement
          partialBResidualConsumerCompiler).leg = (.b : Leg) ∧
      sourceGeneratedClearingBackstopExactSeed.activation
          partialBResidualConsumerCompiler =
        canonicalAClearingFace.counterpartyConsumer.event ∧
      sourceGeneratedClearingBackstopConsumer = rawBackstopAdapter ∧
      sourceGeneratedClearingBackstopActivation.edge = fulfillB ∧
      sourceGeneratedClearingBackstopActivation.nextGeneratedState.current =
        fulfillB.target ∧
      sourceGeneratedClearingBackstopActivation.nextGeneratedState =
        (partialOccurrence.generatedState settlementCompiler).step
          M3FiniteExchangeFixture.P
          fulfillB ∧
      sourceGeneratedClearingBackstopActivation.nextGeneratedState.generated =
        .step (partialOccurrence.generatedState settlementCompiler).generated
          fulfillB ∧
      fulfillB.target.history =
        (partialOccurrence.current settlementCompiler).history ++
          [fulfillB.lifecycleEvent] ∧
      Nonempty (SourceOwnsResponsibilityIncidence M3FiniteExchangeFixture.V
        (P.boundarySource
          canonicalAClearingFace.counterpartyConsumer.event)
        partialOpenB.obligation) ∧
      Nonempty (AutomaticFullFulfillment.FulfilledSlotAt
        (exchangeLaw := exchangeLaw) exactExchangeSeed
        sourceGeneratedClearingBackstopActivation.nextGeneratedState.current
        (.b : Leg))

theorem installedClearingBackstopLocalActionExact :
    ClearingBackstopLocalActionContract := by
  exact ⟨backstop_occurrence_exact,
    backstop_openSettlement_exact,
    backstop_leg_exact,
    backstop_boundaryEvent_exact,
    backstop_consumer_is_C4_adapter,
    backstop_edge_exact,
    backstop_next_current_exact,
    backstop_nextGeneratedState_exact,
    backstop_whole_generated_next_exact,
    backstop_history_exact,
    ⟨backstopSourceOwnership⟩,
    ⟨backstopFulfilledB⟩⟩

/-- The old partial occurrence itself still has a live `b` slot.  C5's
fulfillment belongs to the generated local next, not retroactively to the
source occurrence. -/
theorem partialOccurrenceB_fulfilledFibre_isEmpty :
    IsEmpty (FulfilledExchangeLegAt settlementCompiler partialOccurrence
      (.b : Leg)) := by
  change IsEmpty (FulfilledExchangeLegAt settlementCompiler
    partialOccurrence partialOpenB.leg)
  exact partialOpenB.fulfilledLeg_isEmpty

/-! ## Old/new compiler separation -/

theorem oldAndBackstopCompilersRemainSeparated :
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
        activation = sourceGeneratedClearingBackstopExactSeed) :=
  ⟨residualCompiler_cannot_select_B,
    residualCompiler_cannot_point_to_partialOccurrence,
    backstopCompiler_cannot_select_A,
    backstopCompiler_cannot_point_to_openOccurrence,
    backstopCompiler_has_unique_exact_seed⟩

/-! ## Same-root policy and authority -/

theorem clearingBackstopPolicyCoordinate :
    SourceInstalledPolicyCoordinateAt installedRenewal
      installedClearingBackstop where
  sourceEntry_eq := clearingBackstop_shares_sourceEntry
  selectedRow_heq := clearingBackstop_shares_selectedRow
  successor_heq := clearingBackstop_shares_successor

theorem mandatePolicyCoordinate :
    SourceInstalledPolicyCoordinateAt installedRenewal installedMandate where
  sourceEntry_eq := mandate_shares_sourceEntry
  selectedRow_heq := mandate_shares_selectedRow
  successor_heq := mandate_shares_successor

theorem commonClearingPolicyCoordinate :
    SourceInstalledPolicyCoordinateAt installedRenewal
      installedCommonClearing where
  sourceEntry_eq := commonClearing_shares_sourceEntry
  selectedRow_heq := commonClearing_shares_selectedRow
  successor_heq := commonClearing_shares_successor

theorem clearingBackstopSharesRootAuthority :
    installedClearingBackstop.payload.sourceEntry =
        installedRenewal.payload.sourceEntry ∧
      HEq installedClearingBackstop.payload.selectedRow
        installedRenewal.payload.selectedRow ∧
      HEq installedClearingBackstop.payload.successor
        installedRenewal.payload.successor ∧
      installedClearingBackstop.payload.sourceEntry =
        installedMandate.payload.sourceEntry ∧
      HEq installedClearingBackstop.payload.selectedRow
        installedMandate.payload.selectedRow ∧
      HEq installedClearingBackstop.payload.successor
        installedMandate.payload.successor ∧
      installedClearingBackstop.payload.sourceEntry =
        installedCommonClearing.payload.sourceEntry ∧
      HEq installedClearingBackstop.payload.selectedRow
        installedCommonClearing.payload.selectedRow ∧
      HEq installedClearingBackstop.payload.successor
        installedCommonClearing.payload.successor ∧
      HEq installedClearingBackstop.operationalAuthority
        installedRenewal.operationalAuthority ∧
      HEq installedClearingBackstop.operationalAuthority
        installedMandate.operationalAuthority ∧
      HEq installedClearingBackstop.operationalAuthority
        installedCommonClearing.operationalAuthority ∧
      Nonempty (RenewalResponsibilityConsumerAt
        installedClearingBackstop.operationalAuthority) ∧
      installedClearingBackstop.RootAnswerAndNextFactorizes ∧
      (jointRoot.canonicalCausalAnswerAndNext (ULift.up jointVisit)
          ).nextCurrent = jointRoot.generatedNextCurrentAt jointVisit ∧
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          jointVisit =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          jointVisit ∧
      jointAuthoritySource.restructuringSource =
        (RootInquiryU8CompletionRegression.root.toAuthoritativeRoot.source
          ).restructuringSource := by
  exact ⟨clearingBackstop_shares_sourceEntry,
    clearingBackstop_shares_selectedRow,
    clearingBackstop_shares_successor,
    rfl, HEq.rfl, HEq.rfl,
    clearingBackstop_shares_commonClearing_sourceEntry,
    clearingBackstop_shares_commonClearing_selectedRow,
    clearingBackstop_shares_commonClearing_successor,
    HEq.rfl, HEq.rfl, HEq.rfl,
    ⟨installedClearingBackstop.rootResponsibilityConsumer⟩,
    clearingBackstop_root_factorization,
    clearingBackstop_root_factorization.2.2,
    renewal_and_inquiry_share_occurrence,
    joint_restructuringSource_is_original⟩

theorem clearingBackstopCoordinateIsIndependentAuthority :
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
      jointClearingBackstopProjection ≠ jointFailureProjection :=
  clearingBackstop_projection_distinct_from_existing_coordinates

/-! ## Prop-only direct sink -/

structure ProofCarryingSameRootClearingBackstopCoordinateCertificate : Prop where
  installedExact :
    Nonempty (SourceInstalledRenewalAt clearingBackstopRecognition jointVisit) ∧
      installedClearingBackstop.payload.sourceSeed =
        sourceGeneratedClearingBackstopExactSeed ∧
      installedClearingBackstop.payload.consumer =
        sourceClearingBackstopRestriction ∧
      installedClearingBackstop.payload.disposition =
        sourceGeneratedClearingBackstopDisposition ∧
      partialBResidualConsumerCompiler.consumerOfSeed
          installedClearingBackstop.payload.sourceSeed =
        sourceGeneratedClearingBackstopActivation
  exactSourceProvenance :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      state = core.targetFace.state Lifecycle.actualEventGame.source ∧
        partialBResidualConsumerCompiler.activationAdmittedAt
          installedClearingBackstop.payload.sourceSeed.1
  localActionExact : ClearingBackstopLocalActionContract
  sourceOccurrenceBStillOpen :
    IsEmpty (FulfilledExchangeLegAt settlementCompiler partialOccurrence
      (.b : Leg))
  compilerSeparation :
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
  pclCoordinate : SourceInstalledPolicyCoordinateAt installedRenewal
    installedClearingBackstop
  mandateCoordinate : SourceInstalledPolicyCoordinateAt installedRenewal
    installedMandate
  commonClearingCoordinate : SourceInstalledPolicyCoordinateAt installedRenewal
    installedCommonClearing
  sameRootAuthority :
    installedClearingBackstop.payload.sourceEntry =
        installedRenewal.payload.sourceEntry ∧
      HEq installedClearingBackstop.payload.selectedRow
        installedRenewal.payload.selectedRow ∧
      HEq installedClearingBackstop.payload.successor
        installedRenewal.payload.successor ∧
      installedClearingBackstop.payload.sourceEntry =
        installedMandate.payload.sourceEntry ∧
      HEq installedClearingBackstop.payload.selectedRow
        installedMandate.payload.selectedRow ∧
      HEq installedClearingBackstop.payload.successor
        installedMandate.payload.successor ∧
      installedClearingBackstop.payload.sourceEntry =
        installedCommonClearing.payload.sourceEntry ∧
      HEq installedClearingBackstop.payload.selectedRow
        installedCommonClearing.payload.selectedRow ∧
      HEq installedClearingBackstop.payload.successor
        installedCommonClearing.payload.successor ∧
      HEq installedClearingBackstop.operationalAuthority
        installedRenewal.operationalAuthority ∧
      HEq installedClearingBackstop.operationalAuthority
        installedMandate.operationalAuthority ∧
      HEq installedClearingBackstop.operationalAuthority
        installedCommonClearing.operationalAuthority ∧
      Nonempty (RenewalResponsibilityConsumerAt
        installedClearingBackstop.operationalAuthority) ∧
      installedClearingBackstop.RootAnswerAndNextFactorizes ∧
      (jointRoot.canonicalCausalAnswerAndNext (ULift.up jointVisit)
          ).nextCurrent = jointRoot.generatedNextCurrentAt jointVisit ∧
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
          jointVisit =
        jointRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
          jointVisit ∧
      jointAuthoritySource.restructuringSource =
        (RootInquiryU8CompletionRegression.root.toAuthoritativeRoot.source
          ).restructuringSource
  independentAuthority :
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
      jointClearingBackstopProjection ≠ jointFailureProjection

theorem proofCarryingSameRootClearingBackstopCoordinateDirectConsumer :
    ProofCarryingSameRootClearingBackstopCoordinateCertificate where
  installedExact := installedClearingBackstopExact
  exactSourceProvenance := installedClearingBackstopExactSourceProvenance
  localActionExact := installedClearingBackstopLocalActionExact
  sourceOccurrenceBStillOpen := partialOccurrenceB_fulfilledFibre_isEmpty
  compilerSeparation := oldAndBackstopCompilersRemainSeparated
  pclCoordinate := clearingBackstopPolicyCoordinate
  mandateCoordinate := mandatePolicyCoordinate
  commonClearingCoordinate := commonClearingPolicyCoordinate
  sameRootAuthority := clearingBackstopSharesRootAuthority
  independentAuthority := clearingBackstopCoordinateIsIndependentAuthority

end
end M14ProofCarryingSameRootClearingBackstopCoordinateRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameRootClearingBackstopCoordinateRegression.installedClearingBackstopExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameRootClearingBackstopCoordinateRegression.installedClearingBackstopLocalActionExact
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameRootClearingBackstopCoordinateRegression.partialOccurrenceB_fulfilledFibre_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameRootClearingBackstopCoordinateRegression.oldAndBackstopCompilersRemainSeparated
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameRootClearingBackstopCoordinateRegression.clearingBackstopSharesRootAuthority
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameRootClearingBackstopCoordinateRegression.clearingBackstopCoordinateIsIndependentAuthority
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingSameRootClearingBackstopCoordinateRegression.proofCarryingSameRootClearingBackstopCoordinateDirectConsumer
