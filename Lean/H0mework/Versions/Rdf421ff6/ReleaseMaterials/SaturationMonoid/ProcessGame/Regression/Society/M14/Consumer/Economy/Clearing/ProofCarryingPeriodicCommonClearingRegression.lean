import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Clearing.PeriodicCommonClearingRenewal
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Economy.Clearing.ProofCarryingSameRootCommonClearingCoordinateRegression

/-!
# M14 proof-carrying periodic common clearing

This consumer certifies the depth-only actual carrier.  Every requested root
visit regenerates the common-clearing coordinate, PCL coordinate, public
mandate, selected write, whole-ledger evolution, and next.  Every local
exchange leg still consumes the two boundary-owned fulfillment actions from
the existing exhaustive M4 fold.

The local settlement occurrence and the temporal root occurrence remain two
typed readouts of one assembled certificate; they are never equated.  The
visit-first occurrence is injective, so no clearing authority is free-eternal.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingPeriodicCommonClearingRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Renewal Revision
open Clearing Legislation
open Election Power
open Settlement.SourceOwnedSettlementCompiler
open M3FiniteExchangeFixture
open M3ExchangeSettlementPriceRegression
open M4AutomaticFullFulfillmentRegression
open M8ActualElectionMandateRenewalRegression
open M8RelationshipMaintenanceFixture
open M9ProofCarryingRenewalInquiryRoot
open M14SourceMandateRenewal
open M14SourceCommonClearingRenewal
open M14UBIPeriodicRootHistory
open M14PeriodicMandatePowerRenewal
open M14PeriodicCommonClearingRenewal
open M14ProofCarryingSameRootCommonClearingCoordinateRegression

abbrev PeriodicTwoSidedClearingAt
    (_depth : Nat) (leg : exactExchangeSeed.Leg) : Prop :=
  ∃ face : SourceGeneratedSymmetricClearingAt fulfillmentAuthority
      exactExchangeSeed leg,
    Nonempty (ExactLegFulfillmentAt
      (exchangeLaw := exchangeLaw) exactExchangeSeed leg) ∧
    Nonempty (ExactLegFulfillmentAt
      (exchangeLaw := exchangeLaw) exactExchangeSeed
        face.counterpartyLeg) ∧
    Nonempty (SourceOwnsResponsibilityIncidence V
      (P.boundarySource face.legConsumer.event)
      (exactExchangeSeed.obligation exchangeCompiler leg)) ∧
    Nonempty (SourceOwnsResponsibilityIncidence V
      (P.boundarySource face.counterpartyConsumer.event)
      (exactExchangeSeed.obligation exchangeCompiler
        face.counterpartyLeg)) ∧
    face.legActor ≠ face.counterpartyActor ∧
    face.legSlotIndex ≠ face.counterpartySlotIndex ∧
    Nonempty (AutomaticFullFulfillment.FulfilledSlotAt
      (exchangeLaw := exchangeLaw) exactExchangeSeed
        face.fullResult.current leg) ∧
    Nonempty (AutomaticFullFulfillment.FulfilledSlotAt
      (exchangeLaw := exchangeLaw) exactExchangeSeed
        face.fullResult.current face.counterpartyLeg)

abbrev PeriodicCommonClearingRootContractAt (depth : Nat) : Prop :=
  let clearing :=
    sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
  clearing.rootOccurrence =
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.exactTemporalCausalEventAt (temporalVisitAt depth)) ∧
    commonClearingRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      (.inl ⟨clearing.installed.active, clearing.installed.payload⟩ :
        SourceNativeProjectionFiberAt
          commonClearingRecognition.law.toProjectionLaw PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current)) ∧
    SourceInstalledPolicyCoordinateAt
      clearing.pclInstalled clearing.installed ∧
    SourceInstalledPolicyCoordinateAt
      clearing.pclInstalled clearing.mandate.installed ∧
    HEq clearing.installed.operationalAuthority
      clearing.mandate.installed.operationalAuthority ∧
    Nonempty (RenewalResponsibilityConsumerAt
      clearing.installed.operationalAuthority) ∧
    clearing.installed.payload.sourceEntry =
      RootInquiryU8CompletionRegression.entry ∧
    clearing.appliedReform.residualRow =
      clearing.installed.temporalSelectedRow ∧
    clearing.appliedReform.residualRow.sourceRow.CommutesWithWorld ∧
    clearing.appliedReform.wholeLedgerWriteBack =
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          (temporalVisitAt depth)).wholeLedgerWriteBack ∧
    clearing.installed.RootAnswerAndNextFactorizes ∧
    clearing.pclInstalled.RootAnswerAndNextFactorizes ∧
    clearing.mandate.installed.RootAnswerAndNextFactorizes ∧
    clearing.appliedReform.generatedNext =
      jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
    clearing.installed.payload.disposition.fullResult =
      AutomaticFullFulfillment.fullResult fulfillmentAuthority
        exactExchangeSeed ∧
    HEq clearing.installed.payload.disposition.fullRun automaticWholeRun ∧
    IsEmpty (OpenSettlementAt automaticCompiler automaticOccurrence)

abbrev PeriodicMandateBackingAt (depth : Nat) : Prop :=
  let clearing :=
    sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
  clearing.mandate.installed.payload.sourceSeed = sourceMandateSeed ∧
    clearing.mandate.installed.payload.consumer = sourceMandateConsumer ∧
    clearing.mandate.installed.payload.disposition =
      sourceMandateDisposition ∧
    (∃ state ∈ SourceMandateGame.occurrence.trace,
      SourceMandateSeedAt SourceMandateGame.source state
        clearing.mandate.localFace.event) ∧
    mandateRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      (.inl
        ⟨clearing.mandate.installed.active,
          clearing.mandate.installed.payload⟩ :
        SourceNativeProjectionFiberAt
          mandateRecognition.law.toProjectionLaw PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current)) ∧
    clearing.mandate.rootOccurrence =
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.exactTemporalCausalEventAt (temporalVisitAt depth)) ∧
    clearing.mandate.wholeLedgerWriteBack =
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          (temporalVisitAt depth)).wholeLedgerWriteBack ∧
    clearing.mandate.generatedNext =
      jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
    clearing.mandate.localFace.responsibilityConsumer.1.1.freedomChange.kind =
      FreedomChangeKind.restored ∧
    Nonempty (SourceOwnsResponsibilityIncidence
      (mandateVocabulary lineageCompiler)
      sourceMandateHistory.current
      (mandateObligation lineageCompiler sourceMandateHistory.current)) ∧
    clearing.mandate.localFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler sourceMandateHistory.current).val]? =
      some (.live
        (mandateObligation lineageCompiler sourceMandateHistory.current))

theorem everyDepthAndLegHasActualSymmetricClearing
    (depth : Nat) (leg : exactExchangeSeed.Leg) :
    PeriodicTwoSidedClearingAt depth leg :=
  periodic_commonClearing_every_leg_exact depth leg

theorem everyDepthUsesCanonicalInstalledIndices (depth : Nat) :
    let clearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
    clearing.installed = installedCommonClearingAt depth ∧
      clearing.pclInstalled = installedProofCarryingRenewalAt depth ∧
      clearing.mandate = periodicMandatePowerRenewalAt depth :=
  periodic_commonClearing_indices_exact depth

theorem everyDepthSourceAndActionAreExact (depth : Nat) :
    let clearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
    clearing.installed.payload.sourceSeed = commonClearingSeed ∧
      clearing.installed.payload.consumer =
        sourceCommonClearingRestriction ∧
      clearing.installed.payload.disposition =
        sourceGeneratedCommonClearingDisposition :=
  periodic_commonClearing_source_action_exact depth

theorem everyDepthConsumesRootPolicyAndWholeLedger (depth : Nat) :
    PeriodicCommonClearingRootContractAt depth :=
  periodic_commonClearing_root_policy_and_closure_exact depth

theorem everyDepthConsumesActualMandateBacking (depth : Nat) :
    PeriodicMandateBackingAt depth :=
  periodic_commonClearing_mandate_authority_exact depth

theorem everyDepthGeneratesSameLawNext (depth : Nat) :
    let clearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
    clearing.appliedReform.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      clearing.appliedReform.generatedNext.visit =
        temporalVisitAt (depth + 1) ∧
      clearing.appliedReform.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface :=
  let clearing :=
    sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
  ⟨clearing.generatedNextExact, clearing.nextVisitExact,
    clearing.lawSurfacePreserved⟩

theorem localAndRootOccurrencesRemainTypedSeparately (depth : Nat) :
    let clearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
    clearing.localSettlementOccurrence =
        automaticCompiler.occurrenceOfSeed
          clearing.installed.payload.sourceSeed ∧
      clearing.localSettlementOccurrence = automaticOccurrence ∧
      clearing.rootOccurrence =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt (temporalVisitAt depth)) :=
  let clearing :=
    sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
  ⟨clearing.localSettlementOccurrenceFromInstalledSeed,
    clearing.localSettlementOccurrenceExact,
    clearing.rootOccurrenceExact⟩

theorem everyDepthRetainsIndependentPolicyCoordinates (depth : Nat) :
    let clearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
    SourceInstalledPolicyCoordinateAt
        clearing.pclInstalled clearing.installed ∧
      SourceInstalledPolicyCoordinateAt
        clearing.pclInstalled clearing.mandate.installed ∧
      jointCommonClearingProjection ≠ jointMandateProjection :=
  let clearing :=
    sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
  ⟨clearing.pclCoordinate, clearing.mandateCoordinate,
    commonClearing_projection_ne_mandate_projection⟩

structure ProofCarryingPeriodicCommonClearingCertificate : Prop where
  installedBase :
    ProofCarryingSameRootCommonClearingCoordinateCertificate
  everyDepth : ∀ depth : Nat,
    Nonempty (SourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth)
  exactIndices : ∀ depth : Nat,
    let clearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
    clearing.installed = installedCommonClearingAt depth ∧
      clearing.pclInstalled = installedProofCarryingRenewalAt depth ∧
      clearing.mandate = periodicMandatePowerRenewalAt depth
  sourceActionExact : ∀ depth : Nat,
    let clearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
    clearing.installed.payload.sourceSeed = commonClearingSeed ∧
      clearing.installed.payload.consumer =
        sourceCommonClearingRestriction ∧
      clearing.installed.payload.disposition =
        sourceGeneratedCommonClearingDisposition
  everyLeg : ∀ (depth : Nat) (leg : exactExchangeSeed.Leg),
    PeriodicTwoSidedClearingAt depth leg
  rootPolicyWholeLedger : ∀ depth : Nat,
    PeriodicCommonClearingRootContractAt depth
  mandateBacking : ∀ depth : Nat, PeriodicMandateBackingAt depth
  sameLawNext : ∀ depth : Nat,
    let clearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
    clearing.appliedReform.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) ∧
      clearing.appliedReform.generatedNext.visit =
        temporalVisitAt (depth + 1) ∧
      clearing.appliedReform.generatedNext.root.source.lawSurface =
        jointRoot.source.base.lawSurface
  typedOccurrences : ∀ depth : Nat,
    let clearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
    clearing.localSettlementOccurrence =
        automaticCompiler.occurrenceOfSeed
          clearing.installed.payload.sourceSeed ∧
      clearing.localSettlementOccurrence = automaticOccurrence ∧
      clearing.rootOccurrence =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt (temporalVisitAt depth))
  independentPolicyCoordinates : ∀ depth : Nat,
    let clearing :=
      sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
    SourceInstalledPolicyCoordinateAt
        clearing.pclInstalled clearing.installed ∧
      SourceInstalledPolicyCoordinateAt
        clearing.pclInstalled clearing.mandate.installed ∧
      jointCommonClearingProjection ≠ jointMandateProjection
  occurrenceInjective : Function.Injective
    periodicCommonClearingOccurrenceAt
  adjacentOccurrencesDistinct : ∀ depth : Nat,
    periodicCommonClearingOccurrenceAt depth ≠
      periodicCommonClearingOccurrenceAt (depth + 1)
  noFreeEternalClearing :
    ¬ ∃ occurrence : AnyPeriodicCommonClearingOccurrence,
      ∀ depth : Nat,
        periodicCommonClearingOccurrenceAt depth = occurrence
  strictControls :
    (¬ Nonempty
      (FullyFulfilledExchangeAt nilOpenCompiler nilOpenOccurrence)) ∧
      (∀ leg : exactExchangeSeed.Leg,
        let face := canonicalClearingFace leg
        IsEmpty (AutomaticFullFulfillment.FulfilledSlotAt
          (exchangeLaw := exchangeLaw) exactExchangeSeed
          face.oneSidedEdge.target face.counterpartyLeg)) ∧
      (¬ ∃ activation : residualConsumerCompiler.ExactActivationSeed,
        (activation.openSettlement residualConsumerCompiler).leg =
          exactExchangeSeed.counterparty exchangeCompiler .a) ∧
      IsEmpty (SelectedMaintenanceDebtFlowAt (legToken .a)
        (counterparty .a) .a)
  noSubmittedAuthorityOrFuture : ∀ _depth : Nat, True

theorem proofCarryingPeriodicCommonClearingDirectConsumer :
    ProofCarryingPeriodicCommonClearingCertificate where
  installedBase :=
    proofCarryingSameRootCommonClearingCoordinateDirectConsumer
  everyDepth := every_generated_period_has_actual_commonClearing
  exactIndices := everyDepthUsesCanonicalInstalledIndices
  sourceActionExact := everyDepthSourceAndActionAreExact
  everyLeg := everyDepthAndLegHasActualSymmetricClearing
  rootPolicyWholeLedger := everyDepthConsumesRootPolicyAndWholeLedger
  mandateBacking := everyDepthConsumesActualMandateBacking
  sameLawNext := everyDepthGeneratesSameLawNext
  typedOccurrences := localAndRootOccurrencesRemainTypedSeparately
  independentPolicyCoordinates :=
    everyDepthRetainsIndependentPolicyCoordinates
  occurrenceInjective := periodicCommonClearingOccurrenceAt_injective
  adjacentOccurrencesDistinct :=
    adjacentCommonClearingOccurrences_distinct
  noFreeEternalClearing :=
    no_single_commonClearing_occurrence_carries_all_depths
  strictControls := strictCommonClearingControls
  noSubmittedAuthorityOrFuture :=
    periodic_commonClearing_mouth_has_no_submitted_authority_or_future

end
end M14ProofCarryingPeriodicCommonClearingRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingPeriodicCommonClearingRegression.proofCarryingPeriodicCommonClearingDirectConsumer
