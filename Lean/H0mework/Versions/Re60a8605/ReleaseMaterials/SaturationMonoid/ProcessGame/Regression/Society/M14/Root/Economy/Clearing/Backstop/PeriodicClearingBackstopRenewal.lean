import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Clearing.PeriodicCommonClearingRenewal

/-!
# M14 periodic proof-carrying clearing backstop

The source-generated activation of the existing `partialOccurrence/.b`
responsibility is installed at every finite visit of the literal joint root.
The backstop shares the visit, source entry, selected row, successor,
operational authority, whole-ledger compiler, and generated next with the
existing common-clearing, proof-carrying-renewal, and mandate coordinates.
Its projection and typed local disposition remain independent coordinates.

The local settlement occurrence is always the existing `partialOccurrence`;
the root occurrence is the differently typed exact temporal causal event.
No equality between those occurrence types is introduced.  The sole public
producer accepts only `depth`; activation, adapter, edge, run step, history,
source ownership, root row, ledger, and next are generated internally.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14PeriodicClearingBackstopRenewal

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

/-! ## Same-visit installation and PCL coordinate -/

def installedClearingBackstopAt (depth : Nat) :
    SourceInstalledRenewalAt clearingBackstopRecognition
      (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

theorem clearingBackstopPolicyCoordinateAt (depth : Nat) :
    SourceInstalledPolicyCoordinateAt
      (installedProofCarryingRenewalAt depth)
      (installedClearingBackstopAt depth) where
  sourceEntry_eq := rfl
  selectedRow_heq := HEq.rfl
  successor_heq := HEq.rfl

/-! ## Full visit-indexed actual carrier -/

structure SourceGeneratedProofCarryingPeriodicClearingBackstopAt
    (depth : Nat) : Type 18 where
  private mk ::
  installed : SourceInstalledRenewalAt clearingBackstopRecognition
    (temporalVisitAt depth)
  installedExact : installed = installedClearingBackstopAt depth
  sourceSeedExact : installed.payload.sourceSeed =
    sourceGeneratedClearingBackstopExactSeed
  sourceConsumerExact : installed.payload.consumer =
    sourceClearingBackstopRestriction
  sourceDispositionExact : installed.payload.disposition =
    sourceGeneratedClearingBackstopDisposition
  commonClearing :
    SourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
  commonClearingExact : commonClearing =
    sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
  pclCoordinate : SourceInstalledPolicyCoordinateAt
    commonClearing.pclInstalled installed
  commonClearingCoordinate : SourceInstalledPolicyCoordinateAt
    commonClearing.pclInstalled commonClearing.installed
  mandateCoordinate : SourceInstalledPolicyCoordinateAt
    commonClearing.pclInstalled commonClearing.mandate.installed
  sourceEntryExact : installed.payload.sourceEntry =
    RootInquiryU8CompletionRegression.entry
  backstopAndPCLSourceEntryShared : installed.payload.sourceEntry =
    commonClearing.pclInstalled.payload.sourceEntry
  backstopAndCommonClearingSourceEntryShared :
    installed.payload.sourceEntry =
      commonClearing.installed.payload.sourceEntry
  backstopAndMandateSourceEntryShared : installed.payload.sourceEntry =
    commonClearing.mandate.installed.payload.sourceEntry
  backstopAndPCLSelectedRowShared :
    HEq installed.payload.selectedRow
      commonClearing.pclInstalled.payload.selectedRow
  backstopAndCommonClearingSelectedRowShared :
    HEq installed.payload.selectedRow
      commonClearing.installed.payload.selectedRow
  backstopAndMandateSelectedRowShared :
    HEq installed.payload.selectedRow
      commonClearing.mandate.installed.payload.selectedRow
  backstopAndPCLSuccessorShared :
    HEq installed.payload.successor
      commonClearing.pclInstalled.payload.successor
  backstopAndCommonClearingSuccessorShared :
    HEq installed.payload.successor
      commonClearing.installed.payload.successor
  backstopAndMandateSuccessorShared :
    HEq installed.payload.successor
      commonClearing.mandate.installed.payload.successor
  backstopAndPCLOperationalAuthorityShared :
    HEq installed.operationalAuthority
      commonClearing.pclInstalled.operationalAuthority
  backstopAndCommonClearingOperationalAuthorityShared :
    HEq installed.operationalAuthority
      commonClearing.installed.operationalAuthority
  backstopAndMandateOperationalAuthorityShared :
    HEq installed.operationalAuthority
      commonClearing.mandate.installed.operationalAuthority
  localActivation :
    partialBResidualConsumerCompiler.GeneratedResidualConsumerOccurrence
  localActivationExact : localActivation =
    sourceGeneratedClearingBackstopActivation
  localActivationInExactSourceImage :
    ∃ seed : partialBResidualConsumerCompiler.ExactActivationSeed,
      partialBResidualConsumerCompiler.consumerOfSeed seed =
          localActivation ∧
      installed.payload.sourceSeed = seed ∧
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = core.targetFace.state Lifecycle.actualEventGame.source ∧
          partialBResidualConsumerCompiler.activationAdmittedAt seed.1) ∧
      seed.occurrence partialBResidualConsumerCompiler = partialOccurrence ∧
      seed.openSettlement partialBResidualConsumerCompiler = partialOpenB ∧
      seed.activation partialBResidualConsumerCompiler =
        canonicalAClearingFace.counterpartyConsumer.event
  localSettlementOccurrenceExact :
    sourceGeneratedClearingBackstopExactSeed.occurrence
        partialBResidualConsumerCompiler = partialOccurrence
  localOpenSettlementExact :
    sourceGeneratedClearingBackstopExactSeed.openSettlement
        partialBResidualConsumerCompiler = partialOpenB
  localLegExact :
    (sourceGeneratedClearingBackstopExactSeed.openSettlement
      partialBResidualConsumerCompiler).leg = .b
  localBoundaryEventExact :
    sourceGeneratedClearingBackstopExactSeed.activation
        partialBResidualConsumerCompiler =
      canonicalAClearingFace.counterpartyConsumer.event
  localActivatedConsumerExact :
    sourceGeneratedClearingBackstopExactSeed.activatedConsumer
        partialBResidualConsumerCompiler = rawBackstopAdapter
  localEdgeExact : localActivation.edge = fulfillB
  localNextCurrentExact : localActivation.nextGeneratedState.current =
    fulfillB.target
  localWholeGeneratedStateExact : localActivation.nextGeneratedState =
    (partialOccurrence.generatedState settlementCompiler).step
      M3FiniteExchangeFixture.P fulfillB
  localWholeGeneratedStepExact :
    localActivation.nextGeneratedState.generated =
      .step (partialOccurrence.generatedState settlementCompiler).generated
        fulfillB
  localHistoryExact : fulfillB.target.history =
    (partialOccurrence.current settlementCompiler).history ++
      [fulfillB.lifecycleEvent]
  localSourceOwnership : Nonempty (SourceOwnsResponsibilityIncidence
    M3FiniteExchangeFixture.V
    (M3FiniteExchangeFixture.P.boundarySource
      canonicalAClearingFace.counterpartyConsumer.event)
    partialOpenB.obligation)
  localNextFulfilledB : Nonempty
    (AutomaticFullFulfillment.FulfilledSlotAt
      (exchangeLaw := exchangeLaw) exactExchangeSeed
      localActivation.nextGeneratedState.current (.b : Leg))
  oldLocalOccurrenceStillOpenB : IsEmpty
    (FulfilledExchangeLegAt settlementCompiler partialOccurrence (.b : Leg))
  rootOccurrence : ExactTemporalCausalRootEventAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot (temporalVisitAt depth)
  rootOccurrenceExact : rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt depth)
  componentOutcomeExact :
    clearingBackstopRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
        (jointRoot.emitted (temporalVisitAt depth).current) =
      (.inl ⟨installed.active, installed.payload⟩ :
        SourceNativeProjectionFiberAt
          clearingBackstopRecognition.law.toProjectionLaw PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current))
  appliedReform : SourceNativeBoundedInstitutionalReformAt
    installed.operationalAuthority
  selectedWriteExact : appliedReform.residualRow =
    installed.temporalSelectedRow
  selectedWriteCommutes :
    appliedReform.residualRow.sourceRow.CommutesWithWorld
  rootConsumer : RenewalResponsibilityConsumerAt
    installed.operationalAuthority
  wholeLedgerExact : appliedReform.wholeLedgerWriteBack =
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit
        (temporalVisitAt depth)).wholeLedgerWriteBack
  rootFactorization : installed.RootAnswerAndNextFactorizes
  commonClearingRootFactorization :
    commonClearing.installed.RootAnswerAndNextFactorizes
  pclRootFactorization :
    commonClearing.pclInstalled.RootAnswerAndNextFactorizes
  mandateRootFactorization :
    commonClearing.mandate.installed.RootAnswerAndNextFactorizes
  generatedNextExact : appliedReform.generatedNext =
    jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  lawSurfacePreserved : appliedReform.generatedNext.root.source.lawSurface =
    jointRoot.source.base.lawSurface
  nextVisitExact : appliedReform.generatedNext.visit =
    temporalVisitAt (depth + 1)
  projectionDistinct :
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

/-- Sole periodic producer.  No activation, adapter, edge, local occurrence,
run, policy authority, root occurrence, row, ledger, or next is accepted from
the caller. -/
def sourceGeneratedProofCarryingPeriodicClearingBackstopAt (depth : Nat) :
    SourceGeneratedProofCarryingPeriodicClearingBackstopAt depth := by
  let installed := installedClearingBackstopAt depth
  let commonClearing :=
    sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth
  let localActivation := sourceGeneratedClearingBackstopActivation
  let reform := SourceNativeBoundedInstitutionalReformAt.generate
    installed.operationalAuthority
  exact
    { installed := installed
      installedExact := rfl
      sourceSeedExact := rfl
      sourceConsumerExact := rfl
      sourceDispositionExact := rfl
      commonClearing := commonClearing
      commonClearingExact := rfl
      pclCoordinate := clearingBackstopPolicyCoordinateAt depth
      commonClearingCoordinate := commonClearing.pclCoordinate
      mandateCoordinate := commonClearing.mandateCoordinate
      sourceEntryExact := rfl
      backstopAndPCLSourceEntryShared := rfl
      backstopAndCommonClearingSourceEntryShared := rfl
      backstopAndMandateSourceEntryShared := rfl
      backstopAndPCLSelectedRowShared := HEq.rfl
      backstopAndCommonClearingSelectedRowShared := HEq.rfl
      backstopAndMandateSelectedRowShared := HEq.rfl
      backstopAndPCLSuccessorShared := HEq.rfl
      backstopAndCommonClearingSuccessorShared := HEq.rfl
      backstopAndMandateSuccessorShared := HEq.rfl
      backstopAndPCLOperationalAuthorityShared := HEq.rfl
      backstopAndCommonClearingOperationalAuthorityShared := HEq.rfl
      backstopAndMandateOperationalAuthorityShared := HEq.rfl
      localActivation := localActivation
      localActivationExact := rfl
      localActivationInExactSourceImage :=
        ⟨sourceGeneratedClearingBackstopExactSeed,
          rfl, rfl, backstop_exact_source_provenance,
          backstop_occurrence_exact, backstop_openSettlement_exact,
          backstop_boundaryEvent_exact⟩
      localSettlementOccurrenceExact := backstop_occurrence_exact
      localOpenSettlementExact := backstop_openSettlement_exact
      localLegExact := backstop_leg_exact
      localBoundaryEventExact := backstop_boundaryEvent_exact
      localActivatedConsumerExact := backstop_consumer_is_C4_adapter
      localEdgeExact := backstop_edge_exact
      localNextCurrentExact := backstop_next_current_exact
      localWholeGeneratedStateExact := backstop_nextGeneratedState_exact
      localWholeGeneratedStepExact := backstop_whole_generated_next_exact
      localHistoryExact := backstop_history_exact
      localSourceOwnership := ⟨backstopSourceOwnership⟩
      localNextFulfilledB := ⟨backstopFulfilledB⟩
      oldLocalOccurrenceStillOpenB :=
        backstop_oldOccurrence_B_fulfillment_isEmpty
      rootOccurrence :=
        jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt (temporalVisitAt depth)
      rootOccurrenceExact := rfl
      componentOutcomeExact := installed.componentOutcome_eq_activePayload
      appliedReform := reform
      selectedWriteExact := rfl
      selectedWriteCommutes :=
        reform.residualRow_commutes_with_wholeLedger
      rootConsumer := installed.rootResponsibilityConsumer
      wholeLedgerExact := rfl
      rootFactorization := installed.rootAnswerAndNext_factorizes
      commonClearingRootFactorization := commonClearing.rootFactorization
      pclRootFactorization := commonClearing.pclRootFactorization
      mandateRootFactorization := commonClearing.mandateRootFactorization
      generatedNextExact := reform.generatedNext_eq_rootCompiler
      lawSurfacePreserved := reform.lawSurface_preserved
      nextVisitExact := rfl
      projectionDistinct :=
        clearingBackstop_projection_distinct_from_existing_coordinates }

theorem every_generated_period_has_actual_clearingBackstop (depth : Nat) :
    Nonempty
      (SourceGeneratedProofCarryingPeriodicClearingBackstopAt depth) :=
  ⟨sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth⟩

theorem periodic_clearingBackstop_indices_exact (depth : Nat) :
    let backstop :=
      sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
    backstop.installed = installedClearingBackstopAt depth ∧
      backstop.commonClearing =
        sourceGeneratedProofCarryingPeriodicSymmetricClearingAt depth ∧
      backstop.commonClearing.pclInstalled =
        installedProofCarryingRenewalAt depth ∧
      backstop.commonClearing.mandate =
        periodicMandatePowerRenewalAt depth :=
  let backstop :=
    sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
  ⟨backstop.installedExact,
    backstop.commonClearingExact,
    backstop.commonClearing.pclInstalledExact,
    backstop.commonClearing.mandateExact⟩

theorem periodic_clearingBackstop_local_activation_exact (depth : Nat) :
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
          M3FiniteExchangeFixture.P
          fulfillB ∧
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
        (.b : Leg)) :=
  let backstop :=
    sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
  ⟨backstop.sourceSeedExact,
    backstop.sourceConsumerExact,
    backstop.sourceDispositionExact,
    backstop.localActivationExact,
    backstop.localSettlementOccurrenceExact,
    backstop.localOpenSettlementExact,
    backstop.localLegExact,
    backstop.localActivatedConsumerExact,
    backstop.localEdgeExact,
    backstop.localNextCurrentExact,
    backstop.localWholeGeneratedStateExact,
    backstop.localWholeGeneratedStepExact,
    backstop.localHistoryExact,
    backstop.localSourceOwnership,
    backstop.localNextFulfilledB,
    backstop.oldLocalOccurrenceStillOpenB⟩

theorem periodic_clearingBackstop_exact_source_image (depth : Nat) :
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
        canonicalAClearingFace.counterpartyConsumer.event :=
  (sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
    ).localActivationInExactSourceImage

theorem periodic_clearingBackstop_shared_root_authority_exact
    (depth : Nat) :
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
        backstop.commonClearing.mandate.installed.operationalAuthority :=
  let backstop :=
    sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
  ⟨backstop.sourceEntryExact,
    backstop.backstopAndPCLSourceEntryShared,
    backstop.backstopAndCommonClearingSourceEntryShared,
    backstop.backstopAndMandateSourceEntryShared,
    backstop.backstopAndPCLSelectedRowShared,
    backstop.backstopAndCommonClearingSelectedRowShared,
    backstop.backstopAndMandateSelectedRowShared,
    backstop.backstopAndPCLSuccessorShared,
    backstop.backstopAndCommonClearingSuccessorShared,
    backstop.backstopAndMandateSuccessorShared,
    backstop.backstopAndPCLOperationalAuthorityShared,
    backstop.backstopAndCommonClearingOperationalAuthorityShared,
    backstop.backstopAndMandateOperationalAuthorityShared⟩

theorem periodic_clearingBackstop_root_write_and_next_exact (depth : Nat) :
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
    backstop.nextVisitExact⟩

theorem periodic_clearingBackstop_projection_and_action_authority_exact
    (depth : Nat) :
    let backstop :=
      sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
    jointClearingBackstopProjection ≠ jointCommonClearingProjection ∧
      backstop.installed.payload.disposition =
        sourceGeneratedClearingBackstopDisposition ∧
      backstop.commonClearing.installed.payload.disposition =
        sourceGeneratedCommonClearingDisposition ∧
      backstop.localActivation.edge = fulfillB :=
  let backstop :=
    sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
  ⟨backstop.projectionDistinct.1,
    backstop.sourceDispositionExact,
    backstop.commonClearing.dispositionExact,
    backstop.localEdgeExact⟩

/-! ## Visit-indexed non-eternity -/

structure ClearingBackstopRenewalAtVisit
    (visit : SourceNativeTemporalVisitAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot) : Type 18 where
  private mk ::
  depth : Nat
  visitExact : visit = temporalVisitAt depth
  backstop : SourceGeneratedProofCarryingPeriodicClearingBackstopAt depth

abbrev AnyPeriodicClearingBackstopOccurrence :=
  Sigma ClearingBackstopRenewalAtVisit

def periodicClearingBackstopOccurrenceAt
    (depth : Nat) : AnyPeriodicClearingBackstopOccurrence :=
  ⟨temporalVisitAt depth,
    ⟨depth, rfl,
      sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth⟩⟩

theorem periodicClearingBackstopOccurrenceAt_injective :
    Function.Injective periodicClearingBackstopOccurrenceAt := by
  intro left right equality
  have visitEquality := congrArg Sigma.fst equality
  exact temporalVisitAt_injective visitEquality

theorem adjacentClearingBackstopOccurrences_distinct (depth : Nat) :
    periodicClearingBackstopOccurrenceAt depth ≠
      periodicClearingBackstopOccurrenceAt (depth + 1) := by
  intro equality
  have depthEquality :=
    periodicClearingBackstopOccurrenceAt_injective equality
  omega

theorem no_single_clearingBackstop_occurrence_carries_all_depths :
    ¬ ∃ occurrence : AnyPeriodicClearingBackstopOccurrence,
      ∀ depth : Nat,
        periodicClearingBackstopOccurrenceAt depth = occurrence := by
  rintro ⟨occurrence, allDepths⟩
  have equality := (allDepths 0).trans (allDepths 1).symm
  have depthEquality :=
    periodicClearingBackstopOccurrenceAt_injective equality
  omega

theorem periodic_clearingBackstop_mouth_has_no_submitted_authority_or_future
    (depth : Nat) : True := by
  let backstop :=
    sourceGeneratedProofCarryingPeriodicClearingBackstopAt depth
  fail_if_success exact backstop.submittedActivation
  fail_if_success exact backstop.submittedAdapter
  fail_if_success exact backstop.submittedEdge
  fail_if_success exact backstop.secondRoot
  fail_if_success exact backstop.secondSettlementOccurrence
  fail_if_success exact backstop.parallelRun
  fail_if_success exact backstop.ledgerCandidate
  fail_if_success exact backstop.eventCandidate
  fail_if_success exact backstop.coveragePremise
  fail_if_success exact backstop.futureSchedule
  fail_if_success exact backstop.completedFuture
  fail_if_success exact backstop.localOccurrenceIsRootOccurrence
  trivial

end
end M14PeriodicClearingBackstopRenewal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicClearingBackstopRenewal.installedClearingBackstopAt
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicClearingBackstopRenewal.sourceGeneratedProofCarryingPeriodicClearingBackstopAt
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicClearingBackstopRenewal.periodic_clearingBackstop_local_activation_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicClearingBackstopRenewal.periodic_clearingBackstop_exact_source_image
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicClearingBackstopRenewal.periodic_clearingBackstop_root_write_and_next_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicClearingBackstopRenewal.periodicClearingBackstopOccurrenceAt_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicClearingBackstopRenewal.no_single_clearingBackstop_occurrence_carries_all_depths
