import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Route.PeriodicRouteOutageRestoration

/-!
# Independent necessity of the route gate

The existing route-outage actual carrier already fixes the exact root event,
Payment, standing, tenure relation, noncapture, service, selected row, whole
ledger, responsibility consumer, factorization and generated next while the
source route fibre is empty.  This module adds the missing maximal-necessity
seam: every other currently installed renewal coordinate is regenerated at
that same literal root visit, and no function from the complete remaining
carrier can reconstruct the deleted source route.

The sibling faces are dependent fields, not a closed gate enum.  No root,
occurrence, ledger, registry, target route, history or completed future is
accepted by the producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedRouteGateIndependentNecessity

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Settlement Money Renewal UBI Policy
open Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M3ExchangeSettlementPriceRegression
open M9ProofCarryingRenewalInquiryRoot
open M10OccurrenceCapacityDebitedRunFixture
open M11GeneratedSocialSpaceCrossingFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14EssentialAccessRelationFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14SourceRouteOutageRestoration
open M14PeriodicRouteOutageRestoration

/-! ## Same-visit sibling installations -/

def routeNecessityProofCarryingAt (depth : Nat) :
    SourceInstalledRenewalAt jointRecognition (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def routeNecessityUBIAt (depth : Nat) :
    SourceInstalledRenewalAt ubiRecognition (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def routeNecessityRecognitionWitnessAt (depth : Nat) :
    SourceInstalledRenewalAt recognitionWitnessRecognition
      (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def routeNecessityMandateAt (depth : Nat) :
    SourceInstalledRenewalAt mandateRecognition (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def routeNecessityEssentialServiceAt (depth : Nat) :
    SourceInstalledRenewalAt essentialServiceRestorationRecognition
      (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def routeNecessityCommonClearingAt (depth : Nat) :
    SourceInstalledRenewalAt commonClearingRecognition
      (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def routeNecessityClearingBackstopAt (depth : Nat) :
    SourceInstalledRenewalAt clearingBackstopRecognition
      (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def routeNecessitySourceCrossingAt (depth : Nat) : ConcreteCrossing :=
  ExactServedCrossingDebitedRunAt.servicedCrossingAt
    (phase := anomiePhaseAt depth)
    (crossingCompiler := crossingCompilerAt depth)
    (firstSlotAt depth)

/-- Exact source geometry with all canonical axes except the route incidence.
It reuses the same actual settlement and Payment family as the canonical
geometry. -/
def routeNecessitySourceGeometryAt (depth : Nat) :
    SourceOwnedExitGeometryCompilerAt exitCapacityProgram
      (anomiePhaseAt depth) (crossingCompilerAt depth) run
      (serviceCompilerAt depth) (actualSettlementAt depth) where
  PaysForAt := SourceBackedUBIPaymentReceiptAt
  RoutesAt := RouteOutageRoutesAt

theorem routeNecessitySourceCapacity_eq_zero (depth : Nat) :
    (routeNecessitySourceGeometryAt depth).actionableExitCapacity = 0 :=
  (routeNecessitySourceGeometryAt depth).no_route_receipts_no_exit_capacity
    (fun _code _crossing => by
      change IsEmpty PEmpty
      infer_instance)

theorem routeNecessitySourceActionableExit_isEmpty (depth : Nat) :
    IsEmpty
      ((routeNecessitySourceGeometryAt depth
        ).SourceGeneratedActionableExitRenewalAt) := by
  constructor
  intro renewal
  have positive :
      0 < (routeNecessitySourceGeometryAt depth).actionableExitCapacity :=
    (routeNecessitySourceGeometryAt depth)
      |>.capacity_positive_iff_actionableExitRenewal.mpr ⟨renewal⟩
  rw [routeNecessitySourceCapacity_eq_zero] at positive
  exact Nat.not_lt_zero _ positive

abbrev DeletedRouteAuthorityAt (depth : Nat) :=
  RouteOutageRoutesAt ExitFutureCode.leave
    (routeNecessitySourceCrossingAt depth)

/-! ## Full Type-valued countermodel -/

structure SourceGeneratedRouteGateIndependentNecessityAt
    (depth : Nat) : Type 22 where
  private mk ::
  restoration : SourceGeneratedPeriodicRouteOutageRestorationAt depth
  restorationExact : restoration =
    sourceGeneratedPeriodicRouteOutageRestorationAt depth
  proofCarrying : SourceInstalledRenewalAt jointRecognition
    (temporalVisitAt depth)
  proofCarryingExact : proofCarrying = routeNecessityProofCarryingAt depth
  ubi : SourceInstalledRenewalAt ubiRecognition (temporalVisitAt depth)
  ubiExact : ubi = routeNecessityUBIAt depth
  recognitionWitness : SourceInstalledRenewalAt recognitionWitnessRecognition
    (temporalVisitAt depth)
  recognitionWitnessExact : recognitionWitness =
    routeNecessityRecognitionWitnessAt depth
  mandate : SourceInstalledRenewalAt mandateRecognition
    (temporalVisitAt depth)
  mandateExact : mandate = routeNecessityMandateAt depth
  essentialService : SourceInstalledRenewalAt
    essentialServiceRestorationRecognition (temporalVisitAt depth)
  essentialServiceExact : essentialService =
    routeNecessityEssentialServiceAt depth
  commonClearing : SourceInstalledRenewalAt commonClearingRecognition
    (temporalVisitAt depth)
  commonClearingExact : commonClearing =
    routeNecessityCommonClearingAt depth
  clearingBackstop : SourceInstalledRenewalAt clearingBackstopRecognition
    (temporalVisitAt depth)
  clearingBackstopExact : clearingBackstop =
    routeNecessityClearingBackstopAt depth
  sourceRouteDeleted : IsEmpty (DeletedRouteAuthorityAt depth)

/-- Sole producer: `depth` selects an already generated exact occurrence;
neither the deleted route nor the remaining faces are caller premises. -/
def sourceGeneratedRouteGateIndependentNecessityAt
    (depth : Nat) : SourceGeneratedRouteGateIndependentNecessityAt depth :=
  let restoration :=
    sourceGeneratedPeriodicRouteOutageRestorationAt depth
  { restoration := restoration
    restorationExact := rfl
    proofCarrying := routeNecessityProofCarryingAt depth
    proofCarryingExact := rfl
    ubi := routeNecessityUBIAt depth
    ubiExact := rfl
    recognitionWitness := routeNecessityRecognitionWitnessAt depth
    recognitionWitnessExact := rfl
    mandate := routeNecessityMandateAt depth
    mandateExact := rfl
    essentialService := routeNecessityEssentialServiceAt depth
    essentialServiceExact := rfl
    commonClearing := routeNecessityCommonClearingAt depth
    commonClearingExact := rfl
    clearingBackstop := routeNecessityClearingBackstopAt depth
    clearingBackstopExact := rfl
    sourceRouteDeleted := restoration.sourceRouteMissing _ }

namespace SourceGeneratedRouteGateIndependentNecessityAt

variable {depth : Nat}
  (countermodel : SourceGeneratedRouteGateIndependentNecessityAt depth)

include countermodel

/-! ## Remaining actual authority -/

theorem exactRootOccurrence :
    countermodel.restoration.rootOccurrence =
      jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (temporalVisitAt depth) :=
  countermodel.restoration.rootOccurrenceExact

theorem actualPaymentSharesRoot :
    (periodicSourceBackedPaymentAt depth).rootOccurrence =
      countermodel.restoration.rootOccurrence :=
  countermodel.restoration.paymentRootShared

theorem paymentStandingTenureAndServiceRemain :
    essentialAccessRelationCompiler.GeneratedInterestAt
        tenureActor tenureRelation ∧
      tenureActor = Money.exactCounterpartyActor exactResidualActivation ∧
      essentialAccessRelationCompiler.phaseStep tenureRelation = .tenure ∧
      essentialAccessRelationCompiler.RelationRoleAt
        tenureActor tenureRelation .target .tenureProvider ∧
      (¬ noCapture.Captures ExitFutureCode.leave) ∧
      Nonempty (SourceBackedUBIPaymentReceiptAt
        exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave) ∧
      Nonempty (ExactServedCrossingDebitedRunAt
        (anomiePhaseAt depth) debited (serviceCompilerAt depth)) :=
  let restoration := countermodel.restoration
  ⟨SourceGeneratedPeriodicRouteOutageRestorationAt.sourceTenureInterest
      restoration,
    SourceGeneratedPeriodicRouteOutageRestorationAt.sourceTenureActorIsCounterparty
      restoration,
    SourceGeneratedPeriodicRouteOutageRestorationAt.sourceTenurePhase
      restoration,
    SourceGeneratedPeriodicRouteOutageRestorationAt.sourceTenureRole
      restoration,
    SourceGeneratedPeriodicRouteOutageRestorationAt.sourceUncaptured
      restoration,
    ⟨SourceGeneratedPeriodicRouteOutageRestorationAt.sourcePaymentReceipt
      restoration⟩,
    SourceGeneratedPeriodicRouteOutageRestorationAt.actualService
      restoration⟩

theorem rowLedgerConsumerAndNextRemain :
    countermodel.restoration.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      HEq countermodel.restoration.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      HEq countermodel.restoration.installed.payload.successor
        (installedUBIAt depth).payload.successor ∧
      countermodel.restoration.applied.selectedWrite =
        countermodel.restoration.installed.temporalSelectedRow ∧
      (countermodel.restoration.applied.selectedWrite.sourceRow
        ).CommutesWithWorld ∧
      countermodel.restoration.applied.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      countermodel.restoration.installed.RootAnswerAndNextFactorizes ∧
      countermodel.restoration.applied.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) :=
  ⟨countermodel.restoration.sourceEntryExact,
    countermodel.restoration.selectedRowSharedWithUBI,
    countermodel.restoration.successorSharedWithUBI,
    countermodel.restoration.selectedWriteExact,
    countermodel.restoration.selectedWriteCommutes,
    countermodel.restoration.wholeLedgerExact,
    countermodel.restoration.rootFactorization,
    countermodel.restoration.generatedNextExact⟩

theorem everySiblingActiveAtExactOccurrence :
    jointRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current) =
        .inl ⟨countermodel.proofCarrying.active,
          countermodel.proofCarrying.payload⟩ ∧
      ubiRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current) =
        .inl ⟨countermodel.ubi.active, countermodel.ubi.payload⟩ ∧
      recognitionWitnessRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current) =
        .inl ⟨countermodel.recognitionWitness.active,
          countermodel.recognitionWitness.payload⟩ ∧
      mandateRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current) =
        .inl ⟨countermodel.mandate.active, countermodel.mandate.payload⟩ ∧
      essentialServiceRestorationRecognition.law.toProjectionLaw.outcomeAt
          PUnit.unit (jointRoot.emitted (temporalVisitAt depth).current) =
        .inl ⟨countermodel.essentialService.active,
          countermodel.essentialService.payload⟩ ∧
      commonClearingRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current) =
        .inl ⟨countermodel.commonClearing.active,
          countermodel.commonClearing.payload⟩ ∧
      clearingBackstopRecognition.law.toProjectionLaw.outcomeAt PUnit.unit
          (jointRoot.emitted (temporalVisitAt depth).current) =
        .inl ⟨countermodel.clearingBackstop.active,
          countermodel.clearingBackstop.payload⟩ :=
  ⟨countermodel.proofCarrying.componentOutcome_eq_activePayload,
    countermodel.ubi.componentOutcome_eq_activePayload,
    countermodel.recognitionWitness.componentOutcome_eq_activePayload,
    countermodel.mandate.componentOutcome_eq_activePayload,
    countermodel.essentialService.componentOutcome_eq_activePayload,
    countermodel.commonClearing.componentOutcome_eq_activePayload,
    countermodel.clearingBackstop.componentOutcome_eq_activePayload⟩

theorem everySiblingFactorizes :
    countermodel.proofCarrying.RootAnswerAndNextFactorizes ∧
      countermodel.ubi.RootAnswerAndNextFactorizes ∧
      countermodel.recognitionWitness.RootAnswerAndNextFactorizes ∧
      countermodel.mandate.RootAnswerAndNextFactorizes ∧
      countermodel.essentialService.RootAnswerAndNextFactorizes ∧
      countermodel.commonClearing.RootAnswerAndNextFactorizes ∧
      countermodel.clearingBackstop.RootAnswerAndNextFactorizes :=
  ⟨countermodel.proofCarrying.rootAnswerAndNext_factorizes,
    countermodel.ubi.rootAnswerAndNext_factorizes,
    countermodel.recognitionWitness.rootAnswerAndNext_factorizes,
    countermodel.mandate.rootAnswerAndNext_factorizes,
    countermodel.essentialService.rootAnswerAndNext_factorizes,
    countermodel.commonClearing.rootAnswerAndNext_factorizes,
    countermodel.clearingBackstop.rootAnswerAndNext_factorizes⟩

theorem routeProjectionDistinctFromEverySibling :
    jointRouteOutageRestorationProjection ≠
        jointEssentialServiceRestorationProjection ∧
      jointRouteOutageRestorationProjection ≠ jointMandateProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointRecognitionWitnessProjection ∧
      jointRouteOutageRestorationProjection ≠ jointUBIProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointProofCarryingProjection ∧
      jointRouteOutageRestorationProjection ≠ jointInquiryProjection ∧
      jointRouteOutageRestorationProjection ≠ jointFailureProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointCommonClearingProjection ∧
      jointRouteOutageRestorationProjection ≠
        jointClearingBackstopProjection :=
  let distinct :=
    SourceGeneratedPeriodicRouteOutageRestorationAt.routeProjectionDistinctFromExisting
      (SourceGeneratedRouteGateIndependentNecessityAt.restoration countermodel)
  ⟨distinct.1,
    distinct.2.1,
    distinct.2.2.1,
    distinct.2.2.2.1,
    distinct.2.2.2.2.1,
    distinct.2.2.2.2.2.1,
    distinct.2.2.2.2.2.2,
    commonClearing_projection_ne_routeOutage_projection.symm,
    clearingBackstop_projection_ne_routeOutage_projection.symm⟩

omit countermodel in
theorem sourceAndTargetVisitsDistinct :
    temporalVisitAt depth ≠ temporalVisitAt (depth + 1) := by
  intro equality
  have depthEquality := temporalVisitAt_injective equality
  omega

end SourceGeneratedRouteGateIndependentNecessityAt

/-! ## Deleted fibre and no reconstruction -/

theorem deletedRouteAuthority_isEmpty (depth : Nat) :
    IsEmpty (DeletedRouteAuthorityAt depth) :=
  (sourceGeneratedRouteGateIndependentNecessityAt depth).sourceRouteDeleted

theorem remainingAuthorityCannotReconstructDeletedRoute (depth : Nat) :
    IsEmpty
      (SourceGeneratedRouteGateIndependentNecessityAt depth →
        DeletedRouteAuthorityAt depth) :=
  ⟨fun reconstruct =>
    (deletedRouteAuthority_isEmpty depth).false
      (reconstruct (sourceGeneratedRouteGateIndependentNecessityAt depth))⟩

theorem targetRouteReceiptCannotRetypeAsSourceRoute (depth : Nat) : True := by
  let countermodel := sourceGeneratedRouteGateIndependentNecessityAt depth
  fail_if_success exact
    (countermodel.restoration.targetRouteReceipt :
      DeletedRouteAuthorityAt depth)
  fail_if_success exact countermodel.gateKind
  fail_if_success exact countermodel.remainingCoverage
  fail_if_success exact countermodel.target
  fail_if_success exact countermodel.history
  fail_if_success exact countermodel.future
  trivial

end
end M14SourceGeneratedRouteGateIndependentNecessity
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRouteGateIndependentNecessity.sourceGeneratedRouteGateIndependentNecessityAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRouteGateIndependentNecessity.SourceGeneratedRouteGateIndependentNecessityAt.everySiblingActiveAtExactOccurrence
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRouteGateIndependentNecessity.routeNecessitySourceActionableExit_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRouteGateIndependentNecessity.remainingAuthorityCannotReconstructDeletedRoute
