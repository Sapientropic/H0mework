import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Portfolio.ActionableFuturePortfolio
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Identification.ZeroCapacityCausalNonidentifiabilityRegression

/-!
# M14 proof-carrying actionable-future portfolio consumer

The full tenure/health dependent portfolio is generated at every finite root
visit and strengthens the existing visit-one viable economic disposition.
The scalar exit-capacity readout cannot reconstruct portfolio completeness.
The full tenure/health source and the inhabited one-service source share the
exact root, payment, route, and the same tenure/health domain authority.  Their
exact queue prefixes differ (`cut = 3` versus `cut = 1`) while both matching
capacities equal `1`; health is an actual served occurrence only in the first.

Payment-missing, route-missing, full-capture, and no-actual-service controls
prevent nominal money or a vacuous dependent product from manufacturing a
portfolio.  Service occurrence identity is the dependent service ordinal;
the underlying repeated lifecycle event value is deliberately not claimed to
be distinct.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingActionableFuturePortfolioRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Settlement Money UBI Renewal Capacity
open Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M10OccurrenceCapacityProcessFixture
open M10OccurrenceCapacityDebitedRunFixture
open M11GeneratedSocialSpaceCrossingFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14CaptureResponsibilityDispositionRegression
open M14ZeroCapacityCausalNonidentifiabilityRegression
open M14GeneratedEconomicDisposition
open M14ActionableFuturePortfolio

/-! ## Strict domain, slot, crossing, and dependent-service identity -/

theorem portfolio_domains_are_source_distinct :
    tenureAuthority ≠ healthAuthority :=
  tenure_and_health_authorities_distinct

theorem portfolio_domain_actors_are_distinct :
    domainActor tenureAuthority ≠ domainActor healthAuthority :=
  tenure_health_actors_ne

theorem portfolio_domain_relations_are_distinct :
    domainRelation tenureAuthority ≠ domainRelation healthAuthority :=
  tenure_health_relations_ne

theorem portfolio_domain_phases_are_distinct :
    domainPhase tenureAuthority ≠ domainPhase healthAuthority :=
  tenure_health_phases_ne

theorem tenure_health_slots_are_distinct (depth : Nat) :
    domainSlotAt depth tenureAuthority ≠
      domainSlotAt depth healthAuthority := by
  intro equality
  have values := congrArg Fin.val equality
  change (0 : Nat) = 1 at values
  omega

@[simp] theorem tenure_domain_crossing_eq_first (depth : Nat) :
    domainCrossingAt depth tenureAuthority = firstCrossing :=
  rfl

@[simp] theorem health_domain_crossing_eq_middle (depth : Nat) :
    domainCrossingAt depth healthAuthority = middleCrossing :=
  rfl

theorem tenure_health_crossings_are_distinct (depth : Nat) :
    domainCrossingAt depth tenureAuthority ≠
      domainCrossingAt depth healthAuthority := by
  rw [tenure_domain_crossing_eq_first, health_domain_crossing_eq_middle]
  exact SourceOwnedCrossingCompiler.ExactCrossing.ne_of_position_ne
    first_middle_positions_are_distinct

/-- Service identity is the ordinal-indexed dependent occurrence. -/
abbrev DomainServiceOccurrenceAt (depth : Nat) :=
  Sigma fun slot : Fin (anomiePhaseAt depth).served.length =>
    (serviceCompilerAt depth).ServesAt
      ((anomiePhaseAt depth).served.get slot)
      (run.events.get
        (Fin.cast (actualSettlementAt depth).eventsLength_eq_allocated.symm
          slot))

def domainServiceOccurrenceAt (depth : Nat)
    (domain : EssentialAccessRelationAuthority) :
    DomainServiceOccurrenceAt depth :=
  ⟨domainSlotAt depth domain, domainServiceReceiptAt depth domain⟩

theorem tenure_health_service_occurrences_are_distinct (depth : Nat) :
    domainServiceOccurrenceAt depth tenureAuthority ≠
      domainServiceOccurrenceAt depth healthAuthority := by
  intro equality
  exact tenure_health_slots_are_distinct depth
    (congrArg Sigma.fst equality)

/-! ## Two inhabited sources, one capacity, different completeness -/

def fullPortfolioCapacityAt (depth : Nat) : Nat :=
  (geometryCompilerAt depth).actionableExitCapacity

def stablePortfolioCapacityAt (depth : Nat) : Nat :=
  portfolioCapacityReadoutAt depth (stablePortfolioSourceAt depth)

@[simp] theorem fullPortfolioCapacity_eq_one (depth : Nat) :
    fullPortfolioCapacityAt depth = 1 :=
  actionableExitCapacity_eq_one_at depth

@[simp] theorem stablePortfolioCapacityReadout_eq_one (depth : Nat) :
    stablePortfolioCapacityAt depth = 1 :=
  stablePortfolioCapacity_eq_one depth

@[simp] theorem full_stable_capacity_readouts_equal (depth : Nat) :
    fullPortfolioCapacityAt depth = stablePortfolioCapacityAt depth := by
  rw [fullPortfolioCapacity_eq_one, stablePortfolioCapacityReadout_eq_one]

theorem full_and_stable_are_inhabited_sources
    (depth : Nat) :
    Nonempty (SourceGeneratedActionableFuturePortfolioAt depth) ∧
      Nonempty (SourceGeneratedStableServiceStateAt depth) ∧
      IsEmpty (CompletePortfolioAt depth
        (stablePortfolioSourceAt depth)) ∧
      stablePrefixAt depth ≠ anomiePrefixAt depth ∧
      fullPortfolioSourceAt depth ≠ stablePortfolioSourceAt depth ∧
      fullPortfolioCapacityAt depth = 1 ∧
      stablePortfolioCapacityAt depth = 1 :=
  ⟨every_generated_period_has_actionable_future_portfolio depth,
    ⟨sourceGeneratedStableServiceStateAt depth⟩,
    stableSource_completePortfolio_isEmpty depth,
    stable_anomie_prefixes_distinct depth,
    full_stable_sources_distinct depth,
    fullPortfolioCapacity_eq_one depth,
    stablePortfolioCapacityReadout_eq_one depth⟩

theorem full_stable_same_root_payment_route_different_health_fibre
    (depth : Nat) :
    let full := sourceGeneratedActionableFuturePortfolioAt depth
    let stable := sourceGeneratedStableServiceStateAt depth
    full.paymentOccurrence = stable.paymentOccurrence ∧
      full.paymentOccurrence.rootOccurrence =
        stable.paymentOccurrence.rootOccurrence ∧
      (geometryCompilerAt depth).PaysForAt =
        (stableGeometryCompilerAt depth).PaysForAt ∧
      (geometryCompilerAt depth).RoutesAt =
        (stableGeometryCompilerAt depth).RoutesAt ∧
      Nonempty (SourceGeneratedEssentialDomainActionableAt
        depth healthAuthority) ∧
      Nonempty (SourceGeneratedStableEssentialDomainActionableAt
        depth tenureAuthority) ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      stablePrefixAt depth ≠ anomiePrefixAt depth ∧
      (geometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1 :=
  ⟨rfl, rfl, rfl, rfl,
    ⟨sourceGeneratedEssentialDomainActionableAt depth healthAuthority⟩,
    ⟨sourceGeneratedStableTenureActionableAt depth⟩,
    stableHealthDomainServiceIncidence_isEmpty depth,
    stable_anomie_prefixes_distinct depth,
    actionableExitCapacity_eq_one_at depth,
    stablePortfolioCapacity_eq_one depth⟩

theorem portfolioCapacityReadout_not_injective (depth : Nat) :
    ¬ Function.Injective (portfolioCapacityReadoutAt depth) := by
  intro injective
  exact full_stable_sources_distinct depth
    (injective (full_stable_capacity_readouts_equal depth))

theorem no_scalar_capacity_reconstructs_portfolio_source
    (depth : Nat) :
    ¬ ∃ reconstruct : Nat → EssentialPortfolioSourceAt depth,
      Function.LeftInverse reconstruct (portfolioCapacityReadoutAt depth) := by
  rintro ⟨reconstruct, leftInverse⟩
  apply full_stable_sources_distinct depth
  calc
    fullPortfolioSourceAt depth =
        reconstruct (portfolioCapacityReadoutAt depth
          (fullPortfolioSourceAt depth)) :=
      (leftInverse (fullPortfolioSourceAt depth)).symm
    _ = reconstruct (portfolioCapacityReadoutAt depth
          (stablePortfolioSourceAt depth)) := by
      apply congrArg reconstruct
      change (geometryCompilerAt depth).actionableExitCapacity =
        (stableGeometryCompilerAt depth).actionableExitCapacity
      rw [actionableExitCapacity_eq_one_at,
        stablePortfolioCapacity_eq_one]
    _ = stablePortfolioSourceAt depth :=
      leftInverse (stablePortfolioSourceAt depth)

/-- No scalar observer can classify both portfolio fibres exactly. -/
theorem no_scalar_capacity_reconstructs_portfolio_completeness
    (depth : Nat) :
    ¬ ∃ complete : Nat → Prop,
      (complete (fullPortfolioCapacityAt depth) ↔
        Nonempty (CompletePortfolioAt depth (fullPortfolioSourceAt depth))) ∧
      (complete (stablePortfolioCapacityAt depth) ↔
        Nonempty (CompletePortfolioAt depth
          (stablePortfolioSourceAt depth))) := by
  rintro ⟨complete, fullExact, stableExact⟩
  have fullVisible : complete (fullPortfolioCapacityAt depth) :=
    fullExact.mpr
      (every_generated_period_has_actionable_future_portfolio depth)
  have stableVisible : complete (stablePortfolioCapacityAt depth) := by
    simpa using fullVisible
  rcases stableExact.mp stableVisible with ⟨portfolio⟩
  exact (stableSource_completePortfolio_isEmpty depth).false portfolio

/-! ## Missing-axis controls -/

abbrev PaymentMissingDomainActionableAt
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :=
  ExactFeasibleExitEdgeAt (paymentIncidenceMissingGeometryAt depth)
    ExitFutureCode.leave (domainSlotAt depth domain)

abbrev PaymentMissingPortfolioAt (depth : Nat) :=
  (domain : EssentialAccessRelationAuthority) →
    PaymentMissingDomainActionableAt depth domain

instance paymentMissingPortfolio_isEmpty (depth : Nat) :
    IsEmpty (PaymentMissingPortfolioAt depth) :=
  ⟨fun portfolio =>
    (payment_incidence_missing_at depth ExitFutureCode.leave).false
      (portfolio tenureAuthority).paymentReceipt⟩

abbrev RouteMissingDomainActionableAt
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :=
  ExactFeasibleExitEdgeAt (routeIncidenceMissingGeometryAt depth)
    ExitFutureCode.leave (domainSlotAt depth domain)

abbrev RouteMissingPortfolioAt (depth : Nat) :=
  (domain : EssentialAccessRelationAuthority) →
    RouteMissingDomainActionableAt depth domain

instance routeMissingPortfolio_isEmpty (depth : Nat) :
    IsEmpty (RouteMissingPortfolioAt depth) :=
  ⟨fun portfolio =>
    (route_incidence_missing_at depth ExitFutureCode.leave
      (domainCrossingAt depth tenureAuthority)).false
      (portfolio tenureAuthority).routeReceipt⟩

abbrev CapturedDomainActionableAt
    (depth : Nat) (domain : EssentialAccessRelationAuthority) :=
  ExactFeasibleExitEdgeAt (capturedGeometryCompilerAt depth)
    ExitFutureCode.leave (domainSlotAt depth domain)

abbrev CapturedPortfolioAt (depth : Nat) :=
  (domain : EssentialAccessRelationAuthority) →
    CapturedDomainActionableAt depth domain

instance capturedPortfolio_isEmpty (depth : Nat) :
    IsEmpty (CapturedPortfolioAt depth) :=
  ⟨fun portfolio => by
    let edge := portfolio tenureAuthority
    have noExit : IsEmpty capturedProgram.exitCone.ActionableExitAt :=
      capturedProgram.exitCone.isEmpty_actionableExit_iff_fullPriceCapture.mpr
        capturedProgram_fullPriceCapture
    exact noExit.false ⟨ExitFutureCode.leave, edge.codeSurvives⟩⟩

/-- A cash-only source keeps payment and route laws but has no actual service
receipt at any ordinal. -/
def noServiceCompilerAt (depth : Nat) :
    SourceOwnedOccurrenceServiceCompiler
      (installedCompilerAt depth) M10OccurrenceCapacityDebitedRunFixture.P where
  ServesAt := fun _unit _event => PEmpty

abbrev NoServiceSettlementAt (depth : Nat) :=
  ExactServedCrossingDebitedRunAt (anomiePhaseAt depth)
    debited (noServiceCompilerAt depth)

instance noServiceSettlement_isEmpty (depth : Nat) :
    IsEmpty (NoServiceSettlementAt depth) :=
  ⟨fun settlement => nomatch settlement.serviceAt (firstSlotAt depth)⟩

theorem payment_and_route_live_without_actual_service (depth : Nat) :
    Nonempty (PeriodicSourceBackedPaymentAt depth) ∧
      Nonempty (SourceBackedUBIPaymentReceiptAt
      exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave) ∧
      Nonempty (SourceGeneratedUBIRouteReceiptAt ExitFutureCode.leave
        (domainCrossingAt depth tenureAuthority)) ∧
      IsEmpty (NoServiceSettlementAt depth) :=
  ⟨⟨periodicSourceBackedPaymentAt depth⟩,
    ⟨SourceBackedUBIPaymentReceiptAt.generate⟩,
    ⟨SourceGeneratedUBIRouteReceiptAt.generate _⟩,
    noServiceSettlement_isEmpty depth⟩

theorem service_and_route_live_without_payment (depth : Nat) :
    Nonempty (PeriodicSourceBackedPaymentAt depth) ∧
      Nonempty (ExactServedCrossingDebitedRunAt (anomiePhaseAt depth)
      debited (serviceCompilerAt depth)) ∧
      Nonempty ((paymentIncidenceMissingGeometryAt depth).RoutesAt
        ExitFutureCode.leave (domainCrossingAt depth tenureAuthority)) ∧
      IsEmpty (PaymentMissingPortfolioAt depth) :=
  ⟨⟨periodicSourceBackedPaymentAt depth⟩,
    ⟨actualSettlementAt depth⟩,
    ⟨SourceGeneratedUBIRouteReceiptAt.generate _⟩,
    paymentMissingPortfolio_isEmpty depth⟩

theorem payment_and_service_live_without_route (depth : Nat) :
    Nonempty (PeriodicSourceBackedPaymentAt depth) ∧
      Nonempty ((routeIncidenceMissingGeometryAt depth).PaysForAt
      exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave) ∧
      Nonempty (ExactServedCrossingDebitedRunAt (anomiePhaseAt depth)
        debited (serviceCompilerAt depth)) ∧
      IsEmpty (RouteMissingPortfolioAt depth) :=
  ⟨⟨periodicSourceBackedPaymentAt depth⟩,
    ⟨SourceBackedUBIPaymentReceiptAt.generate⟩,
    ⟨actualSettlementAt depth⟩,
    routeMissingPortfolio_isEmpty depth⟩

theorem payment_route_service_live_under_capture_but_portfolio_empty
    (depth : Nat) :
    Nonempty (PeriodicSourceBackedPaymentAt depth) ∧
      fullCapture.Captures ExitFutureCode.leave ∧
      Nonempty ((capturedGeometryCompilerAt depth).PaysForAt
      capturedProgram.purchasingPowerStanding ExitFutureCode.leave) ∧
      Nonempty ((capturedGeometryCompilerAt depth).RoutesAt
        ExitFutureCode.leave (domainCrossingAt depth tenureAuthority)) ∧
      Nonempty (ExactServedCrossingDebitedRunAt (anomiePhaseAt depth)
        debited (serviceCompilerAt depth)) ∧
      IsEmpty (CapturedPortfolioAt depth) :=
  ⟨⟨periodicSourceBackedPaymentAt depth⟩,
    leave_is_captured,
    ⟨SourceBackedUBIPaymentReceiptAt.generate⟩,
    ⟨SourceGeneratedUBIRouteReceiptAt.generate _⟩,
    ⟨actualSettlementAt depth⟩,
    capturedPortfolio_isEmpty depth⟩

/-! ## Direct whole-program certificate -/

structure ProofCarryingActionableFuturePortfolioCertificate : Prop where
  everyDepth : ∀ depth : Nat,
    Nonempty (SourceGeneratedActionableFuturePortfolioAt depth)
  fixedPortfolioViable : Nonempty
    (SourceGeneratedPortfolioViableEconomicDispositionAt
      postRepairViableExposure postRepairViableImage
        (ordinaryEconomicLandingAt 0))
  portfolioPaymentIsViablePayment :
    fixedPortfolioViableEconomicDisposition.portfolio.paymentOccurrence =
      fixedPortfolioViableEconomicDisposition.viable.actualExit.paymentOccurrence
  portfolioViableRootEvent :
    postRepairViableExposure.root.erasedRootEvent =
      ⟨temporalVisitAt 1,
        fixedPortfolioViableEconomicDisposition.portfolio
          |>.paymentOccurrence |>.rootOccurrence⟩
  portfolioViableImage :
    postRepairViableImage =
      M14EconomicSingleFold.economicImage postRepairViableExposure
  domainAuthorityDistinct : tenureAuthority ≠ healthAuthority
  domainActorDistinct : domainActor tenureAuthority ≠ domainActor healthAuthority
  domainRelationDistinct :
    domainRelation tenureAuthority ≠ domainRelation healthAuthority
  domainPhaseDistinct : domainPhase tenureAuthority ≠ domainPhase healthAuthority
  everyDepthSlotsDistinct : ∀ depth,
    domainSlotAt depth tenureAuthority ≠ domainSlotAt depth healthAuthority
  everyDepthTenureSlotGenerated : ∀ depth
      (incidence : SourceGeneratedEssentialDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .tenure)),
    incidence.slot = tenureSlotAt depth
  everyDepthHealthSlotGenerated : ∀ depth
      (incidence : SourceGeneratedEssentialDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)),
    incidence.slot = healthSlotAt depth
  everyDepthCrossingsDistinct : ∀ depth,
    domainCrossingAt depth tenureAuthority ≠
      domainCrossingAt depth healthAuthority
  everyDepthServiceOccurrencesDistinct : ∀ depth,
    domainServiceOccurrenceAt depth tenureAuthority ≠
      domainServiceOccurrenceAt depth healthAuthority
  everyDepthSourcePrefixesDistinct : ∀ depth,
    stablePrefixAt depth ≠ anomiePrefixAt depth
  sameRootPaymentRouteDifferentHealthFibre : ∀ depth,
    let full := sourceGeneratedActionableFuturePortfolioAt depth
    let stable := sourceGeneratedStableServiceStateAt depth
    full.paymentOccurrence = stable.paymentOccurrence ∧
      full.paymentOccurrence.rootOccurrence =
        stable.paymentOccurrence.rootOccurrence ∧
      (geometryCompilerAt depth).PaysForAt =
        (stableGeometryCompilerAt depth).PaysForAt ∧
      (geometryCompilerAt depth).RoutesAt =
        (stableGeometryCompilerAt depth).RoutesAt ∧
      Nonempty (SourceGeneratedEssentialDomainActionableAt
        depth healthAuthority) ∧
      Nonempty (SourceGeneratedStableEssentialDomainActionableAt
        depth tenureAuthority) ∧
      IsEmpty (SourceGeneratedStableDomainServiceIncidenceAt depth
        (exactEssentialAccessSeed .health)) ∧
      stablePrefixAt depth ≠ anomiePrefixAt depth ∧
      (geometryCompilerAt depth).actionableExitCapacity = 1 ∧
      (stableGeometryCompilerAt depth).actionableExitCapacity = 1
  sameScalarDifferentCompleteness : ∀ depth,
    Nonempty (SourceGeneratedActionableFuturePortfolioAt depth) ∧
      Nonempty (SourceGeneratedStableServiceStateAt depth) ∧
      IsEmpty (CompletePortfolioAt depth
        (stablePortfolioSourceAt depth)) ∧
      stablePrefixAt depth ≠ anomiePrefixAt depth ∧
      fullPortfolioSourceAt depth ≠ stablePortfolioSourceAt depth ∧
      fullPortfolioCapacityAt depth = 1 ∧
      stablePortfolioCapacityAt depth = 1
  scalarSourceReadoutNoninjective : ∀ depth,
    ¬ Function.Injective (portfolioCapacityReadoutAt depth)
  scalarCannotReconstructSource : ∀ depth,
    ¬ ∃ reconstruct : Nat → EssentialPortfolioSourceAt depth,
      Function.LeftInverse reconstruct (portfolioCapacityReadoutAt depth)
  scalarCannotReconstructCompleteness : ∀ depth,
    ¬ ∃ complete : Nat → Prop,
      (complete (fullPortfolioCapacityAt depth) ↔
        Nonempty (CompletePortfolioAt depth (fullPortfolioSourceAt depth))) ∧
      (complete (stablePortfolioCapacityAt depth) ↔
        Nonempty (CompletePortfolioAt depth
          (stablePortfolioSourceAt depth)))
  everyDepthPaymentMissing : ∀ depth, IsEmpty (PaymentMissingPortfolioAt depth)
  everyDepthRouteMissing : ∀ depth, IsEmpty (RouteMissingPortfolioAt depth)
  everyDepthCaptured : ∀ depth, IsEmpty (CapturedPortfolioAt depth)
  everyDepthNoService : ∀ depth, IsEmpty (NoServiceSettlementAt depth)
  cashOnlyNoServiceControl : ∀ depth,
    Nonempty (PeriodicSourceBackedPaymentAt depth) ∧
      Nonempty (SourceBackedUBIPaymentReceiptAt
        exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave) ∧
      Nonempty (SourceGeneratedUBIRouteReceiptAt ExitFutureCode.leave
        (domainCrossingAt depth tenureAuthority)) ∧
      IsEmpty (NoServiceSettlementAt depth)
  serviceRouteNoPaymentControl : ∀ depth,
    Nonempty (PeriodicSourceBackedPaymentAt depth) ∧
      Nonempty (ExactServedCrossingDebitedRunAt (anomiePhaseAt depth)
        debited (serviceCompilerAt depth)) ∧
      Nonempty ((paymentIncidenceMissingGeometryAt depth).RoutesAt
        ExitFutureCode.leave (domainCrossingAt depth tenureAuthority)) ∧
      IsEmpty (PaymentMissingPortfolioAt depth)
  paymentServiceNoRouteControl : ∀ depth,
    Nonempty (PeriodicSourceBackedPaymentAt depth) ∧
      Nonempty ((routeIncidenceMissingGeometryAt depth).PaysForAt
        exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave) ∧
      Nonempty (ExactServedCrossingDebitedRunAt (anomiePhaseAt depth)
        debited (serviceCompilerAt depth)) ∧
      IsEmpty (RouteMissingPortfolioAt depth)
  captureControl : ∀ depth,
    Nonempty (PeriodicSourceBackedPaymentAt depth) ∧
      fullCapture.Captures ExitFutureCode.leave ∧
      Nonempty ((capturedGeometryCompilerAt depth).PaysForAt
        capturedProgram.purchasingPowerStanding ExitFutureCode.leave) ∧
      Nonempty ((capturedGeometryCompilerAt depth).RoutesAt
        ExitFutureCode.leave (domainCrossingAt depth tenureAuthority)) ∧
      Nonempty (ExactServedCrossingDebitedRunAt (anomiePhaseAt depth)
        debited (serviceCompilerAt depth)) ∧
      IsEmpty (CapturedPortfolioAt depth)

theorem proofCarryingActionableFuturePortfolioDirectConsumer :
    ProofCarryingActionableFuturePortfolioCertificate where
  everyDepth := every_generated_period_has_actionable_future_portfolio
  fixedPortfolioViable := ⟨fixedPortfolioViableEconomicDisposition⟩
  portfolioPaymentIsViablePayment :=
    fixedPortfolioViable_paymentOccurrence_eq
  portfolioViableRootEvent :=
    fixedPortfolioViable_rootEvent
  portfolioViableImage :=
    fixedPortfolioViableEconomicDisposition.sameImage
  domainAuthorityDistinct := portfolio_domains_are_source_distinct
  domainActorDistinct := portfolio_domain_actors_are_distinct
  domainRelationDistinct := portfolio_domain_relations_are_distinct
  domainPhaseDistinct := portfolio_domain_phases_are_distinct
  everyDepthSlotsDistinct := tenure_health_slots_are_distinct
  everyDepthTenureSlotGenerated := tenureDomainService_slot_eq
  everyDepthHealthSlotGenerated := healthDomainService_slot_eq
  everyDepthCrossingsDistinct := tenure_health_crossings_are_distinct
  everyDepthServiceOccurrencesDistinct :=
    tenure_health_service_occurrences_are_distinct
  everyDepthSourcePrefixesDistinct := stable_anomie_prefixes_distinct
  sameRootPaymentRouteDifferentHealthFibre :=
    full_stable_same_root_payment_route_different_health_fibre
  sameScalarDifferentCompleteness :=
    full_and_stable_are_inhabited_sources
  scalarSourceReadoutNoninjective := portfolioCapacityReadout_not_injective
  scalarCannotReconstructSource :=
    no_scalar_capacity_reconstructs_portfolio_source
  scalarCannotReconstructCompleteness :=
    no_scalar_capacity_reconstructs_portfolio_completeness
  everyDepthPaymentMissing := paymentMissingPortfolio_isEmpty
  everyDepthRouteMissing := routeMissingPortfolio_isEmpty
  everyDepthCaptured := capturedPortfolio_isEmpty
  everyDepthNoService := noServiceSettlement_isEmpty
  cashOnlyNoServiceControl := payment_and_route_live_without_actual_service
  serviceRouteNoPaymentControl := service_and_route_live_without_payment
  paymentServiceNoRouteControl := payment_and_service_live_without_route
  captureControl :=
    payment_route_service_live_under_capture_but_portfolio_empty

end
end M14ProofCarryingActionableFuturePortfolioRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActionableFuturePortfolioRegression.no_scalar_capacity_reconstructs_portfolio_completeness
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingActionableFuturePortfolioRegression.proofCarryingActionableFuturePortfolioDirectConsumer
