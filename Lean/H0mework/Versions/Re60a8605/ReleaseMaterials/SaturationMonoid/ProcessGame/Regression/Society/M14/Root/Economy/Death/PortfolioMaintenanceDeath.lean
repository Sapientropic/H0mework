import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.Economy.Portfolio.ActionableFuturePortfolio

/-!
# M14 source-generated portfolio-maintenance death

A positive scalar outside option is not enough to keep a multi-domain future
habitable.  The exact one-service source keeps its periodic payment, generated
route, uncaptured tenure action, root factorization, and capacity `1`, while
the compiler-generated health-service fibre and hence the complete dependent
portfolio are empty.

This is a local economic death witness, not a whole-root terminal.  Its sole
producer accepts only the finite temporal depth and computes the exact stable
source.  It accepts no death tag, empty-fibre proof, capacity, occurrence,
image, landing, or terminal candidate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14PortfolioMaintenanceDeath

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal UBI Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M9ProofCarryingRenewalInquiryRoot
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EssentialAccessRelationFixture
open M14EssentialAccessSectorRegression
open M14GeneratedEconomicDisposition
open M14ActionableFuturePortfolio

/-! ## Exact local-death carrier -/

/-- A source-generated maintenance death is indexed by the exact portfolio
source it diagnoses.  Only the one-service source can inhabit the carrier. -/
structure SourceGeneratedPortfolioMaintenanceDeathAt
    (depth : Nat) (source : EssentialPortfolioSourceAt depth) : Type 18 where
  private mk ::
  source_eq : source = stablePortfolioSourceAt depth
  stable : SourceGeneratedStableServiceStateAt depth
  stable_eq : stable = sourceGeneratedStableServiceStateAt depth
  paymentRootExact : stable.paymentOccurrence.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt depth)
  paymentReceipt : Nonempty (SourceBackedUBIPaymentReceiptAt
    exitCapacityProgram.purchasingPowerStanding ExitFutureCode.leave)
  routeReceipt : Nonempty (SourceGeneratedUBIRouteReceiptAt
    ExitFutureCode.leave
      (ExactServedCrossingDebitedRunAt.servicedCrossingAt
        (phase := stablePhaseAt depth)
        (crossingCompiler := crossingCompilerAt depth)
        (stableSlotAt depth)))
  tenureActionable : SourceGeneratedStableEssentialDomainActionableAt
    depth tenureAuthority
  healthServiceEmpty : IsEmpty
    (SourceGeneratedStableDomainServiceIncidenceAt depth
      (exactEssentialAccessSeed .health))
  completePortfolioEmpty : IsEmpty (CompletePortfolioAt depth source)
  uncaptured : ¬ noCapture.Captures ExitFutureCode.leave
  exactCapacity :
    (stableGeometryCompilerAt depth).actionableExitCapacity = 1
  rootFactorization : stable.paymentOccurrence.installed.RootAnswerAndNextFactorizes
  groundedTerminalEmpty : IsEmpty
    (SourceGeneratedGroundedEconomicTerminalAt
      (tenureRepairExposureAt depth) (tenureEconomicImageAt depth) none)
  actualRootSuccessor :
    (jointRoot.toAuthoritativeRoot.toRoot.evolutionAt
      (rootVisitAt depth).current).nextCurrent? =
        some (rootVisitAt depth).current

/-- Sole producer: all evidence is regenerated from the exact finite visit. -/
def portfolioMaintenanceDeathAt (depth : Nat) :
    SourceGeneratedPortfolioMaintenanceDeathAt depth
      (stablePortfolioSourceAt depth) :=
  let stable := sourceGeneratedStableServiceStateAt depth
  { source_eq := rfl
    stable := stable
    stable_eq := rfl
    paymentRootExact := stable.paymentOccurrence.rootOccurrence_eq
    paymentReceipt := ⟨stable.paymentOccurrence.paymentReceipt⟩
    routeReceipt :=
      ⟨SourceGeneratedUBIRouteReceiptAt.generate _⟩
    tenureActionable := stable.tenureActionable
    healthServiceEmpty := stable.healthServiceUnavailable
    completePortfolioEmpty := stableSource_completePortfolio_isEmpty depth
    uncaptured := by simp [noCapture]
    exactCapacity := stable.exactCapacity
    rootFactorization := stable.paymentOccurrence.rootFactorization
    groundedTerminalEmpty := fixedGroundedEconomicTerminal_isEmpty depth
    actualRootSuccessor := fixedRoot_has_actual_successor depth }

theorem every_generated_period_has_maintenance_death (depth : Nat) :
    Nonempty (SourceGeneratedPortfolioMaintenanceDeathAt depth
      (stablePortfolioSourceAt depth)) :=
  ⟨portfolioMaintenanceDeathAt depth⟩

/-! ## Exact-source negatives -/

/-- A full tenure/health source cannot be re-labelled as maintenance death. -/
instance fullSource_maintenanceDeath_isEmpty (depth : Nat) :
    IsEmpty (SourceGeneratedPortfolioMaintenanceDeathAt depth
      (fullPortfolioSourceAt depth)) :=
  ⟨fun death => full_stable_sources_distinct depth death.source_eq⟩

theorem full_source_cannot_generate_maintenance_death (depth : Nat) :
    IsEmpty (SourceGeneratedPortfolioMaintenanceDeathAt depth
      (fullPortfolioSourceAt depth)) :=
  fullSource_maintenanceDeath_isEmpty depth

/-! ## Honest next-visit restoration transporter -/

/-- The existing finite root history transports the missing-domain source to
the next visit's full source-generated portfolio.  This carrier establishes
the exact restoration responsibility and target; it is deliberately not an
action-bearing root update. -/
structure SourceGeneratedMaintenanceRestorationTransportAt
    {depth : Nat}
    (death : SourceGeneratedPortfolioMaintenanceDeathAt depth
      (stablePortfolioSourceAt depth)) : Type 18 where
  private mk ::
  targetPortfolio : SourceGeneratedActionableFuturePortfolioAt (depth + 1)
  targetPortfolio_eq : targetPortfolio =
    sourceGeneratedActionableFuturePortfolioAt (depth + 1)
  targetHealthLive : SourceGeneratedEssentialDomainActionableAt
    (depth + 1) healthAuthority
  sourcePortfolioEmpty : IsEmpty
    (CompletePortfolioAt depth (stablePortfolioSourceAt depth))
  targetPortfolioLive : Nonempty
    (CompletePortfolioAt (depth + 1)
      (fullPortfolioSourceAt (depth + 1)))
  sourceTargetPrefixesDistinct :
    stablePrefixAt depth ≠ anomiePrefixAt depth
  adjacentVisitsDistinct : temporalVisitAt depth ≠ temporalVisitAt (depth + 1)
  adjacentPaymentOccurrencesDistinct :
    periodicPaymentOccurrenceAt depth ≠
      periodicPaymentOccurrenceAt (depth + 1)
  targetPaymentRootExact : targetPortfolio.paymentOccurrence.rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt (depth + 1))
  generatedNextVisitExact :
    (periodicUBISourceAt depth).generatedNext.visit =
      temporalVisitAt (depth + 1)
  sourceCapacityStillPositive :
    (stableGeometryCompilerAt depth).actionableExitCapacity = 1
  targetCapacityPositive :
    (geometryCompilerAt (depth + 1)).actionableExitCapacity = 1

def maintenanceRestorationTransportAt {depth : Nat}
    (death : SourceGeneratedPortfolioMaintenanceDeathAt depth
      (stablePortfolioSourceAt depth)) :
    SourceGeneratedMaintenanceRestorationTransportAt death :=
  let target := sourceGeneratedActionableFuturePortfolioAt (depth + 1)
  { targetPortfolio := target
    targetPortfolio_eq := rfl
    targetHealthLive := target.actionable healthAuthority
    sourcePortfolioEmpty := stableSource_completePortfolio_isEmpty depth
    targetPortfolioLive :=
      every_generated_period_has_actionable_future_portfolio (depth + 1)
    sourceTargetPrefixesDistinct := stable_anomie_prefixes_distinct depth
    adjacentVisitsDistinct := adjacent_periods_are_distinct depth
    adjacentPaymentOccurrencesDistinct :=
      adjacent_payment_occurrences_are_distinct depth
    targetPaymentRootExact := target.rootOccurrenceExact
    generatedNextVisitExact := rfl
    sourceCapacityStillPositive := death.exactCapacity
    targetCapacityPositive := actionableExitCapacity_eq_one_at (depth + 1) }

theorem every_maintenance_death_generates_restoration_transport
    (depth : Nat) :
    Nonempty (SourceGeneratedMaintenanceRestorationTransportAt
      (depth := depth) (portfolioMaintenanceDeathAt depth)) :=
  ⟨maintenanceRestorationTransportAt
    (depth := depth) (portfolioMaintenanceDeathAt depth)⟩

/-! The transporter is intentionally silent about an action-bearing service
maintenance disposition.  That missing pre-emitter action is the generated
next construction responsibility, not a premise hidden in this carrier. -/

end
end M14PortfolioMaintenanceDeath
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14PortfolioMaintenanceDeath.portfolioMaintenanceDeathAt
#print axioms SaturationMonoid.ProcessGame.Society.M14PortfolioMaintenanceDeath.full_source_cannot_generate_maintenance_death
#print axioms SaturationMonoid.ProcessGame.Society.M14PortfolioMaintenanceDeath.every_maintenance_death_generates_restoration_transport
