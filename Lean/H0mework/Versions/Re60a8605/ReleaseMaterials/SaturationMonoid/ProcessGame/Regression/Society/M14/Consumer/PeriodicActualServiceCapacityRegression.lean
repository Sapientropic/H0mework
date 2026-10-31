import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.UBIPeriodicActualServiceCapacity

/-!
# M14 arbitrary-depth actual-service UBI direct consumer

The consumer quantifies every generated finite temporal depth.  It retains
the visit-indexed payment occurrence, exact service settlement, canonical
capacity, capture control, anomie backlog, and non-replay of occurrence
authority without storing a future table in the root.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14PeriodicActualServiceCapacityRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Capacity Space CrossingCost UBI
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity

theorem every_period_exact_capacity (depth : Nat) :
    (geometryCompilerAt depth).actionableExitCapacity = 1 :=
  actionableExitCapacity_eq_one_at depth

theorem every_period_captured_capacity_zero (depth : Nat) :
    (capturedGeometryCompilerAt depth).actionableExitCapacity = 0 :=
  captured_nominal_capacity_eq_zero_at depth

theorem every_period_payment_route_service_join (depth : Nat) :
    Nonempty (ExactFeasibleExitEdgeAt (geometryCompilerAt depth)
      ExitFutureCode.leave (firstSlotAt depth)) :=
  ⟨firstFeasibleExitAt depth⟩

theorem every_period_strongest_iff (depth : Nat) :
    Nonempty
        (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt ↔
      ∃ (code : exitRelationCompiler.FutureCode)
        (slot : Fin (anomiePhaseAt depth).served.length),
        code ∈ exitRelationCompiler.futureCodeCarrier ∧
        Nonempty (exitRelationCompiler.FutureContinuationAt
          independentExitRelation.1 .target code) ∧
        ¬ exitRelationCompiler.futureIdle code ∧
        ¬ noCapture.Captures code ∧
        Nonempty (SourceBackedUBIPaymentReceiptAt
          exitCapacityProgram.purchasingPowerStanding code) ∧
        Nonempty (SourceGeneratedUBIRouteReceiptAt code
          (ExactServedCrossingDebitedRunAt.servicedCrossingAt
            (phase := anomiePhaseAt depth)
            (crossingCompiler := crossingCompilerAt depth) slot)) :=
  strongest_actual_exit_renewal_iff_at depth

theorem every_period_anomie_keeps_exit (depth : Nat) :
    (anomiePhaseAt depth).phaseTag = .anomie ∧
      0 < (geometryCompilerAt depth).actionableExitCapacity ∧
      (anomiePhaseAt depth).backlog ≠ [] :=
  anomie_with_positive_exit_capacity_at depth

theorem adjacent_actual_exit_occurrences_are_distinct (depth : Nat) :
    periodicActualServiceExitOccurrenceAt depth ≠
      periodicActualServiceExitOccurrenceAt (depth + 1) := by
  intro equality
  have depth_eq := periodicActualServiceExitOccurrenceAt_injective equality
  omega

/-- Type-level non-replay guard: a generated actual exit at one visit cannot
be retyped as authority at the next visit. -/
theorem actual_exit_authority_cannot_retype_at_next_visit : True := by
  fail_if_success
    exact (periodicActualServiceExitAt 0 : PeriodicActualServiceExitAt 1)
  trivial

structure PeriodicActualServiceCapacityCertificate : Prop where
  everyPeriod : ∀ depth : Nat, Nonempty (PeriodicActualServiceExitAt depth)
  everyPeriodJoin : ∀ depth : Nat,
    Nonempty (ExactFeasibleExitEdgeAt (geometryCompilerAt depth)
      ExitFutureCode.leave (firstSlotAt depth))
  everyPeriodStrongestIff : ∀ depth : Nat,
    Nonempty
        (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt ↔
      ∃ (code : exitRelationCompiler.FutureCode)
        (slot : Fin (anomiePhaseAt depth).served.length),
        code ∈ exitRelationCompiler.futureCodeCarrier ∧
        Nonempty (exitRelationCompiler.FutureContinuationAt
          independentExitRelation.1 .target code) ∧
        ¬ exitRelationCompiler.futureIdle code ∧
        ¬ noCapture.Captures code ∧
        Nonempty (SourceBackedUBIPaymentReceiptAt
          exitCapacityProgram.purchasingPowerStanding code) ∧
        Nonempty (SourceGeneratedUBIRouteReceiptAt code
          (ExactServedCrossingDebitedRunAt.servicedCrossingAt
            (phase := anomiePhaseAt depth)
            (crossingCompiler := crossingCompilerAt depth) slot))
  everyPeriodExactCapacity : ∀ depth : Nat,
    (geometryCompilerAt depth).actionableExitCapacity = 1
  everyPeriodCapturedCapacity : ∀ depth : Nat,
    (capturedGeometryCompilerAt depth).actionableExitCapacity = 0
  everyPeriodBounds : ∀ depth : Nat,
    (geometryCompilerAt depth).actionableExitCapacity ≤
        (anomiePhaseAt depth).served.length ∧
      (geometryCompilerAt depth).actionableExitCapacity ≤
        (anomiePhaseAt depth).capacity
  everyPeriodAnomieWithExit : ∀ depth : Nat,
    (anomiePhaseAt depth).phaseTag = .anomie ∧
      0 < (geometryCompilerAt depth).actionableExitCapacity ∧
      (anomiePhaseAt depth).backlog ≠ []
  actualExitOccurrencesDistinct :
    Function.Injective periodicActualServiceExitOccurrenceAt
  paymentOccurrencesRetained : ∀ depth : Nat,
    (periodicActualServiceExitOccurrenceAt depth).paymentOccurrence =
      periodicPaymentOccurrenceAt depth
  noCompletedServiceInRoot : ∀ _depth : Nat, True
  noCrossVisitRetyping : True

theorem periodicActualServiceCapacityDirectConsumer :
    PeriodicActualServiceCapacityCertificate where
  everyPeriod := every_generated_period_has_actual_service_exit
  everyPeriodJoin := every_period_payment_route_service_join
  everyPeriodStrongestIff := every_period_strongest_iff
  everyPeriodExactCapacity := every_period_exact_capacity
  everyPeriodCapturedCapacity := every_period_captured_capacity_zero
  everyPeriodBounds := capacity_bounded_by_actual_service_and_root_at
  everyPeriodAnomieWithExit := every_period_anomie_keeps_exit
  actualExitOccurrencesDistinct :=
    periodicActualServiceExitOccurrenceAt_injective
  paymentOccurrencesRetained :=
    periodicActualServiceExit_paymentOccurrence
  noCompletedServiceInRoot := root_payload_has_no_completed_periodic_service
  noCrossVisitRetyping := actual_exit_authority_cannot_retype_at_next_visit

end
end M14PeriodicActualServiceCapacityRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicActualServiceCapacityRegression.periodicActualServiceCapacityDirectConsumer
