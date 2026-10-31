/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.OccurrenceCapacityDebitConsumerRegression
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M11.BoundaryMaintenanceRegression
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Space.CrossingCostPhase

/-!
# M11 actual-service boundary failure regression

The anomie prefix is paired with the existing two-event `NativeDebitedRun` and
two ordinal service receipts.  Thus `residualSettled` is read from actual
lifecycle events, not inferred from capacity allocation.  The same installed
M11 boundary-maintenance root then generates the sole canonical
`FailingBoundaryLineageAt`; no sibling failure carrier is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M11BoundaryFailureRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Capacity Space CrossingCost
open M10OccurrenceCapacityProcessFixture
open M10OccurrenceCapacityDebitedRunFixture
open M10OccurrenceCapacityDebitConsumerRegression

/-! ## Same installed boundary root, sole canonical failure carrier -/

@[simp] theorem maintenance_phaseQueue_length :
    M11BoundaryMaintenanceRegression.maintenance.phaseRateCompiler.queue.length = 3 := by
  rfl

def maintenanceAnomiePrefix : SourceGeneratedExactQueuePrefixAt
    M11BoundaryMaintenanceRegression.maintenance.phaseRateCompiler :=
  SourceGeneratedExactQueuePrefixAt.generate
    M11BoundaryMaintenanceRegression.maintenance.phaseRateCompiler
    ⟨3, by rw [maintenance_phaseQueue_length]; decide⟩

def maintenanceAnomiePhase : SourceGeneratedOccurrenceCapacityPhaseAt
    M11BoundaryMaintenanceRegression.installedRenewal
    M11BoundaryMaintenanceRegression.maintenance.phaseRateCompiler
    maintenanceAnomiePrefix :=
  SourceGeneratedOccurrenceCapacityPhaseAt.generate
    M11BoundaryMaintenanceRegression.installedRenewal
    M11BoundaryMaintenanceRegression.maintenance.phaseRateCompiler
    maintenanceAnomiePrefix

@[simp] theorem maintenance_anomie_tag :
    maintenanceAnomiePhase.phaseTag = .anomie :=
  rfl

/-- Every exact unit in this installed phase is classified by the same
pre-emitter boundary source. -/
theorem exactBoundarySaturation : ExactBoundarySaturatedPhaseAt
    M11BoundaryMaintenanceRegression.maintenance maintenanceAnomiePhase where
  classifies := by
    intro unit unit_mem
    refine ⟨unit, HEq.rfl, ?_⟩
    cases classified : M11BoundaryMaintenanceRegression.maintenanceCrossingCompiler.boundaryCertificate?
        (M11BoundaryMaintenanceRegression.maintenanceCrossingCompiler.exactCrossingOf unit) with
    | none =>
        simp [SourceOwnedCrossingCompiler.boundaryCertificate?,
          M11BoundaryMaintenanceRegression.maintenanceCrossingCompiler,
          M11GeneratedSocialSpaceCrossingFixture.crossingCompiler]
          at classified
    | some certificate =>
        exact ⟨certificate, classified⟩

/-- Canonical root-specialized failing lineage; this is the only M11 failure
authority carrier. -/
theorem canonicalFailingBoundary : Nonempty (FailingBoundaryLineageAt
    M11BoundaryMaintenanceRegression.maintenance maintenanceAnomiePhase) :=
  anomie_hasFailingBoundaryLineage exactBoundarySaturation
    maintenance_anomie_tag

/-- Every canonical failure is the exact recurrent backlog occurrence. -/
theorem every_failure_is_recurrent
    (failure : FailingBoundaryLineageAt
      M11BoundaryMaintenanceRegression.maintenance maintenanceAnomiePhase) :
    failure.unit = recurrentUnit := by
  have membership := failure.backlog_mem
  change failure.unit ∈ [recurrentUnit] at membership
  exact List.mem_singleton.mp membership

/-! ## Actual eventwise settlement on that same installed phase -/

/-- Reindex the already fixed M11 crossing law to the maintenance phase. -/
abbrev costCrossingCompiler : SourceOwnedCrossingCompiler
    M11BoundaryMaintenanceRegression.maintenance.phaseRateCompiler := by
  change SourceOwnedCrossingCompiler
    M11BoundaryMaintenanceRegression.rateCompiler
  exact M11BoundaryMaintenanceRegression.maintenanceCrossingCompiler

/-- Exact transporter from the already-certified M10 service receipts to the
same queue units under the M11 installed-root index.  It carries an `HEq`
occurrence identity rather than minting a second receipt family. -/
inductive MaintenanceServiceReceiptAt :
    M11BoundaryMaintenanceRegression.maintenance.phaseRateCompiler.QueueUnit →
      LifecycleEvent V → Type
  | transported
      {maintenanceUnit :
        M11BoundaryMaintenanceRegression.maintenance.phaseRateCompiler.QueueUnit}
      {event : LifecycleEvent V}
      (sourceUnit : installedCompiler.QueueUnit)
      (sameOccurrence : HEq maintenanceUnit sourceUnit)
      (receipt : ServiceReceiptAt sourceUnit event) :
      MaintenanceServiceReceiptAt maintenanceUnit event

def maintenanceServiceCompiler : SourceOwnedOccurrenceServiceCompiler
    M11BoundaryMaintenanceRegression.maintenance.phaseRateCompiler P where
  ServesAt := MaintenanceServiceReceiptAt

/-- The actual two-event run services precisely the allocated prefix of the
same three-crossing M11 anomie phase. -/
def actualAnomieSettlement : ExactServedCrossingDebitedRunAt
    maintenanceAnomiePhase debited maintenanceServiceCompiler where
  sourceBudget_eq_capacity := rfl
  eventsLength_eq_allocated := rfl
  serviceAt := by
    rintro ⟨index, index_lt⟩
    cases index with
    | zero =>
        exact MaintenanceServiceReceiptAt.transported
          firstUnit HEq.rfl ServiceReceiptAt.first
    | succ index =>
        cases index with
        | zero =>
            exact MaintenanceServiceReceiptAt.transported
              middleUnit HEq.rfl ServiceReceiptAt.middle
        | succ index =>
            exact False.elim (by
              change Nat.succ (Nat.succ index) < 2 at index_lt
              omega)

@[simp] theorem actualResidualSettled_eq_two :
    actualAnomieSettlement.actualResidualSettled = 2 :=
  rfl

@[simp] theorem maintenanceDebt_eq_three :
    maintenanceDebt (phase := maintenanceAnomiePhase) = 3 :=
  rfl

@[simp] theorem anomie_preservedHeadroom_eq_zero :
    preservedHeadroom (phase := maintenanceAnomiePhase) = 0 :=
  rfl

/-- Strong memo inequality on one installed phase and root: `3 > 2 + 0`. -/
theorem actual_maintenanceDebt_gt_settled_add_headroom :
    maintenanceDebt (phase := maintenanceAnomiePhase) >
      actualAnomieSettlement.actualResidualSettled +
        preservedHeadroom (phase := maintenanceAnomiePhase) :=
  (actualAnomieSettlement
    |>.maintenanceDebt_gt_actualSettled_add_headroom_iff_anomie).mpr
      maintenance_anomie_tag

/-- Every serviced ordinal retains both its exact crossing and actual
lifecycle-event receipt. -/
def firstServicedCrossing : costCrossingCompiler.ExactCrossing :=
  costCrossingCompiler.exactCrossingOf
    (maintenanceAnomiePhase.served.get ⟨0, by decide⟩)

def secondServicedCrossing : costCrossingCompiler.ExactCrossing :=
  costCrossingCompiler.exactCrossingOf
    (maintenanceAnomiePhase.served.get ⟨1, by decide⟩)

theorem actual_service_keeps_two_distinct_crossings :
    firstServicedCrossing ≠ secondServicedCrossing := by
  apply SourceOwnedCrossingCompiler.ExactCrossing.ne_of_position_ne
  exact first_middle_positions_are_distinct

/-- The actual-service inequality and anomie tag are equivalent, rather than
merely coexisting in the fixture. -/
theorem actual_service_inequality_is_anomie_exact :
    maintenanceDebt (phase := maintenanceAnomiePhase) >
        actualAnomieSettlement.actualResidualSettled +
          preservedHeadroom (phase := maintenanceAnomiePhase) ↔
      maintenanceAnomiePhase.phaseTag = .anomie :=
  actualAnomieSettlement
    |>.maintenanceDebt_gt_actualSettled_add_headroom_iff_anomie

structure BoundaryFailureWholeCertificate where
  actualSettlement : ExactServedCrossingDebitedRunAt
    maintenanceAnomiePhase debited maintenanceServiceCompiler
  actualInequality :
    maintenanceDebt (phase := maintenanceAnomiePhase) >
      actualSettlement.actualResidualSettled +
        preservedHeadroom (phase := maintenanceAnomiePhase)
  canonicalFailure : Nonempty (FailingBoundaryLineageAt
    M11BoundaryMaintenanceRegression.maintenance maintenanceAnomiePhase)
  rootFactorization :
    M11BoundaryMaintenanceRegression.installedRenewal.RootAnswerAndNextFactorizes
  generatedNext :
    M11BoundaryMaintenanceRegression.maintenance.generatedNext =
      M11BoundaryMaintenanceRegression.root.generatedNextCurrentAt
        M11BoundaryMaintenanceRegression.visit

def boundaryFailureWholeConsumer : BoundaryFailureWholeCertificate where
  actualSettlement := actualAnomieSettlement
  actualInequality := actual_maintenanceDebt_gt_settled_add_headroom
  canonicalFailure := canonicalFailingBoundary
  rootFactorization :=
    M11BoundaryMaintenanceRegression.installed_factorizes_root_answer_and_next
  generatedNext :=
    M11BoundaryMaintenanceRegression.local_run_reads_only_root_generated_next.1

end
end M11BoundaryFailureRegression
end Society
end ProcessGame
end SaturationMonoid
