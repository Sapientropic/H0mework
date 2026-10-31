/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.OccurrenceCapacityConsumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Space.SourceGeneratedCrossing

/-!
# Crossing cost and source-generated maintenance failure

Crossing cost is not a second phase system.  This module maps the exact M10
served/backlog decomposition into exact crossings and proves that the memo's
maintenance-debt inequality is precisely the existing anomie comparison.

When the source classifier certifies every crossing in the observed prefix as
a boundary crossing, that same inequality generates an exact unpaid boundary
crossing.  No failure tag, debt scalar, crossing list, or boundary witness is
accepted by a producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Space
namespace CrossingCost

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Capacity

universe u uLineage uUnit
universe uSiteSeed uSiteLineage uFlow
universe uBoundarySeed uBoundaryLineage uBoundaryClass

variable {LocalSource LocalState Seed : Type u}
variable {occurrenceOf : LocalSource → RootedAccountedUnfolding LocalState}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {SeedAt : LocalSource → LocalState → Seed → Prop}
variable {Lineage : LocalSource → Type uLineage}
variable {lineageOf : ∀ source,
  SourceSeed occurrenceOf Seed SeedAt source → Lineage source}

variable {N : WorldRelationNetwork.{u}}
variable {RootV : ConstructiveRoot.Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N RootV}
variable {ConsumerAt DispositionAt :
  SourceSeed occurrenceOf Seed SeedAt game.source → Type u}
variable {recognition : SourceNativeRenewalRecognitionAt root game Seed SeedAt
  ConsumerAt DispositionAt}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}
variable {installed : SourceInstalledRenewalAt recognition visit}

variable {rateCompiler : SourceOwnedOccurrenceRateCompiler.{u, u, u,
  uLineage, uUnit} game Seed SeedAt Lineage lineageOf
    installed.payload.sourceSeed}
variable {exactPrefix : SourceGeneratedExactQueuePrefixAt rateCompiler}
variable {phase : SourceGeneratedOccurrenceCapacityPhaseAt
  installed rateCompiler exactPrefix}
variable {crossingCompiler : SourceOwnedCrossingCompiler rateCompiler}

/-! ## The exact M10 decomposition, read as crossings -/

/-- All crossing debt visible at the exact source-derived boundary. -/
def debtCrossings : List crossingCompiler.ExactCrossing :=
  phase.queuePrefix.map crossingCompiler.exactCrossingOf

/-- Crossings covered by the installed operational capacity. -/
def settledCrossings : List crossingCompiler.ExactCrossing :=
  phase.served.map crossingCompiler.exactCrossingOf

/-- Exact crossing occurrences left unpaid by that capacity. -/
def unsettledCrossings : List crossingCompiler.ExactCrossing :=
  phase.backlog.map crossingCompiler.exactCrossingOf

/-- Existing M10 headroom; no second capacity coordinate is introduced. -/
def preservedHeadroom : Nat := phase.spare

/-- Maintenance debt is the number of exact crossing occurrences, not a
caller-supplied scalar. -/
def maintenanceDebt : Nat := phase.rate

/-- Capacity allocated to the observed crossings.  This is deliberately not
called settlement: actual settlement is introduced below only through a
`NativeDebitedRun` and eventwise source service receipts. -/
def allocatedServiceCapacity : Nat := phase.served.length

theorem settled_append_unsettled :
    settledCrossings (phase := phase)
        (crossingCompiler := crossingCompiler) ++
      unsettledCrossings (phase := phase)
        (crossingCompiler := crossingCompiler) =
      debtCrossings (phase := phase)
        (crossingCompiler := crossingCompiler) := by
  unfold settledCrossings unsettledCrossings debtCrossings
  rw [← List.map_append, phase.served_append_backlog]

@[simp] theorem debtCrossings_length_eq_maintenanceDebt :
    (debtCrossings (phase := phase)
      (crossingCompiler := crossingCompiler)).length =
      maintenanceDebt (phase := phase) := by
  simp [debtCrossings, maintenanceDebt,
    SourceGeneratedOccurrenceCapacityPhaseAt.rate]

@[simp] theorem allocatedServiceCapacity_eq_min :
    allocatedServiceCapacity (phase := phase) =
      min phase.capacity phase.rate := by
  simp [allocatedServiceCapacity]

@[simp] theorem unsettledCrossings_length :
    (unsettledCrossings (phase := phase)
      (crossingCompiler := crossingCompiler)).length =
      phase.rate - phase.capacity := by
  simp [unsettledCrossings]

/-- Capacity allocation alone satisfies the same arithmetic partition as M10.
This lemma is not an actual-settlement claim. -/
theorem maintenanceDebt_gt_allocated_add_headroom_iff_anomie :
    maintenanceDebt (phase := phase) >
      allocatedServiceCapacity (phase := phase) +
        preservedHeadroom (phase := phase) ↔
      phase.phaseTag = .anomie := by
  rw [phase.phaseTag_eq_anomie_iff]
  unfold maintenanceDebt allocatedServiceCapacity preservedHeadroom
    SourceGeneratedOccurrenceCapacityPhaseAt.spare
  rw [phase.served_length]
  constructor
  · intro inequality
    apply Nat.lt_of_not_ge
    intro rate_le_capacity
    have lowerBound : phase.rate ≤
        min phase.capacity phase.rate + (phase.capacity - phase.rate) := by
      rw [min_eq_right rate_le_capacity]
      exact Nat.le_add_right phase.rate _
    exact (Nat.not_lt_of_ge lowerBound) inequality
  · intro capacity_lt_rate
    have capacity_le_rate : phase.capacity ≤ phase.rate :=
      capacity_lt_rate.le
    rw [min_eq_left capacity_le_rate,
      Nat.sub_eq_zero_of_le capacity_le_rate, Nat.add_zero]
    exact capacity_lt_rate

/-- Anomie is witnessed by a nonempty exact crossing residual. -/
theorem anomie_unsettledCrossings_ne_nil
    (anomie : phase.phaseTag = .anomie) :
    unsettledCrossings (phase := phase)
      (crossingCompiler := crossingCompiler) ≠ [] := by
  simpa [unsettledCrossings] using phase.anomie_backlog_ne_nil anomie

/-! ## Actual eventwise settlement -/

variable {RunV : ResponsibilityLifecycle.Vocabulary.{u}}
variable {P : NativeResponsibilityProcess RunV}
variable {B : NativeCarryDebitProcess P}
variable {runLineage : RunV.Lineage}
variable {sourceState targetState : ResponsibilityState RunV}
variable {run : P.Run sourceState targetState}
variable {debited : NativeDebitedRun P B runLineage run}
variable {service : SourceOwnedOccurrenceServiceCompiler rateCompiler P}

/-- Actual service of exactly the capacity-allocated crossing prefix.  The
count comes from a genuine debited lifecycle run, and every ordinal is tied to
the corresponding source queue unit by a service receipt. -/
structure ExactServedCrossingDebitedRunAt
    (phase : SourceGeneratedOccurrenceCapacityPhaseAt
      installed rateCompiler exactPrefix)
    (debited : NativeDebitedRun P B runLineage run)
    (service : SourceOwnedOccurrenceServiceCompiler rateCompiler P) :
    Type (max (u + 4) (max (uLineage + 1) (uUnit + 2))) where
  sourceBudget_eq_capacity :
    B.budgetAt sourceState runLineage = phase.capacity
  eventsLength_eq_allocated :
    run.events.length = phase.served.length
  serviceAt : (index : Fin phase.served.length) →
    service.ServesAt
      (phase.served.get index)
      (run.events.get
        (Fin.cast eventsLength_eq_allocated.symm index))

namespace ExactServedCrossingDebitedRunAt

variable (settlement : ExactServedCrossingDebitedRunAt
  phase debited service)

/-- Actual settled residual count; unlike capacity allocation, this value is
read from the certified lifecycle run. -/
def actualResidualSettled
    (_settlement : ExactServedCrossingDebitedRunAt
      phase debited service) : Nat :=
  run.events.length

@[simp] theorem actualResidualSettled_eq_allocated :
    settlement.actualResidualSettled =
      allocatedServiceCapacity (phase := phase) := by
  exact settlement.eventsLength_eq_allocated

/-- Exact crossing occurrence serviced at one ordinal. -/
def servicedCrossingAt (index : Fin phase.served.length) :
    crossingCompiler.ExactCrossing :=
  crossingCompiler.exactCrossingOf (phase.served.get index)

/-- Source-owned service receipt at the same queue/run ordinal. -/
def serviceReceiptAt (index : Fin phase.served.length) :
    service.ServesAt
      (phase.served.get index)
      (run.events.get
        (Fin.cast settlement.eventsLength_eq_allocated.symm index)) :=
  settlement.serviceAt index

/-- With actual debit receipts installed, the memo's maintenance inequality
is exactly M10 anomie.  No settlement count is inferred from capacity alone. -/
theorem maintenanceDebt_gt_actualSettled_add_headroom_iff_anomie :
    maintenanceDebt (phase := phase) >
      settlement.actualResidualSettled +
        preservedHeadroom (phase := phase) ↔
      phase.phaseTag = .anomie := by
  rw [settlement.actualResidualSettled_eq_allocated]
  exact maintenanceDebt_gt_allocated_add_headroom_iff_anomie

end ExactServedCrossingDebitedRunAt

end CrossingCost
end Space
end Society
end ProcessGame
end SaturationMonoid
