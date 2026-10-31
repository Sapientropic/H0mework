import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.OccurrenceCapacityConsumer
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.Fixture.OccurrenceCapacityRenewalRoot
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.Fixture.OccurrenceCapacityDebitedRun

/-!
# M10 actual-debit consumers

The critical and anomie prefixes share the same exact rate compiler and the
same installed renewal row of capacity two.  A genuine two-event maintenance
run aligns with the critical prefix and reaches target budget zero.  A run
claiming the three-event anomie rate at that same source budget cannot carry
`NativeDebitedRun` certification.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M10OccurrenceCapacityDebitConsumerRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity Renewal
open M10OccurrenceCapacityProcessFixture
open M10OccurrenceCapacityRenewalRootFixture
open M10OccurrenceCapacityDebitedRunFixture

/-- The same rate compiler reindexed to the literal installed payload seed. -/
def installedCompiler : SourceOwnedOccurrenceRateCompiler.{0, 0, 0, 0, 0}
    game Seed seedAt Lineage lineageOf installedRenewal.payload.sourceSeed :=
  compiler

@[simp] theorem installedCompiler_queue_length :
    installedCompiler.queue.length = 3 := by
  simp [installedCompiler]

def criticalPrefix : SourceGeneratedExactQueuePrefixAt installedCompiler :=
  SourceGeneratedExactQueuePrefixAt.generate installedCompiler
    ⟨2, by rw [installedCompiler_queue_length]; decide⟩

def criticalPhase : SourceGeneratedOccurrenceCapacityPhaseAt
    installedRenewal installedCompiler criticalPrefix :=
  SourceGeneratedOccurrenceCapacityPhaseAt.generate
    installedRenewal installedCompiler criticalPrefix

@[simp] theorem critical_rate_eq_two : criticalPhase.rate = 2 := rfl

@[simp] theorem critical_capacity_eq_two : criticalPhase.capacity = 2 := rfl

@[simp] theorem critical_tag : criticalPhase.phaseTag = .critical := rfl

theorem criticalAlignment : ExactOccurrenceCapacityDebitedRunAt
    criticalPhase debited where
  sourceBudget_eq_capacity := rfl
  eventsLength_eq_rate := rfl

/-- Source-owned ordered service relation for the two concrete arrival units
and the two actual maintenance events. -/
inductive ServiceReceiptAt :
    installedCompiler.QueueUnit → LifecycleEvent V → Type
  | first : ServiceReceiptAt firstUnit firstMaintenance.lifecycleEvent
  | middle : ServiceReceiptAt middleUnit secondMaintenance.lifecycleEvent

def serviceCompiler :
    SourceOwnedOccurrenceServiceCompiler installedCompiler P where
  ServesAt := ServiceReceiptAt

def criticalProvenanceAlignment :
    ExactProvenanceOccurrenceCapacityDebitedRunAt
      criticalPhase debited serviceCompiler where
  numeric := criticalAlignment
  serviceAt := by
    rintro ⟨index, index_lt⟩
    have prefix_length : criticalPhase.queuePrefix.length = 2 :=
      critical_rate_eq_two
    cases index with
    | zero => exact ServiceReceiptAt.first
    | succ index =>
        cases index with
        | zero => exact ServiceReceiptAt.middle
        | succ index =>
            exact False.elim (by rw [prefix_length] at index_lt; omega)

/-- Critical is now an actual liveness conclusion, not just `2 = 2`. -/
theorem critical_actual_run_exhausts_target_budget :
    debitProcess.budgetAt secondMaintenance.target () = 0 :=
  ExactOccurrenceCapacityDebitedRunAt.critical_targetBudget_eq_zero
    criticalAlignment critical_tag

/-- The stronger eventwise correspondence reaches the same exhaustion result
without erasing either queue-unit or lifecycle-event provenance. -/
theorem critical_eventwise_service_exhausts_target_budget :
    debitProcess.budgetAt secondMaintenance.target () = 0 :=
  ExactProvenanceOccurrenceCapacityDebitedRunAt.critical_targetBudget_eq_zero
    criticalProvenanceAlignment critical_tag

def first_service_receipt :
    serviceCompiler.ServesAt firstUnit firstMaintenance.lifecycleEvent :=
  ServiceReceiptAt.first

def middle_service_receipt :
    serviceCompiler.ServesAt middleUnit secondMaintenance.lifecycleEvent :=
  ServiceReceiptAt.middle

def anomiePrefix : SourceGeneratedExactQueuePrefixAt installedCompiler :=
  SourceGeneratedExactQueuePrefixAt.generate installedCompiler
    ⟨3, by rw [installedCompiler_queue_length]; decide⟩

def anomiePhase : SourceGeneratedOccurrenceCapacityPhaseAt
    installedRenewal installedCompiler anomiePrefix :=
  SourceGeneratedOccurrenceCapacityPhaseAt.generate
    installedRenewal installedCompiler anomiePrefix

@[simp] theorem anomie_rate_eq_three : anomiePhase.rate = 3 := rfl

@[simp] theorem anomie_capacity_eq_two : anomiePhase.capacity = 2 := rfl

@[simp] theorem anomie_tag : anomiePhase.phaseTag = .anomie := rfl

/-- Any three-event lifecycle run at the exact capacity-two source is denied
full debit certification by the anomie phase. -/
theorem anomie_rejects_every_three_event_full_debit
    {target : ResponsibilityState V}
    {candidateRun : P.Run sourceState target}
    (threeEvents : candidateRun.events.length = 3) :
    IsEmpty (NativeDebitedRun P debitProcess () candidateRun) :=
  anomie_forbids_full_debited_run anomie_tag rfl threeEvents

/-- The existing two-step actual run cannot be relabelled as a full consumer
of the three-unit anomie prefix. -/
theorem two_step_run_cannot_align_with_anomie :
    IsEmpty (ExactOccurrenceCapacityDebitedRunAt anomiePhase debited) :=
  anomie_forbids_full_debited_consumption anomie_tag debited

structure OccurrenceCapacityDebitConsumerCertificate where
  critical : SourceGeneratedOccurrenceCapacityPhaseAt
    installedRenewal installedCompiler criticalPrefix
  criticalRun : NativeDebitedRun P debitProcess () run
  criticalAlignment : ExactOccurrenceCapacityDebitedRunAt
    critical criticalRun
  service : SourceOwnedOccurrenceServiceCompiler installedCompiler P
  criticalProvenance : ExactProvenanceOccurrenceCapacityDebitedRunAt
    critical criticalRun service
  criticalTargetZero :
    debitProcess.budgetAt secondMaintenance.target () = 0
  anomie : SourceGeneratedOccurrenceCapacityPhaseAt
    installedRenewal installedCompiler anomiePrefix
  anomieNoTwoStepAlignment :
    IsEmpty (ExactOccurrenceCapacityDebitedRunAt anomie criticalRun)

def occurrenceCapacityDebitDirectConsumer :
    OccurrenceCapacityDebitConsumerCertificate where
  critical := criticalPhase
  criticalRun := debited
  criticalAlignment := criticalAlignment
  service := serviceCompiler
  criticalProvenance := criticalProvenanceAlignment
  criticalTargetZero := critical_actual_run_exhausts_target_budget
  anomie := anomiePhase
  anomieNoTwoStepAlignment := two_step_run_cannot_align_with_anomie

end
end M10OccurrenceCapacityDebitConsumerRegression
end Society
end ProcessGame
end SaturationMonoid
