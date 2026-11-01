import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capture.CounterpartyRenewal
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Capture.CaptureResponsibilityDispositionRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Power.EmploymentOutsideOptionGeometryRegression

/-!
# M14 relation-owned counterparty capture renewal

The fixed captured leave code now renews an exact source-generated exchange
counterparty relation and target role.  Its actor is distinct from the worker,
its relation authority lives in the exchange compiler rather than the exit
compiler, and its activated residual consumer generates the payment next.

At every generated depth the relation renewal is joined to the exact periodic
payment/root occurrence and actual service.  Full capture yields counterparty
capture renewal while the worker's actual exit type is empty.  Conversely,
under no capture the worker exit exists and the counterparty relation standing
still exists, but no capture verdict is available.  These are separated
authorities, not competing definitions of one actor or relation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14CounterpartyCaptureRenewalRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open Settlement.SourceOwnedSettlementCompiler
open UBI.Capture
open Lifecycle.Universal.FixedAdapter
open M3FiniteExchangeFixture M3ExchangeSettlementPriceRegression
open M14UBIExitCapacityFixture
open M14UBIPeriodicRootHistory
open M14UBIPeriodicActualServiceCapacity
open M14EmploymentOutsideOptionGeometryRegression
open M14CaptureResponsibilityDispositionRegression
open _root_.SaturationMonoid.ProcessGame.Regression.Society.Lifecycle.Universal

theorem fixedCounterpartyCaptureRenewal :
    SourceGeneratedCounterpartyCaptureRenewalAt capturedProgram
      ExitFutureCode.leave leave_is_captured :=
  SourceGeneratedCounterpartyCaptureRenewalAt.generate capturedProgram
    ExitFutureCode.leave leave_is_captured

theorem counterparty_actor_is_not_worker :
    exactCounterpartyActor exactResidualActivation ≠ worker := by
  intro equality
  have values := congrArg Subtype.val equality
  cases values

theorem counterparty_relation_and_actor_have_exact_trace_provenance :
    ∃ seed : relationCompiler.ExactRelationSeed,
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = core.targetFace.state Lifecycle.actualEventGame.source ∧
        relationCompiler.relationSeedAt Lifecycle.actualEventGame.source
          state seed.1 ∧
        core.targetFace.SeedAt Lifecycle.actualEventGame.source state
          (relationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor relationCompiler =
        exactCounterpartyActor exactResidualActivation ∧
      relationCompiler.relationOf seed =
        exactCaptureCounterpartyRelation
          (paymentSeed := exactResidualActivation) :=
  fixedCounterpartyCaptureRenewal.exact_relation_actor_provenance

theorem counterparty_target_role_is_relation_phase_generated :
    relationCompiler.RelationRoleAt
      (exactCounterpartyActor exactResidualActivation)
      (exactCaptureCounterpartyRelation
        (paymentSeed := exactResidualActivation)) .target
      (exactCaptureCounterpartyTargetRole
        (paymentSeed := exactResidualActivation)) ∧
    exactCaptureCounterpartyPhase (paymentSeed := exactResidualActivation) =
      relationCompiler.phaseStepOf Lifecycle.actualEventGame.source
        (exactCaptureCounterpartyRelation
          (paymentSeed := exactResidualActivation)).1 :=
  ⟨fixedCounterpartyCaptureRenewal.counterpartyTargetRole,
    fixedCounterpartyCaptureRenewal.phaseGenerated⟩

theorem counterparty_capture_consumer_generates_payment_next :
    capturedProgram.purchasingPowerStanding.activatedConsumer.nextGeneratedState =
      capturedProgram.payment.nextGenerated :=
  fixedCounterpartyCaptureRenewal.activated_consumer_generates_payment_next

/-- Commuting mouth which prevents a free relation-role wrapper: the exact
capture beneficiary, generated counterparty role, source-owned residual, and
consumer-generated next all come from the same indexed program/seed. -/
theorem counterparty_beneficiary_role_residual_next_commute :
    OpenSettlementAt.protectedInterest
        (fullCapture.captureSettlement ExitFutureCode.leave
          leave_is_captured) =
      exchangeLaw.protectedInterestOfActor
        (exactCounterpartyActor exactResidualActivation) ∧
    relationCompiler.RelationRoleAt
      (exactCounterpartyActor exactResidualActivation)
      (exactCaptureCounterpartyRelation
        (paymentSeed := exactResidualActivation)) .target
      (exactCaptureCounterpartyTargetRole
        (paymentSeed := exactResidualActivation)) ∧
    Nonempty (SourceOwnsResponsibilityIncidence M3FiniteExchangeFixture.V
      (M3FiniteExchangeFixture.P.boundarySource
        capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
      (exactOpenSettlement exactResidualActivation).obligation) ∧
    capturedProgram.purchasingPowerStanding.activatedConsumer.nextGeneratedState =
      capturedProgram.payment.nextGenerated :=
  ⟨fixedCounterpartyCaptureRenewal.captureDisposition.beneficiaryGenerated,
    fixedCounterpartyCaptureRenewal.counterpartyTargetRole,
    fixedCounterpartyCaptureRenewal.captureDisposition.sourceOwnedResidual,
    fixedCounterpartyCaptureRenewal.captureDisposition.consumerNextIsPaymentNext⟩

/-- Typed coproduct used only to state cross-compiler separation.  Its two
values retain the actual generated relations; it is not a relation registry. -/
inductive CaptureExitRelationAuthority where
  | capture (relation : relationCompiler.GeneratedRelation)
  | exit (relation : exitRelationCompiler.GeneratedRelation)

def counterpartyCaptureRelationAuthority : CaptureExitRelationAuthority :=
  .capture (exactCaptureCounterpartyRelation
    (paymentSeed := exactResidualActivation))

def workerExitRelationAuthority : CaptureExitRelationAuthority :=
  .exit independentExitRelation

theorem counterparty_and_worker_exit_relation_authorities_distinct :
    counterpartyCaptureRelationAuthority ≠ workerExitRelationAuthority := by
  intro equality
  cases equality

/-- Temporal authority join.  The local relation law may recur, but each
renewal is indexed by its exact periodic payment/root occurrence. -/
structure PeriodicCounterpartyCaptureRenewalAt
    (depth : Nat)
    (payment : PeriodicSourceBackedPaymentAt depth) : Prop where
  periodicCapture : PeriodicCaptureResponsibilityAt depth payment
  relationRenewal : SourceGeneratedCounterpartyCaptureRenewalAt
    capturedProgram ExitFutureCode.leave leave_is_captured
  actorDistinctFromWorker :
    exactCounterpartyActor exactResidualActivation ≠ worker
  relationAuthoritiesDistinct :
    counterpartyCaptureRelationAuthority ≠ workerExitRelationAuthority
  workerActualExitEmpty : IsEmpty
    (capturedGeometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt

theorem periodicCounterpartyCaptureRenewalAt (depth : Nat) :
    PeriodicCounterpartyCaptureRenewalAt depth
      (periodicSourceBackedPaymentAt depth) where
  periodicCapture := periodicCaptureResponsibilityAt depth
  relationRenewal := fixedCounterpartyCaptureRenewal
  actorDistinctFromWorker := counterparty_actor_is_not_worker
  relationAuthoritiesDistinct :=
    counterparty_and_worker_exit_relation_authorities_distinct
  workerActualExitEmpty := captured_actual_outside_option_is_empty_at depth

theorem full_capture_renews_counterparty_while_worker_exit_empty
    (depth : Nat) :
    SourceGeneratedCounterpartyCaptureRenewalAt capturedProgram
        ExitFutureCode.leave leave_is_captured ∧
      IsEmpty
        (capturedGeometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt ∧
      exactCounterpartyActor exactResidualActivation ≠ worker :=
  ⟨fixedCounterpartyCaptureRenewal,
    captured_actual_outside_option_is_empty_at depth,
    counterparty_actor_is_not_worker⟩

/-- Under no capture, worker exit and the counterparty relation standing can
coexist; what is absent is specifically the capture verdict/renewal. -/
theorem uncaptured_worker_exit_coexists_with_counterparty_relation
    (depth : Nat) :
    Nonempty
        (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt ∧
      relationCompiler.GeneratedInterestAt
        (exactCounterpartyActor exactResidualActivation)
        (exactCaptureCounterpartyRelation
          (paymentSeed := exactResidualActivation)) ∧
      ¬ noCapture.Captures ExitFutureCode.leave ∧
      counterpartyCaptureRelationAuthority ≠ workerExitRelationAuthority :=
  ⟨uncaptured_actual_outside_option_at depth,
    fixedCounterpartyCaptureRenewal.counterpartyInterest,
    uncaptured_leave_has_no_capture_verdict,
    counterparty_and_worker_exit_relation_authorities_distinct⟩

structure CounterpartyCaptureRenewalCertificate : Prop where
  everyDepth : ∀ depth : Nat,
    PeriodicCounterpartyCaptureRenewalAt depth
      (periodicSourceBackedPaymentAt depth)
  actorDistinct : exactCounterpartyActor exactResidualActivation ≠ worker
  relationAuthoritiesDistinct :
    counterpartyCaptureRelationAuthority ≠ workerExitRelationAuthority
  exactTraceProvenance :
    ∃ seed : relationCompiler.ExactRelationSeed,
      (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
        state = core.targetFace.state Lifecycle.actualEventGame.source ∧
        relationCompiler.relationSeedAt Lifecycle.actualEventGame.source
          state seed.1 ∧
        core.targetFace.SeedAt Lifecycle.actualEventGame.source state
          (relationCompiler.beneficiaryActorSeed seed.1)) ∧
      seed.actor relationCompiler =
        exactCounterpartyActor exactResidualActivation ∧
      relationCompiler.relationOf seed =
        exactCaptureCounterpartyRelation
          (paymentSeed := exactResidualActivation)
  generatedRoleAndPhase :
    relationCompiler.RelationRoleAt
      (exactCounterpartyActor exactResidualActivation)
      (exactCaptureCounterpartyRelation
        (paymentSeed := exactResidualActivation)) .target
      (exactCaptureCounterpartyTargetRole
        (paymentSeed := exactResidualActivation)) ∧
    exactCaptureCounterpartyPhase (paymentSeed := exactResidualActivation) =
      relationCompiler.phaseStepOf Lifecycle.actualEventGame.source
        (exactCaptureCounterpartyRelation
          (paymentSeed := exactResidualActivation)).1
  consumerGeneratesPaymentNext :
    capturedProgram.purchasingPowerStanding.activatedConsumer.nextGeneratedState =
      capturedProgram.payment.nextGenerated
  beneficiaryRoleResidualNextCommute :
    OpenSettlementAt.protectedInterest
        (fullCapture.captureSettlement ExitFutureCode.leave
          leave_is_captured) =
      exchangeLaw.protectedInterestOfActor
        (exactCounterpartyActor exactResidualActivation) ∧
    relationCompiler.RelationRoleAt
      (exactCounterpartyActor exactResidualActivation)
      (exactCaptureCounterpartyRelation
        (paymentSeed := exactResidualActivation)) .target
      (exactCaptureCounterpartyTargetRole
        (paymentSeed := exactResidualActivation)) ∧
    Nonempty (SourceOwnsResponsibilityIncidence M3FiniteExchangeFixture.V
      (M3FiniteExchangeFixture.P.boundarySource
        capturedProgram.purchasingPowerStanding.activatedConsumer.activation)
      (exactOpenSettlement exactResidualActivation).obligation) ∧
    capturedProgram.purchasingPowerStanding.activatedConsumer.nextGeneratedState =
      capturedProgram.payment.nextGenerated
  capturedOneSide : ∀ depth : Nat,
    SourceGeneratedCounterpartyCaptureRenewalAt capturedProgram
        ExitFutureCode.leave leave_is_captured ∧
      IsEmpty
        (capturedGeometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt ∧
      exactCounterpartyActor exactResidualActivation ≠ worker
  uncapturedCoexistence : ∀ depth : Nat,
    Nonempty
        (geometryCompilerAt depth).SourceGeneratedActionableExitRenewalAt ∧
      relationCompiler.GeneratedInterestAt
        (exactCounterpartyActor exactResidualActivation)
        (exactCaptureCounterpartyRelation
          (paymentSeed := exactResidualActivation)) ∧
      ¬ noCapture.Captures ExitFutureCode.leave ∧
      counterpartyCaptureRelationAuthority ≠ workerExitRelationAuthority

theorem counterpartyCaptureRenewalDirectConsumer :
    CounterpartyCaptureRenewalCertificate where
  everyDepth := periodicCounterpartyCaptureRenewalAt
  actorDistinct := counterparty_actor_is_not_worker
  relationAuthoritiesDistinct :=
    counterparty_and_worker_exit_relation_authorities_distinct
  exactTraceProvenance :=
    counterparty_relation_and_actor_have_exact_trace_provenance
  generatedRoleAndPhase :=
    counterparty_target_role_is_relation_phase_generated
  consumerGeneratesPaymentNext :=
    counterparty_capture_consumer_generates_payment_next
  beneficiaryRoleResidualNextCommute :=
    counterparty_beneficiary_role_residual_next_commute
  capturedOneSide :=
    full_capture_renews_counterparty_while_worker_exit_empty
  uncapturedCoexistence :=
    uncaptured_worker_exit_coexists_with_counterparty_relation

end
end M14CounterpartyCaptureRenewalRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14CounterpartyCaptureRenewalRegression.periodicCounterpartyCaptureRenewalAt
#print axioms SaturationMonoid.ProcessGame.Society.M14CounterpartyCaptureRenewalRegression.counterpartyCaptureRenewalDirectConsumer
