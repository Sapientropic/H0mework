import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.UBIExitCapacityFixture
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.Lifecycle.Universal.UniversalSixClassRegression

/-!
# M14 UBI exit-capacity direct consumer

This consumer closes the local strongest iff and both decisive controls:

* an exact employment-power loss does not erase the worker actor, while an
  uncaptured relation-owned target continuation yields UBI exit capacity;
* the same source-backed payment under complete settlement capture is only a
  nominal transfer and admits no exit-capacity renewal.

The zero quote remains a price observation and does not itself count as
capture.  Job Guarantee is independently empty because the employment target
future is empty.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ExitCapacityRenewalRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Settlement Price Money UBI
open Lifecycle.Universal.FixedAdapter
open M3ExchangeSettlementPriceRegression
open M8PurchasingPowerStandingRegression
open M14UBIExitCapacityFixture
open _root_.SaturationMonoid.ProcessGame.Regression.Society.Lifecycle.Universal

theorem worker_is_surviving_target_actor :
    worker = targetActor .t0 ∧
      law.SurviveAt (sourceActor .s0) worker := by
  have worker_eq : worker = targetActor .t0 := by
    apply Subtype.ext
    rfl
  constructor
  · exact worker_eq
  · rw [worker_eq]
    exact fixed_survival

theorem exact_employment_relation_loss :
    employmentLoss.power.freedomChange.kind = .lost ∧
      ExitFutureCode.work ∉
        exitRelationCompiler.futureCodesAt employmentRelation .target ∧
      employmentRelation ≠ independentExitRelation :=
  ⟨employmentLoss.changeKind_eq_lost,
    employmentLoss.employment_target_rejects_lostCode,
    employment_ne_independentExit⟩

theorem strongest_exitCapacityRenewal_iff :
    Nonempty (ExitCapacityRenewalAt exitCapacityProgram) ↔
      ∃ code,
        code ∈ exitRelationCompiler.futureCodeCarrier ∧
        Nonempty (exitRelationCompiler.FutureContinuationAt
          independentExitRelation.1 .target code) ∧
        ¬ exitRelationCompiler.futureIdle code ∧
        ¬ noCapture.Captures code :=
  ExitCapacityRenewalAt.nonempty_iff_sourceGeneratedUncapturedContinuation

theorem exit_survives_employment_loss_and_capture :
    employmentLoss.lostCode ∉
        exitRelationCompiler.futureCodesAt employmentRelation .target ∧
      Nonempty (exitRelationCompiler.FutureContinuationAt
        independentExitRelation.1 .target exitCapacityRenewal.exit.1) ∧
      ¬ exitRelationCompiler.futureIdle exitCapacityRenewal.exit.1 ∧
      ¬ noCapture.Captures exitCapacityRenewal.exit.1 :=
  exitCapacityRenewal.preserves_actionable_continuation_after_employment_loss

theorem exit_has_domain_native_continuation_witness :
    ∃ continuation : exitRelationCompiler.FutureContinuationAt
        independentExitRelation.1 .target exitCapacityRenewal.exit.1,
      exitRelationCompiler.FutureContinuationWitnessAt
        independentExitRelation.1 .target exitCapacityRenewal.exit.1
        continuation :=
  exitCapacityProgram.exitCone.actionableExit_has_witnessed_continuation
    exitCapacityRenewal.exit

theorem payment_is_source_backed_and_generates_next :
    (∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      residualConsumerCompiler.activationSeedAt
        Lifecycle.actualEventGame.source state
        (PurchasingPowerStandingAt.renewalEvent
          exitCapacityProgram.purchasingPowerStanding)) ∧
      exitCapacityProgram.payment.nextGenerated =
        PurchasingPowerStandingAt.nextGeneratedState
          exitCapacityProgram.purchasingPowerStanding :=
  ⟨exitCapacityProgram.payment_event_mem_source_trace,
    exitCapacityProgram.payment_next_is_exact_generated⟩

/-- A zero observer quote leaves both the price domain and exit capacity
inhabited; numeric zero is not price capture. -/
theorem zero_quote_does_not_erase_exit_capacity :
    openAZeroPrice.value = 0 ∧
      Nonempty (ExchangePriceObservationAt openZeroObserver) ∧
      Nonempty (ExitCapacityRenewalAt exitCapacityProgram) :=
  ⟨rfl, ⟨openAZeroPrice⟩, ⟨exitCapacityRenewal⟩⟩

theorem full_capture_is_nominal_and_excludes_exit :
    NominalTransferReadoutAt capturedProgram ∧
      IsEmpty (ExitCapacityRenewalAt capturedProgram) :=
  ⟨nominalTransfer, nominalTransfer.excludes_exitCapacityRenewal⟩

theorem captured_leave_points_to_exact_open_settlement :
    fullCapture.captureSettlement .leave rfl =
      exactOpenSettlement exactResidualActivation :=
  fullCapture.captureSettlement_eq .leave rfl

theorem jobGuarantee_empty_while_ubi_exit_survives :
    IsEmpty (JobGuaranteeStandingAt
      (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
      (game := Lifecycle.actualEventGame)
      (core := Lifecycle.Universal.FixedAdapter.core)
      (exitRelationCompiler := exitRelationCompiler) worker employmentRelation
      (exitRelationCompiler.roleAt employmentRelation .target)) ∧
      Nonempty (ExitCapacityRenewalAt exitCapacityProgram) :=
  ⟨noEmploymentTargetFuture_noJobGuarantee
      (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
      (game := Lifecycle.actualEventGame)
      (core := Lifecycle.Universal.FixedAdapter.core)
      (exitRelationCompiler := exitRelationCompiler) worker employmentRelation
      (exitRelationCompiler.roleAt employmentRelation .target)
      employment_target_future_empty,
    ⟨exitCapacityRenewal⟩⟩

/-- Reverse separation: an alternative source-generated job remains
actionable while complete capture eliminates the UBI outside option. -/
theorem jobGuarantee_survives_while_captured_ubi_fails :
    Nonempty NewJobGuaranteeStanding ∧
      IsEmpty (ExitCapacityRenewalAt capturedProgram) :=
  ⟨⟨jobGuaranteeStanding⟩,
    nominalTransfer.excludes_exitCapacityRenewal⟩

/-- The two support mechanisms are not definitionally exclusive: both can
coexist when the independent payment exit is uncaptured. -/
theorem ubi_and_jobGuarantee_can_coexist :
    Nonempty (ExitCapacityRenewalAt exitCapacityProgram) ∧
      Nonempty NewJobGuaranteeStanding :=
  ⟨⟨exitCapacityRenewal⟩, ⟨jobGuaranteeStanding⟩⟩

structure ExitCapacityRenewalCertificate where
  sourceBackedPayment :
    ∃ state ∈ Lifecycle.actualEventGame.occurrence.trace,
      residualConsumerCompiler.activationSeedAt
        Lifecycle.actualEventGame.source state
        (PurchasingPowerStandingAt.renewalEvent
          exitCapacityProgram.purchasingPowerStanding)
  generatedPaymentNext :
    exitCapacityProgram.payment.nextGenerated =
      PurchasingPowerStandingAt.nextGeneratedState
        exitCapacityProgram.purchasingPowerStanding
  workerSurvives : law.SurviveAt (sourceActor .s0) worker
  employmentLost : employmentLoss.power.freedomChange.kind = .lost
  supportRelationIndependent : employmentRelation ≠ independentExitRelation
  exitRenewal : ExitCapacityRenewalAt exitCapacityProgram
  strongestIff :
    Nonempty (ExitCapacityRenewalAt exitCapacityProgram) ↔
      ∃ code,
        code ∈ exitRelationCompiler.futureCodeCarrier ∧
        Nonempty (exitRelationCompiler.FutureContinuationAt
          independentExitRelation.1 .target code) ∧
        ¬ exitRelationCompiler.futureIdle code ∧
        ¬ noCapture.Captures code
  zeroQuoteStillPrice : openAZeroPrice.value = 0 ∧
    Nonempty (ExchangePriceObservationAt openZeroObserver)
  capturedNominal : NominalTransferReadoutAt capturedProgram
  capturedNoExit : IsEmpty (ExitCapacityRenewalAt capturedProgram)
  jobGuaranteeNoExit : IsEmpty (JobGuaranteeStandingAt
    (occurrenceOf := Lifecycle.actualEventOccurrenceOf)
    (game := Lifecycle.actualEventGame)
    (core := Lifecycle.Universal.FixedAdapter.core)
    (exitRelationCompiler := exitRelationCompiler) worker
    employmentRelation (exitRelationCompiler.roleAt employmentRelation .target))
  reverseSeparation : Nonempty NewJobGuaranteeStanding ∧
    IsEmpty (ExitCapacityRenewalAt capturedProgram)
  coexistence : Nonempty (ExitCapacityRenewalAt exitCapacityProgram) ∧
    Nonempty NewJobGuaranteeStanding

def exitCapacityRenewalDirectConsumer : ExitCapacityRenewalCertificate where
  sourceBackedPayment := payment_is_source_backed_and_generates_next.1
  generatedPaymentNext := payment_is_source_backed_and_generates_next.2
  workerSurvives := worker_is_surviving_target_actor.2
  employmentLost := exact_employment_relation_loss.1
  supportRelationIndependent := exact_employment_relation_loss.2.2
  exitRenewal := exitCapacityRenewal
  strongestIff := strongest_exitCapacityRenewal_iff
  zeroQuoteStillPrice :=
    ⟨zero_quote_does_not_erase_exit_capacity.1,
      zero_quote_does_not_erase_exit_capacity.2.1⟩
  capturedNominal := full_capture_is_nominal_and_excludes_exit.1
  capturedNoExit := full_capture_is_nominal_and_excludes_exit.2
  jobGuaranteeNoExit := jobGuarantee_empty_while_ubi_exit_survives.1
  reverseSeparation := jobGuarantee_survives_while_captured_ubi_fails
  coexistence := ubi_and_jobGuarantee_can_coexist

end
end M14ExitCapacityRenewalRegression
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ExitCapacityRenewalRegression.exitCapacityRenewalDirectConsumer
