import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Lifecycle.Characterization.SourceGeneratedPaidExitLifecycleTemporalSpine

/-!
# Nontrivial maximum characterization of the paid-exit lifecycle

The left side is the existing, genuinely nullable actionable-renewal fibre.
The right side joins its full payment/route/service contract to the independent
four-occurrence root-temporal spine.  This module does not import or call the
canonical maximum producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPaidExitLifecycleMaximumCharacterization

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M10OccurrenceCapacityDebitedRunFixture
open M14UBIExitCapacityFixture
open M14UBIProofCarryingRootRestriction
open M14UBIPeriodicActualServiceCapacity
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
open M14SourceGeneratedPaidExitLifecycleTemporalSpine

abbrev PaidExitLifecycleActionableRenewalContractAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Prop :=
  ∃ (code : birthBearerExitRelationCompiler.FutureCode)
    (slot : Fin
      (anomiePhaseAt
        (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
      ).served.length),
    code ∈ birthBearerExitRelationCompiler.futureCodeCarrier ∧
    Nonempty (birthBearerExitRelationCompiler.FutureContinuationAt
      birthBearerIndependentExitRelation.1 .target code) ∧
    ¬ birthBearerExitRelationCompiler.futureIdle code ∧
    ¬ birthBearerNoCapture.Captures code ∧
    Nonempty (SourceBackedUBIPaymentReceiptAt
      birthBearerExitCapacityProgram.purchasingPowerStanding code) ∧
    Nonempty (SourceGeneratedUBIRouteReceiptAt code
      (ExactServedCrossingDebitedRunAt.servicedCrossingAt
        (phase := anomiePhaseAt
          (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index))
        (crossingCompiler := crossingCompilerAt
          (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index))
        slot))

abbrev PaidExitLifecycleMaximumContractAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Prop :=
  ∃ (code : birthBearerExitRelationCompiler.FutureCode)
    (slot : Fin
      (anomiePhaseAt
        (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
      ).served.length),
    code ∈ birthBearerExitRelationCompiler.futureCodeCarrier ∧
    Nonempty (birthBearerExitRelationCompiler.FutureContinuationAt
      birthBearerIndependentExitRelation.1 .target code) ∧
    ¬ birthBearerExitRelationCompiler.futureIdle code ∧
    ¬ birthBearerNoCapture.Captures code ∧
    Nonempty (SourceBackedUBIPaymentReceiptAt
      birthBearerExitCapacityProgram.purchasingPowerStanding code) ∧
    Nonempty (SourceGeneratedUBIRouteReceiptAt code
      (ExactServedCrossingDebitedRunAt.servicedCrossingAt
        (phase := anomiePhaseAt
          (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index))
        (crossingCompiler := crossingCompilerAt
          (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index))
        slot)) ∧
    PaidExitLifecycleRootTemporalAt oldVisit sourceIndex index code

abbrev PaidExitLifecycleFullCaptureContractAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Prop :=
  ∃ (code : birthBearerExitRelationCompiler.FutureCode)
    (slot : Fin
      (anomiePhaseAt
        (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
      ).served.length),
    code ∈ birthBearerExitRelationCompiler.futureCodeCarrier ∧
    Nonempty (birthBearerExitRelationCompiler.FutureContinuationAt
      birthBearerIndependentExitRelation.1 .target code) ∧
    ¬ birthBearerExitRelationCompiler.futureIdle code ∧
    ¬ birthBearerFullCapture.Captures code ∧
    Nonempty (SourceBackedUBIPaymentReceiptAt
      birthBearerCapturedProgram.purchasingPowerStanding code) ∧
    Nonempty (SourceGeneratedUBIRouteReceiptAt code
      (ExactServedCrossingDebitedRunAt.servicedCrossingAt
        (phase := anomiePhaseAt
          (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index))
        (crossingCompiler := crossingCompilerAt
          (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index))
        slot))

private theorem code_eq_lifecycleAction
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (code : birthBearerExitRelationCompiler.FutureCode)
    (continuation : Nonempty
      (birthBearerExitRelationCompiler.FutureContinuationAt
        birthBearerIndependentExitRelation.1 .target code))
    (nonIdle : ¬ birthBearerExitRelationCompiler.futureIdle code) :
    code =
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorContinuationAction.1 := by
  have code_eq_leave : code = ExitFutureCode.leave := by
    cases code with
    | idle => exact False.elim (nonIdle rfl)
    | work => exact nomatch Classical.choice continuation
    | leave => rfl
  have action_eq_leave :
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorContinuationAction.1 = ExitFutureCode.leave := by
    rw [(paidExitLifecycleContinuationAt oldVisit sourceIndex index
      ).successorContinuationAction_eq_canonical]
    rfl
  exact code_eq_leave.trans action_eq_leave.symm

/-- Independent local characterization of the genuinely nullable semantic
mouth.  Root-temporal authority is deliberately absent here and is joined only
by the typed maximum carrier. -/
theorem installedActionableRenewal_iff_fullContract
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Nonempty
        (birthBearerGeometryCompilerAt
          (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
        ).SourceGeneratedActionableExitRenewalAt ↔
      PaidExitLifecycleActionableRenewalContractAt oldVisit sourceIndex index := by
  let depth := paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index
  exact
    (birthBearerGeometryCompilerAt depth
      ).actionableExitRenewal_nonempty_iff_full_contract

/-- The same rooted temporal chain remains present under the replacement
compiler, but its full-capture contract is empty. -/
theorem fullCaptureActionableRenewal_iff_fullContract
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Nonempty
        (birthBearerCapturedGeometryCompilerAt
          (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
        ).SourceGeneratedActionableExitRenewalAt ↔
      PaidExitLifecycleFullCaptureContractAt oldVisit sourceIndex index := by
  let depth := paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index
  exact
    (birthBearerCapturedGeometryCompilerAt depth
      ).actionableExitRenewal_nonempty_iff_full_contract

theorem paidExitLifecycleFullCaptureContract_isFalse
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ¬ PaidExitLifecycleFullCaptureContractAt oldVisit sourceIndex index := by
  rintro
    ⟨code, _slot, _inCarrier, future, nonIdle, uncaptured, _payment, _route⟩
  have codeExact := code_eq_lifecycleAction oldVisit sourceIndex index code
    future nonIdle
  apply uncaptured
  rw [codeExact]
  change
    (paidExitLifecycleContinuationAt oldVisit sourceIndex index
      ).successorContinuationAction.1 = ExitFutureCode.leave
  exact
    (congrArg (fun action => action.1)
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorContinuationAction_eq_canonical).trans
      birthBearerExitExerciseAction_code_exact

theorem paidExitLifecycleFullCaptureRenewal_isEmpty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    IsEmpty
      (birthBearerCapturedGeometryCompilerAt
        (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
      ).SourceGeneratedActionableExitRenewalAt :=
  ⟨fun renewal =>
    paidExitLifecycleFullCaptureContract_isFalse oldVisit sourceIndex index
      ((fullCaptureActionableRenewal_iff_fullContract oldVisit sourceIndex index).mp
        ⟨renewal⟩)⟩

end
end M14SourceGeneratedPaidExitLifecycleMaximumCharacterization
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidExitLifecycleMaximumCharacterization.installedActionableRenewal_iff_fullContract
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPaidExitLifecycleMaximumCharacterization.paidExitLifecycleFullCaptureRenewal_isEmpty
