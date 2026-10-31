import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Necessity.Lifecycle.Characterization.SourceGeneratedPaidExitLifecycleMaximumCharacterization

/-!
# Source-generated proof-carrying paid-exit lifecycle maximum

The carrier owns one existing, genuinely nullable actionable-renewal witness
and the independent root-temporal composite indexed by that witness's code.
It stores none of the five predecessor certificates: those are recovered from
the canonical final disposition along the existing dependency chain.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum

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
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedPaidExitLifecycleMaximumCharacterization

/-- The maximum carrier is not a sealed token: its mouth is the existing
actionable-renewal semantic fibre. -/
structure ProofCarryingPaidExitLifecycleMaximumAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) : Type 32 where
  private mk ::
  actionableRenewal :
    (birthBearerGeometryCompilerAt
      (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
    ).SourceGeneratedActionableExitRenewalAt
  rooted : PaidExitLifecycleRootTemporalAt oldVisit sourceIndex index
    actionableRenewal.code

namespace ProofCarryingPaidExitLifecycleMaximumAt

variable {oldVisit : OldVisit} {sourceIndex index : Nat}
  (lifecycle : ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
    index)

include lifecycle

def continuation
    (_lifecycle : ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
      index) :=
  paidExitLifecycleContinuationAt oldVisit sourceIndex index

def disposition
    (_lifecycle : ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
      index) :=
  paidExitLifecycleDispositionAt oldVisit sourceIndex index

theorem code_eq_continuationAction :
    lifecycle.actionableRenewal.code =
      lifecycle.continuation.successorContinuationAction.1 :=
  lifecycle.rooted.roleIndependentContinuation.codeExact

theorem exactThreePaidSuccessorEdges :
    HEq
        (paidExitLifecycleStandingRenewalAt oldVisit sourceIndex index
          ).sourcePayment.nextPaidBy
        (paidExitLifecycleStandingRenewalAt oldVisit sourceIndex index
          ).targetConsequence.outerRootEvent.occurrence ∧
      HEq lifecycle.continuation.executedPayment.nextPaidBy
        lifecycle.continuation.successorRootEvent.occurrence ∧
      HEq lifecycle.continuation.successorPayment.nextPaidBy
        (paidExitLifecycleFurtherPaidStepAt oldVisit sourceIndex index
          ).targetRootEvent.occurrence :=
  ⟨lifecycle.rooted.occurrenceSpine.firstPaidNext,
    lifecycle.rooted.occurrenceSpine.secondPaidNext,
    lifecycle.rooted.occurrenceSpine.thirdPaidNext⟩

theorem everyDistinctStage_sameAction_differentAuthorityAndK :
    ∀ left right : PaidExitLifecycleStage, left ≠ right →
      paidExitLifecycleActionReadoutAt oldVisit sourceIndex index left =
          paidExitLifecycleActionReadoutAt oldVisit sourceIndex index right ∧
        paidExitLifecycleOuterAuthorityAt oldVisit sourceIndex index left ≠
          paidExitLifecycleOuterAuthorityAt oldVisit sourceIndex index right ∧
        paidExitLifecycleActualServiceKAt oldVisit sourceIndex index left ≠
          paidExitLifecycleActualServiceKAt oldVisit sourceIndex index right := by
  intro left right distinct
  exact
    ⟨(lifecycle.rooted.actionReadoutConstant left).trans
        (lifecycle.rooted.actionReadoutConstant right).symm,
      fun equality => distinct
        (lifecycle.rooted.outerAuthorityInjective equality),
      fun equality => distinct
        (lifecycle.rooted.actualServiceKInjective equality)⟩

theorem maximumContract :
    PaidExitLifecycleMaximumContractAt oldVisit sourceIndex index := by
  let renewal := lifecycle.actionableRenewal
  have generated :=
    (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
      birthBearerNoCapture birthBearerIndependentExitRelation renewal.code).mp
      renewal.feasible.codeSurvives
  exact
    ⟨renewal.code, renewal.slot, generated.1, generated.2.1,
      generated.2.2.1, generated.2.2.2,
      ⟨renewal.feasible.paymentReceipt⟩,
      ⟨renewal.feasible.routeReceipt⟩,
      lifecycle.rooted⟩

omit lifecycle

/-- The typed maximum is equivalent to the independently stated full
contract.  The reverse direction rebuilds the semantic renewal and then the
carrier; it never calls the canonical producer below. -/
theorem nonempty_iff_maximumContract
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Nonempty
        (ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex index) ↔
      PaidExitLifecycleMaximumContractAt oldVisit sourceIndex index := by
  let depth := paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index
  constructor
  · rintro ⟨lifecycle⟩
    exact lifecycle.maximumContract
  · rintro
      ⟨code, slot, inCarrier, future, nonIdle, uncaptured, ⟨payment⟩,
        ⟨route⟩, rooted⟩
    have codeSurvives :
        code ∈ birthBearerExitCapacityProgram.exitCone.survivingCodes :=
      (SourceOwnedPriceCaptureCompilerAt.mem_survivingExitCodes_iff
        birthBearerNoCapture birthBearerIndependentExitRelation code).mpr
        ⟨inCarrier, future, nonIdle, uncaptured⟩
    let feasible : ExactFeasibleExitEdgeAt
        (birthBearerGeometryCompilerAt depth) code slot :=
      FeasibleExitEdgeAt.generate
        (actualSettlement := actualSettlementAt depth) codeSurvives payment route
    let renewal :
        (birthBearerGeometryCompilerAt depth
          ).SourceGeneratedActionableExitRenewalAt :=
      { code := code
        slot := slot
        feasible := feasible }
    exact ⟨{ actionableRenewal := renewal, rooted := rooted }⟩

include lifecycle

theorem proofCarryingPaidExitLifecycleMaximum_exact :
    PaidExitLifecycleMaximumContractAt oldVisit sourceIndex index ∧
      PaidExitLifecycleOccurrenceSpineAt oldVisit sourceIndex index ∧
      PaidExitLifecycleResponseExecutionAt oldVisit sourceIndex index ∧
      PaidExitLifecycleRoleIndependentContinuationAt oldVisit sourceIndex index
        lifecycle.actionableRenewal.code ∧
      PaidExitLifecycleExternalDispositionAt oldVisit sourceIndex index ∧
      PaidExitLifecycleServicesAndFutureAt oldVisit sourceIndex index ∧
      IsEmpty
        (birthBearerCapturedGeometryCompilerAt
          (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
        ).SourceGeneratedActionableExitRenewalAt :=
  ⟨lifecycle.maximumContract,
    lifecycle.rooted.occurrenceSpine,
    lifecycle.rooted.responseExecution,
    lifecycle.rooted.roleIndependentContinuation,
    lifecycle.rooted.externalDisposition,
    lifecycle.rooted.servicesAndFuture,
    paidExitLifecycleFullCaptureRenewal_isEmpty oldVisit sourceIndex index⟩

end ProofCarryingPaidExitLifecycleMaximumAt

def sourceGeneratedProofCarryingPaidExitLifecycleMaximumAt
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex index := by
  let depth := paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index
  let renewal := birthBearerActionableExitRenewalAt depth
  have actionCodeExact : renewal.code =
      (paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorContinuationAction.1 := by
    change ExitFutureCode.leave = _
    symm
    exact
      (congrArg (fun action => action.1)
        (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).successorContinuationAction_eq_canonical).trans
        birthBearerExitExerciseAction_code_exact
  have rooted :
      PaidExitLifecycleRootTemporalAt oldVisit sourceIndex index renewal.code := by
    rw [actionCodeExact]
    exact paidExitLifecycleRootTemporalAt oldVisit sourceIndex index
  exact { actionableRenewal := renewal, rooted := rooted }

theorem sourceGeneratedProofCarryingPaidExitLifecycleMaximum_hasNoCallerPayload
    (oldVisit : OldVisit) (sourceIndex index : Nat) : True := by
  let lifecycle :=
    sourceGeneratedProofCarryingPaidExitLifecycleMaximumAt oldVisit
      sourceIndex index
  fail_if_success exact lifecycle.payment
  fail_if_success exact lifecycle.action
  fail_if_success exact lifecycle.liability
  fail_if_success exact lifecycle.consumer
  fail_if_success exact lifecycle.registry
  fail_if_success exact lifecycle.history
  trivial

end
end M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum.sourceGeneratedProofCarryingPaidExitLifecycleMaximumAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum.ProofCarryingPaidExitLifecycleMaximumAt.nonempty_iff_maximumContract
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum.ProofCarryingPaidExitLifecycleMaximumAt.proofCarryingPaidExitLifecycleMaximum_exact
