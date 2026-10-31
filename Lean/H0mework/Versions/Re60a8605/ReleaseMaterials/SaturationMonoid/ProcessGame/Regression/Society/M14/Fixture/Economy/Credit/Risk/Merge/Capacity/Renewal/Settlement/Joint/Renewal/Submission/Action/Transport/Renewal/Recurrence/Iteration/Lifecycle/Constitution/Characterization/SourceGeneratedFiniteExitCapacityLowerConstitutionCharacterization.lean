import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Producer.SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch

/-!
# Source-generated finite exit-capacity lower constitution

The full paid-exit lifecycle maximum is already forced by its local
actionable-renewal contract.  The reverse direction regenerates the existing
root-temporal chain at the contract's code; it does not accept that chain or
call the canonical lifecycle-maximum producer.

The cycle specialization only reindexes this characterization by the paid
replay physically carried by the generated recurrence node.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedFiniteExitCapacityLowerConstitutionCharacterization

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Power Exchange Settlement Price Money UBI
open Renewal Capacity Space CrossingCost
open UBI.Capacity UBI.Capacity.SourceOwnedExitGeometryCompilerAt
open M14UBIExitCapacityFixture
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedPaidSuccessorBearerRoleIndependentContinuation
open M14SourceGeneratedPaidExitLifecycleTemporalSpine
open M14SourceGeneratedPaidExitLifecycleMaximumCharacterization
open M14SourceGeneratedProofCarryingPaidExitLifecycleMaximum
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch

/-- Strong lower constitutional characterization.  Unlike the older maximum
contract, the right side does not ask the caller for the root-temporal chain.
The unique viable continuation code transports the independently generated
chain to the operational renewal selected by the contract. -/
theorem paidExitLifecycleMaximum_nonempty_iff_actionableRenewalContract
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Nonempty
        (ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex index) ↔
      PaidExitLifecycleActionableRenewalContractAt oldVisit sourceIndex
        index := by
  constructor
  · rintro ⟨lifecycle⟩
    exact
      (installedActionableRenewal_iff_fullContract oldVisit sourceIndex
        index).mp ⟨lifecycle.actionableRenewal⟩
  · rintro
      ⟨code, slot, inCarrier, future, nonIdle, uncaptured, payment, route⟩
    have code_eq_leave : code = ExitFutureCode.leave := by
      cases code with
      | idle => exact False.elim (nonIdle rfl)
      | work =>
          rcases future with ⟨continuation⟩
          exact nomatch continuation
      | leave => rfl
    have action_eq_leave :
        (paidExitLifecycleContinuationAt oldVisit sourceIndex index
          ).successorContinuationAction.1 = ExitFutureCode.leave := by
      rw [(paidExitLifecycleContinuationAt oldVisit sourceIndex index
        ).successorContinuationAction_eq_canonical]
      rfl
    have code_eq_action :
        code =
          (paidExitLifecycleContinuationAt oldVisit sourceIndex index
            ).successorContinuationAction.1 :=
      code_eq_leave.trans action_eq_leave.symm
    have rooted :
        PaidExitLifecycleRootTemporalAt oldVisit sourceIndex index code := by
      rw [code_eq_action]
      exact paidExitLifecycleRootTemporalAt oldVisit sourceIndex index
    exact
      (ProofCarryingPaidExitLifecycleMaximumAt.nonempty_iff_maximumContract
        oldVisit sourceIndex index).mpr
          ⟨code, slot, inCarrier, future, nonIdle, uncaptured, payment, route,
            rooted⟩

/-- The same lower constitution at the exact paid-replay index carried by one
generated finite self-U8 cycle. -/
theorem cyclePaidExitLifecycleMaximum_nonempty_iff_actionableRenewalContract
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    Nonempty
        (ProofCarryingPaidExitLifecycleMaximumAt oldVisit sourceIndex
          (cycleLifecycleIndex initial depth)) ↔
      PaidExitLifecycleActionableRenewalContractAt oldVisit sourceIndex
        (cycleLifecycleIndex initial depth) :=
  paidExitLifecycleMaximum_nonempty_iff_actionableRenewalContract oldVisit
    sourceIndex (cycleLifecycleIndex initial depth)

/-- Forgetting payment/route/service incidence from the operational contract
still produces the semantic exit-capacity renewal at the very same code. -/
theorem actionableRenewalContract_generates_semanticExitCapacityRenewal
    (oldVisit : OldVisit) (sourceIndex index : Nat)
    (contract :
      PaidExitLifecycleActionableRenewalContractAt oldVisit sourceIndex
        index) :
    ∃ operational :
        (birthBearerGeometryCompilerAt
          (paidExitLifecycleSuccessorDepthAt oldVisit sourceIndex index)
        ).SourceGeneratedActionableExitRenewalAt,
      ∃ semantic : ExitCapacityRenewalAt birthBearerExitCapacityProgram,
        semantic.exit.1 = operational.code := by
  rcases
      (installedActionableRenewal_iff_fullContract oldVisit sourceIndex
        index).mpr contract with
    ⟨operational⟩
  let semantic : ExitCapacityRenewalAt birthBearerExitCapacityProgram :=
    ExitCapacityRenewalAt.generate
      ⟨operational.code, operational.feasible.codeSurvives⟩
  exact ⟨operational, semantic, rfl⟩

end
end M14SourceGeneratedFiniteExitCapacityLowerConstitutionCharacterization
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedFiniteExitCapacityLowerConstitutionCharacterization.paidExitLifecycleMaximum_nonempty_iff_actionableRenewalContract
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedFiniteExitCapacityLowerConstitutionCharacterization.cyclePaidExitLifecycleMaximum_nonempty_iff_actionableRenewalContract
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedFiniteExitCapacityLowerConstitutionCharacterization.actionableRenewalContract_generates_semanticExitCapacityRenewal
