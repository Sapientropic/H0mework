import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.DepthZero.Producer.SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Runtime.SourceGeneratedContributionMergeSupportSeparation

/-!
# Direct consumer of the depth-zero U8 no-free receipt

The canonical first tick consumes the one fixed receipt.  Its old-root micro
current cannot replace the revised-world macro next, and no isolated Unit,
root event, U8 core or row answer can retype as the complete receipt.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityDepthZeroU8NoFreeReceipt

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M9ProofCarryingRenewalInquiryRuntime
open M9ProofCarryingRenewalU8Revision
open M13SelfU8Regression
open M14SourceGeneratedContributionMergeSupportSeparation
open M14SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt
open M14SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt.SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt

abbrev CanonicalDepthZeroU8NoFreeReceipt :=
  SourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt

theorem depthZero_resolution_exact :
    firstTick.resolution =
      .revised RootInquiryU8CompletionRegression.obstruction
        RootInquiryU8CompletionRegression.u7Gate
        RootInquiryU8CompletionRegression.failure jointCore :=
  firstTick_resolution_is_jointCore

@[simp] theorem depthZero_runtimeNextEngine_exact :
    (jointRuntime.stateAt 1).engine = firstTick.next :=
  rfl

theorem depthZero_macroNext_exact :
    sourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt.nextPaidBy =
      (processPresentation .contributionMergeAction).erase :=
  sourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt.nextPaidBy_exact

/-- The source micro current lives in the original network while the paid U8
receipt lands in the revised network. -/
theorem depthZero_sourceMicroNetwork_ne_macroNetwork :
    OriginalN ≠ RevisedN :=
  originalNetwork_ne_revisedNetwork

theorem bareUnit_event_core_orAnswer_cannot_retype_asDepthZeroReceipt : True := by
  fail_if_success
    exact (PUnit.unit : CanonicalDepthZeroU8NoFreeReceipt)
  fail_if_success
    exact (firstTick.receipt.1 : CanonicalDepthZeroU8NoFreeReceipt)
  fail_if_success
    exact (jointCore : CanonicalDepthZeroU8NoFreeReceipt)
  fail_if_success
    exact (firstTick.receipt.2.2.1 : CanonicalDepthZeroU8NoFreeReceipt)
  fail_if_success
    exact (firstTick.receipt.2.2.2 : CanonicalDepthZeroU8NoFreeReceipt)
  trivial

structure ProofCarryingContributionCapacityDepthZeroU8NoFreeReceipt : Prop where
  receipt : CanonicalDepthZeroU8NoFreeReceipt
  resolutionExact :
    firstTick.resolution =
      .revised RootInquiryU8CompletionRegression.obstruction
        RootInquiryU8CompletionRegression.u7Gate
        RootInquiryU8CompletionRegression.failure jointCore
  runtimeNextEngineExact :
    (jointRuntime.stateAt 1).engine = firstTick.next
  macroNextExact :
    receipt.nextPaidBy =
      (processPresentation .contributionMergeAction).erase
  sourceMicroAndMacroNetworksDistinct : OriginalN ≠ RevisedN

theorem proofCarryingContributionCapacityDepthZeroU8NoFreeReceipt :
    ProofCarryingContributionCapacityDepthZeroU8NoFreeReceipt where
  receipt := sourceGeneratedContributionCapacityDepthZeroU8NoFreeReceipt
  resolutionExact := depthZero_resolution_exact
  runtimeNextEngineExact := depthZero_runtimeNextEngine_exact
  macroNextExact := depthZero_macroNext_exact
  sourceMicroAndMacroNetworksDistinct :=
    depthZero_sourceMicroNetwork_ne_macroNetwork

end
end M14ProofCarryingContributionCapacityDepthZeroU8NoFreeReceipt
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityDepthZeroU8NoFreeReceipt.proofCarryingContributionCapacityDepthZeroU8NoFreeReceipt
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityDepthZeroU8NoFreeReceipt.depthZero_macroNext_exact
