import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.DepthZero.Consumer.ProofCarryingContributionCapacityDepthZeroU8NoFreeReceipt
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Payment.Action.Consumer.ProofCarryingContributionMergeCrossRootPayment
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Payment.Action.Cut.Consumer.ProofCarryingContributionCapacityCutCrossRootPayment
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Assembly.ProofCarryingContributionCapacityDepthThreeToTwelveNoFreeRuntime

/-!
# Complete named depth-zero-to-twelve no-free runtime

This is a Prop product of the existing branch-specific receipts.  It does not
encode a future schedule, create a branch enum, or store a second runtime.
Together the four fields cover the thirteen already generated canonical
ticks `0 ... 12`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingContributionCapacityDepthZeroToTwelveNoFreeRuntime

open M14ProofCarryingContributionCapacityDepthZeroU8NoFreeReceipt
open M14ProofCarryingContributionMergeCrossRootPayment
open M14ProofCarryingContributionCapacityCutCrossRootPayment
open M14ProofCarryingContributionCapacityDepthThreeToTwelveNoFreeRuntime

structure ProofCarryingContributionCapacityDepthZeroToTwelveNoFreeRuntime : Prop where
  depthZeroU8 :
    ProofCarryingContributionCapacityDepthZeroU8NoFreeReceipt
  depthOneMerge : ProofCarryingContributionMergeCrossRootPayment
  depthTwoCapacityCut :
    ProofCarryingContributionCapacityCutCrossRootPayment
  depthThreeToTwelve :
    ProofCarryingContributionCapacityDepthThreeToTwelveNoFreeRuntime

theorem proofCarryingContributionCapacityDepthZeroToTwelveNoFreeRuntime :
    ProofCarryingContributionCapacityDepthZeroToTwelveNoFreeRuntime where
  depthZeroU8 :=
    proofCarryingContributionCapacityDepthZeroU8NoFreeReceipt
  depthOneMerge := proofCarryingContributionMergeCrossRootPayment
  depthTwoCapacityCut :=
    proofCarryingContributionCapacityCutCrossRootPayment
  depthThreeToTwelve :=
    proofCarryingContributionCapacityDepthThreeToTwelveNoFreeRuntime

end M14ProofCarryingContributionCapacityDepthZeroToTwelveNoFreeRuntime
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingContributionCapacityDepthZeroToTwelveNoFreeRuntime.proofCarryingContributionCapacityDepthZeroToTwelveNoFreeRuntime
