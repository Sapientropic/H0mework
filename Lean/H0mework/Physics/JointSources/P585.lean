import H0mework.Physics.AlphaSources.P581
import H0mework.Physics.YukawaSources.P584

/-!
# Proposition 585: the three main producer nails as one receipt

This file is an indexing / closure layer, not a new physical derivation.  It
collects the three narrow producer debts currently being attacked:

1. the `alpha_s` inverse residual target `-89000/128511`, supplied by the
   finite SU(7)-breaking alpha-gap producer from P581;
2. the nine Yukawa integer depths, supplied by the carrier-card stencil from
   P584 and carried by the selected SU(7) discrete seed from P583;
3. the CKM/Jarlskog depth sum `386`, read from the same stencil.

Keeping these as one receipt prevents the Standard-Model projection track from
turning into another flat list of numerological-looking facts.  The remaining
producer debt is exactly the hard physics/representation statement: why the
SU(7) breaking dynamics, threshold/RG corrections, and consolidation order
select these finite producers.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-- The exact nine-depth target, in the mass-order display used by the
verification harness and P582-P584. -/
def mainYukawaDepthTarget : List Nat :=
  [50, 346, 372, 489, 583, 682, 880, 908, 982]

/-- THEOREM 1: the carrier-card stencil gives exactly the main nine-depth
target. -/
theorem mainYukawaDepthTarget_from_stencil :
    [ (yukawaDepthStencilOf .top).toNat
    , (yukawaDepthStencilOf .bottom).toNat
    , (yukawaDepthStencilOf .tau).toNat
    , (yukawaDepthStencilOf .charm).toNat
    , (yukawaDepthStencilOf .muon).toNat
    , (yukawaDepthStencilOf .strange).toNat
    , (yukawaDepthStencilOf .down).toNat
    , (yukawaDepthStencilOf .up).toNat
    , (yukawaDepthStencilOf .electron).toNat
    ] = mainYukawaDepthTarget := by
  exact yukawaDepthStencil_massOrder_eq

/-- THEOREM 2: the selected SU(7) seed carries exactly the same main nine-depth
target. -/
theorem mainYukawaDepthTarget_from_selectedSeed :
    [ selectedDiscreteStandardModelSeed.su7.yukawaDepth .top
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .bottom
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .tau
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .charm
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .muon
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .strange
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .down
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .up
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .electron
    ] = mainYukawaDepthTarget := by
  norm_num [mainYukawaDepthTarget, selectedDiscreteStandardModelSeed,
    selectedSU7DiscreteConsolidationData, selectedYukawaIntegerDepth]

/-- THEOREM 3: the SU(7)-breaking residual producer gives the exact inverse
correction target `-89000/128511`. -/
theorem mainAlphaStrongResidualTarget_from_su7Breaking :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongSU7BreakingResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511) := by
  rw [alphaStrongSU7BreakingResidualGapProducer_inverseCorrection]
  exact alphaStrongResidualInverseCorrectionNeeded_eq ℚ

/-- THEOREM 4: the CKM/Jarlskog depth sum is read from the carrier-card
stencil and is the P278 sum `386`. -/
theorem mainCKMDepthSum_from_stencil :
    (yukawaDepthStencilOf .strange -
        yukawaDepthStencilOf .up) +
      (yukawaDepthStencilOf .bottom -
        yukawaDepthStencilOf .charm) +
      (yukawaDepthStencilOf .up -
        yukawaDepthStencilOf .bottom) +
      (yukawaDepthStencilOf .strange -
        yukawaDepthStencilOf .charm) =
        (386 : Int) := by
  rw [ckmDepthSum_fromStencil_eq_386]
  rfl

/-- A compact certificate for the three current producer nails. -/
structure StandardModelThreeProducerNailReceipt where
  alpha_s :
    AlphaStrongSU7BreakingProducerReceipt
  yukawa_depths :
    YukawaDepthCarrierStencilReceipt
  selected_seed_depths :
    [ selectedDiscreteStandardModelSeed.su7.yukawaDepth .top
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .bottom
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .tau
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .charm
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .muon
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .strange
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .down
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .up
    , selectedDiscreteStandardModelSeed.su7.yukawaDepth .electron
    ] = mainYukawaDepthTarget
  alpha_inverse_target :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        alphaStrongSU7BreakingResidualGapProducer.producedGap =
      -((89000 : ℚ) / 128511)
  ckm_depth_sum :
    (yukawaDepthStencilOf .strange -
        yukawaDepthStencilOf .up) +
      (yukawaDepthStencilOf .bottom -
        yukawaDepthStencilOf .charm) +
      (yukawaDepthStencilOf .up -
        yukawaDepthStencilOf .bottom) +
      (yukawaDepthStencilOf .strange -
        yukawaDepthStencilOf .charm) =
        (386 : Int)

/-- THEOREM 5: the current three-nail producer receipt. -/
theorem standardModelThreeProducerNailReceipt :
    StandardModelThreeProducerNailReceipt where
  alpha_s := alphaStrongSU7BreakingProducerReceipt
  yukawa_depths := yukawaDepthCarrierStencilReceipt
  selected_seed_depths := mainYukawaDepthTarget_from_selectedSeed
  alpha_inverse_target := mainAlphaStrongResidualTarget_from_su7Breaking
  ckm_depth_sum := mainCKMDepthSum_from_stencil

end StandardModelConstraint
end SaturationMonoid
