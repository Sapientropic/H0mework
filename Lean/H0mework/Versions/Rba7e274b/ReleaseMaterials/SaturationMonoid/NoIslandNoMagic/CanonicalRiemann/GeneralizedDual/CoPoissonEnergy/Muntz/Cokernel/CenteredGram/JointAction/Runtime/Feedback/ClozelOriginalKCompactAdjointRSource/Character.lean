import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactAdjointRSource.Columns
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactAdjointRSource
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)



def actualCompactPricedKMeanRPrice (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half (material : BurnolL2)
 let A:=star (OriginalRieszSource.Kernel.A coordinate)
 let b:=star (OriginalRieszSource.Kernel.beta coordinate)
 (A*actualCompactFourierResponsePrice coordinate OriginalRieszSource.Response.wholeU material-
 b*actualCompactFourierResponsePrice coordinate OriginalRieszSource.Response.wholeV material-
 coordinate.value*A*((1/2:ℂ)*OriginalKGapMeanRSourceAction.actualMeanGram observation nontrivial half h/(coordinate.value/2))+
 (1-coordinate.value)*b*inner ℂ (fourierL2 OriginalKConstantContactSourceAction.ConstantSource.seed) acted-
 (2:ℂ)*OriginalKConstantContactSourceAction.actualConstantContactMeanInputPrice observation nontrivial half h)/(2*coordinate.value-1)

/-- Actual compact adjoint/rank/FTC prices are consumed in the original unweighted K action. -/
theorem actual_source_column_priced_K_mean (h : ℝ) :
 OriginalKConstantContactSourceAction.actualConstantContactMeanKPrice observation nontrivial half h=
 actualCompactPricedKMeanRPrice observation nontrivial half h := by
 have generated:=actual_original_UV_F_R_source_prices observation nontrivial half h
 dsimp only at generated
 unfold OriginalKConstantContactSourceAction.actualConstantContactMeanKPrice actualCompactPricedKMeanRPrice
 dsimp only
 rw [generated.1,generated.2]

/-- Same original character consumes the complete source-generated compact-column response. -/
theorem actual_compact_source_priced_character_source (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 A*OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h=
 characterPrice*star a*star
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h+
    OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h)-
 star characterPrice*a*
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h-
    OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h)-
 characterPrice*((2*star a)*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)-
   A*OriginalKInsideDebtRSource.actualWavePaPairPrice observation nontrivial half h nonnegative bounded-
   A*star a*(OriginalKPositionQuarterFTCAction.actualPositionQuarterPairPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterPairPrice observation nontrivial half h+star (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h)*OriginalKQuarterTailPhysicalSource.actualQuarterTailPairPrice observation nontrivial half+star (actualCompactPricedKMeanRPrice observation nontrivial half h+inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)) (OriginalKFullSourceRResponse.Op.R observation nontrivial half (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)))))+
 star characterPrice*((2*a)*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
   A*OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded+
   A*a*(OriginalKPositionQuarterFTCAction.actualPositionQuarterSiblingPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterSiblingPrice observation nontrivial half h+OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*OriginalKQuarterTailPhysicalSource.actualQuarterTailSiblingPrice observation nontrivial half+(actualCompactPricedKMeanRPrice observation nontrivial half h-inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)) (OriginalKFullSourceRResponse.Op.R observation nontrivial half (OriginalKGapMeanRSourceAction.Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2))))) := by
 have source:=OriginalKConstantContactSourceAction.actual_constant_contact_priced_character_source observation nontrivial half h nonnegative bounded
 dsimp only at source ⊢
 rw [actual_source_column_priced_K_mean] at source
 exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompactAdjointRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
