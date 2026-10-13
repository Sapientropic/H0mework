import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJordanSeedFieldSource.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanSeedFieldSource
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







namespace Native
export OriginalKFourierKernelDependentRAction (actualNativeKernelCoefficient actualWholeSingleReturn actualResonantFKMeanPrice actual_resonant_native_field_price actual_resonant_FK_mean_price)
end Native

local instance jordanSeedPriceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualJordanSeedFKMeanPrice (h : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 star (Native.actualNativeKernelCoefficient coordinate)*
 (-(coordinate.value-1)/2*
    (star (1/z^2)*(1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)+
      inner ℂ (actualJordanSeedExterior z) (Fphysical : BurnolL2))+
  (2/(coordinate.value-1):ℂ)*
    (star (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate)*
      inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
      (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)))+
 OriginalKCompactAdjointRSource.actualCompactFourierResponsePrice coordinate
   (Native.actualWholeSingleReturn coordinate) material

/-- The original FK field consumes the generated exact quarter plus retained exterior, using the actual receiver Fourier face. -/
theorem actual_jordan_seed_FK_mean_price (h : ℝ) :
 Native.actualResonantFKMeanPrice observation nontrivial half h=
 actualJordanSeedFKMeanPrice observation nontrivial half h :=by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 have qualified : 1/4<(dual.value/2).re :=by
  rw [Complex.div_re];norm_num;linarith [dual.rightHalf]
 unfold Native.actualResonantFKMeanPrice actualJordanSeedFKMeanPrice
 dsimp only
 have whole:=Native.actual_resonant_native_field_price coordinate material
 have jPrice:=actual_jordan_seed_physical_price (dual.value/2) qualified Fphysical
 change inner ℂ (J.actualResonantField (dual.value/2) J.seed) (fourierL2 (material : BurnolL2))=
   star (1/(dual.value/2)^2)*(1/2:ℂ)*Paid.actualMean (fourierL2 (material : BurnolL2))+
   inner ℂ (actualJordanSeedExterior (dual.value/2)) (fourierL2 (material : BurnolL2)) at jPrice
 rw [whole,jPrice]
 rfl

/-- Original character actually consumes the whole-source seed response. -/
theorem actual_jordan_seed_source_priced_character_source (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
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
   A*star a*(OriginalKPositionQuarterFTCAction.actualPositionQuarterPairPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterPairPrice observation nontrivial half h+star (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h)*OriginalKQuarterTailPhysicalSource.actualQuarterTailPairPrice observation nontrivial half+star (OriginalKConstantSeedWholeRAction.actualWholeSeedPricedKMeanRPrice observation nontrivial half h+actualJordanSeedFKMeanPrice observation nontrivial half h)))+
 star characterPrice*((2*a)*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
   A*OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded+
   A*a*(OriginalKPositionQuarterFTCAction.actualPositionQuarterSiblingPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterSiblingPrice observation nontrivial half h+OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*OriginalKQuarterTailPhysicalSource.actualQuarterTailSiblingPrice observation nontrivial half+(OriginalKConstantSeedWholeRAction.actualWholeSeedPricedKMeanRPrice observation nontrivial half h-actualJordanSeedFKMeanPrice observation nontrivial half h))) :=by
 have source:=OriginalKFourierKernelDependentRAction.actual_resonant_source_priced_character_source observation nontrivial half h nonnegative bounded
 dsimp only at source ⊢
 rw [actual_jordan_seed_FK_mean_price] at source
 exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanSeedFieldSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
