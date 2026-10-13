import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJordanExteriorSourceAction.FiniteField
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanExteriorSourceAction
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
export OriginalKFourierKernelDependentRAction (actualNativeKernelCoefficient actualWholeSingleReturn)
end Native

local instance exteriorPriceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualExteriorSourcePrice (h shift : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let z:=(OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 actualProtectedBandPrice (star z) shift Fphysical+
 actualBeyondBandPrice z shift Fphysical-
 inner ℂ (actualTwoRadiusFiniteField z shift) (Fphysical : BurnolL2)

/-- Native source qualifications pay these two rates; no target price or nonzero constructor is added. -/
theorem actual_native_exterior_source_price (h shift : ℝ) (nonnegative : 0≤shift) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let z:=(OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value/2
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 inner ℂ (Source.actualJordanSeedExterior z) (Fphysical : BurnolL2)=
 actualExteriorSourcePrice observation nontrivial half h shift :=by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 have right:1/4<z.re:=by
  dsimp only [z]
  rw [Complex.div_re];norm_num;linarith [dual.rightHalf]
 have first:z≠0:=by
  intro bad
  rw [bad] at right
  norm_num at right
 have second:z-1/2≠0:=by
  intro bad
  have real:=congrArg Complex.re bad
  dsimp only [z] at real
  rw [Complex.sub_re,Complex.div_re] at real
  norm_num at real
  linarith [dual.belowOne]
 exact actual_original_exterior_generated_price z right first second shift nonnegative _

def actualExteriorGeneratedFKMeanPrice (h shift : ℝ) : ℂ :=
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let dual:=OriginalKQuarterTailPhysicalSource.actualStarSource coordinate
 let z:=dual.value/2
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let Fphysical:=evenFaceFourierEquiv burnolUnscaledCommonGapRadius material
 star (Native.actualNativeKernelCoefficient coordinate)*
 (-(coordinate.value-1)/2*
    (star (1/z^2)*(1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)+
      actualExteriorSourcePrice observation nontrivial half h shift)+
  (2/(coordinate.value-1):ℂ)*
    (star (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization coordinate)*
      inner ℂ (burnolCompletedMellinRieszVector coordinate) Fphysical+
      (1/2:ℂ)*Paid.actualMean (Fphysical : BurnolL2)))+
 OriginalKCompactAdjointRSource.actualCompactFourierResponsePrice coordinate
   (Native.actualWholeSingleReturn coordinate) material

/-- The original FK consumer reads the source-generated finite field and complete tail. -/
theorem actual_generated_exterior_FK_price (h shift : ℝ) (nonnegative : 0≤shift) :
 OriginalKJordanSeedFieldSource.actualJordanSeedFKMeanPrice observation nontrivial half h=
 actualExteriorGeneratedFKMeanPrice observation nontrivial half h shift :=by
 have price:=actual_native_exterior_source_price observation nontrivial half h shift nonnegative
 dsimp only at price
 unfold OriginalKJordanSeedFieldSource.actualJordanSeedFKMeanPrice actualExteriorGeneratedFKMeanPrice
 dsimp only
 rw [price]

/-- Original character actually consumes the whole-source seed response. -/
theorem actual_exterior_action_priced_character_source (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) (shift : ℝ) (shiftNonnegative : 0≤shift) :
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
   A*star a*(OriginalKPositionQuarterFTCAction.actualPositionQuarterPairPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterPairPrice observation nontrivial half h+star (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h)*OriginalKQuarterTailPhysicalSource.actualQuarterTailPairPrice observation nontrivial half+star (OriginalKConstantSeedWholeRAction.actualWholeSeedPricedKMeanRPrice observation nontrivial half h+actualExteriorGeneratedFKMeanPrice observation nontrivial half h shift)))+
 star characterPrice*((2*a)*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
   A*OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded+
   A*a*(OriginalKPositionQuarterFTCAction.actualPositionQuarterSiblingPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterSiblingPrice observation nontrivial half h+OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*OriginalKQuarterTailPhysicalSource.actualQuarterTailSiblingPrice observation nontrivial half+(OriginalKConstantSeedWholeRAction.actualWholeSeedPricedKMeanRPrice observation nontrivial half h-actualExteriorGeneratedFKMeanPrice observation nontrivial half h shift))) :=by
 have source:=OriginalKJordanSeedFieldSource.actual_jordan_seed_source_priced_character_source observation nontrivial half h nonnegative bounded
 dsimp only at source ⊢
 rw [actual_generated_exterior_FK_price observation nontrivial half h shift shiftNonnegative] at source
 exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKJordanExteriorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
