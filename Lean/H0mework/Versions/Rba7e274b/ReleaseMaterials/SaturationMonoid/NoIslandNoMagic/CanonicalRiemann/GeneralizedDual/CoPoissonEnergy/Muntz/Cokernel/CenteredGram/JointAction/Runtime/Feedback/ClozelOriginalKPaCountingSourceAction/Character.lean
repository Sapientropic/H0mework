import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCountingSourceAction.Price
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCountingSourceAction
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance paCountingCharacterComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)

def actualPaCountingCharacterRead (h:ℝ) (_nonnegative:0≤h) (_bounded:h≤Real.log 2) (kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice wavePairPrice waveSiblingPrice:ℂ):ℂ:=
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 let W:=star D*D
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 let T:=star κ*κ
 T*W*characterPrice*star a*star
   (kforcingPrice+
    forcingPrice)-
 T*W*star characterPrice*a*
   (kforcingPrice-
    forcingPrice)-
 characterPrice*(κ*W*(2*star a)*pairPrice-
   T*W*A*wavePairPrice-
   A*star a*(T*W*(OriginalKPositionQuarterFTCAction.actualPositionQuarterPairPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterPairPrice observation nontrivial half h+star (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h)*OriginalKQuarterTailPhysicalSource.actualQuarterTailPairPrice observation nontrivial half)+κ*D*star (kprice+fprice)))+
 star characterPrice*(star κ*W*(2*a)*siblingPrice+
   T*W*A*waveSiblingPrice+
   A*a*(T*W*(OriginalKPositionQuarterFTCAction.actualPositionQuarterSiblingPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterSiblingPrice observation nontrivial half h+OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*OriginalKQuarterTailPhysicalSource.actualQuarterTailSiblingPrice observation nontrivial half)+star κ*star D*(kprice-fprice)))

def actualFinitePaCountingCharacter (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 actualPaCountingCharacterRead observation nontrivial half h nonnegative bounded
 (OriginalKCompleteMCofinalSource.actualFiniteKMeanDebtPrice c h n)
 (OriginalKFullKernelCofinalSource.actualDoubleFiniteFKMeanDebtPrice c h n)
 (OriginalKFourierForcingCofinalAction.actualFiniteFourierForcingPrice c h n)
 (OriginalKPrimitivePhysicalSourceAction.actualFiniteKForcingPrice observation nontrivial half h n)
 (OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitivePairPrice observation nontrivial half h n)
 (OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitiveSiblingPrice observation nontrivial half h n)
 (actualFiniteWavePairPrice observation nontrivial half h nonnegative bounded n)
 (actualFiniteWaveSiblingPrice observation nontrivial half h nonnegative bounded n)

def actualPaCountingCharacterResidual (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c
 let w:=(star κ*κ)*(star D*D)
 χ*w*A*actualWavePairPriceResidual observation nontrivial half h nonnegative bounded n+
 star χ*w*A*actualWaveSiblingPriceResidual observation nontrivial half h nonnegative bounded n

/-- The complete current character body consumes actual original PaWave R/Q counting source prices and their own origin material, preserving every prior source field. -/
theorem actual_current_Pa_counting_character_residual (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitiveCharacter observation nontrivial half h nonnegative bounded n-
 actualFinitePaCountingCharacter observation nontrivial half h nonnegative bounded n=
 actualPaCountingCharacterResidual observation nontrivial half h nonnegative bounded n :=by
 have price:=actual_original_wave_counting_two_price_residuals observation nontrivial half h nonnegative bounded n
 have pair:OriginalKInsideDebtRSource.actualWavePaPairPrice observation nontrivial half h nonnegative bounded=
  actualFiniteWavePairPrice observation nontrivial half h nonnegative bounded n+
  actualWavePairPriceResidual observation nontrivial half h nonnegative bounded n :=by
  linear_combination price.1
 have sibling:OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded=
  actualFiniteWaveSiblingPrice observation nontrivial half h nonnegative bounded n+
  actualWaveSiblingPriceResidual observation nontrivial half h nonnegative bounded n :=by
  linear_combination price.2
 unfold OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitiveCharacter
  OriginalKPrimitivePhysicalSourceAction.actualPrimitiveCharacterRead
 rw [pair,sibling]
 unfold actualFinitePaCountingCharacter actualPaCountingCharacterRead actualPaCountingCharacterResidual
 dsimp only
 ring

/-- The independent original character retains all five exact same-source residuals and the whole original source/native inventory. -/
theorem actual_original_finite_Pa_counting_character (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 OriginalKFullKernelCofinalSource.actualOriginalCharacterValue observation nontrivial half h=
 actualFinitePaCountingCharacter observation nontrivial half h nonnegative bounded n+
 actualPaCountingCharacterResidual observation nontrivial half h nonnegative bounded n+
 OriginalKPrimitivePhysicalSourceAction.actualPrimitiveCharacterResidual observation nontrivial half h n+
 OriginalKFourierForcingCofinalAction.actualForcingCharacterResidual observation nontrivial half h n+
 OriginalKFullKernelCofinalSource.actualFourierDualCharacterResidual observation nontrivial half h n+
 OriginalKCompleteMCofinalSource.actualCharacterSourceResidual observation nontrivial half h n :=by
 have source:=OriginalKPrimitivePhysicalSourceAction.actual_original_finite_primitive_character observation nontrivial half h nonnegative bounded n
 have effect:=actual_current_Pa_counting_character_residual observation nontrivial half h nonnegative bounded n
 linear_combination source+effect

def actualPaCountingCharacterError (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℝ:=
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c
 let w:=(star κ*κ)*(star D*D)
 (‖χ*w*A‖*‖K c+Fphysical (K c)‖+‖star χ*w*A‖*‖K c-Fphysical (K c)‖)*
 actualPaCountingResponseError c (actualWaveSource observation nontrivial half h nonnegative bounded) n

/-- The character's own source error is paid from both complete Pa R/Q feet and the actual counting origin error. -/
theorem actual_Pa_counting_character_residual_error (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 ‖actualPaCountingCharacterResidual observation nontrivial half h nonnegative bounded n‖≤
 actualPaCountingCharacterError observation nontrivial half h nonnegative bounded n :=by
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c
 let w:=(star κ*κ)*(star D*D)
 have costs:=actual_original_wave_counting_two_price_errors observation nontrivial half h nonnegative bounded n
 have literal:actualPaCountingCharacterResidual observation nontrivial half h nonnegative bounded n=
  χ*w*A*actualWavePairPriceResidual observation nontrivial half h nonnegative bounded n+
  star χ*w*A*actualWaveSiblingPriceResidual observation nontrivial half h nonnegative bounded n:=rfl
 rw [literal]
 change ‖χ*w*A*actualWavePairPriceResidual observation nontrivial half h nonnegative bounded n+
  star χ*w*A*actualWaveSiblingPriceResidual observation nontrivial half h nonnegative bounded n‖≤
  (‖χ*w*A‖*‖K c+Fphysical (K c)‖+‖star χ*w*A‖*‖K c-Fphysical (K c)‖)*
  actualPaCountingResponseError c (actualWaveSource observation nontrivial half h nonnegative bounded) n
 calc
  _≤‖χ*w*A*actualWavePairPriceResidual observation nontrivial half h nonnegative bounded n‖+
     ‖star χ*w*A*actualWaveSiblingPriceResidual observation nontrivial half h nonnegative bounded n‖:=norm_add_le _ _
  _≤_:=by
   simp only [norm_mul]
   have first:=mul_le_mul_of_nonneg_left costs.1 (norm_nonneg (χ*w*A))
   have second:=mul_le_mul_of_nonneg_left costs.2 (norm_nonneg (star χ*w*A))
   simpa only [norm_mul,add_mul,mul_assoc] using add_le_add first second

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCountingSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
