import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierForcingCofinalAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierForcingCofinalAction
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance forcingCofinalCharacterPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)

def actualForcingCharacterRead (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (kprice fprice forcingPrice:ℂ):ℂ:=
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 let W:=star D*D
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 let T:=star κ*κ
 T*W*characterPrice*star a*star
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h+
    forcingPrice)-
 T*W*star characterPrice*a*
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h-
    forcingPrice)-
 characterPrice*(T*W*(2*star a)*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)-
   T*W*A*OriginalKInsideDebtRSource.actualWavePaPairPrice observation nontrivial half h nonnegative bounded-
   A*star a*(T*W*(OriginalKPositionQuarterFTCAction.actualPositionQuarterPairPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterPairPrice observation nontrivial half h+star (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h)*OriginalKQuarterTailPhysicalSource.actualQuarterTailPairPrice observation nontrivial half)+κ*D*star (kprice+fprice)))+
 star characterPrice*(T*W*(2*a)*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
   T*W*A*OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded+
   A*a*(T*W*(OriginalKPositionQuarterFTCAction.actualPositionQuarterSiblingPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterSiblingPrice observation nontrivial half h+OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*OriginalKQuarterTailPhysicalSource.actualQuarterTailSiblingPrice observation nontrivial half)+star κ*star D*(kprice-fprice)))

def actualFiniteForcingCharacter (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 actualForcingCharacterRead observation nontrivial half h nonnegative bounded
 (OriginalKCompleteMCofinalSource.actualFiniteKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n)
 (OriginalKFullKernelCofinalSource.actualDoubleFiniteFKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n)
 (actualFiniteFourierForcingPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n)

def actualForcingCharacterResidual (h:ℝ) (n:Nat):ℂ:=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c
 let w:=(star κ*κ)*(star D*D)
 let cost:=actualFourierForcingPriceResidual c h n
 w*χ*star a*star cost+w*star χ*a*cost

/-- The complete current character body consumes the actual original forcing action field, with its own same-source discrepancy. -/
theorem actual_current_forcing_character_residual (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 OriginalKFullKernelCofinalSource.actualDoubleFiniteSourceCharacter observation nontrivial half h nonnegative bounded n-
 actualFiniteForcingCharacter observation nontrivial half h nonnegative bounded n=
 actualForcingCharacterResidual observation nontrivial half h n :=by
 have price:=actual_original_FK_Ward_finite_residual observation nontrivial half h n
 have generated:OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h=
  actualFiniteFourierForcingPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n+
  actualFourierForcingPriceResidual (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n :=by
  linear_combination price
 unfold OriginalKFullKernelCofinalSource.actualDoubleFiniteSourceCharacter
  OriginalKCompleteMCofinalSource.actualCharacterSourceRead
 rw [generated]
 unfold actualFiniteForcingCharacter actualForcingCharacterRead actualForcingCharacterResidual
 dsimp only
 simp only [star_add,star_mul]
 ring

/-- The independent original source character preserves both earlier source residues and the complete forcing action residual. -/
theorem actual_original_finite_forcing_character (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 OriginalKFullKernelCofinalSource.actualOriginalCharacterValue observation nontrivial half h=
 actualFiniteForcingCharacter observation nontrivial half h nonnegative bounded n+
 actualForcingCharacterResidual observation nontrivial half h n+
 OriginalKFullKernelCofinalSource.actualFourierDualCharacterResidual observation nontrivial half h n+
 OriginalKCompleteMCofinalSource.actualCharacterSourceResidual observation nontrivial half h n :=by
 have source:=OriginalKFullKernelCofinalSource.actual_original_double_finite_source_character observation nontrivial half h nonnegative bounded n
 have generated:=actual_current_forcing_character_residual observation nontrivial half h nonnegative bounded n
 dsimp only at source
 change OriginalKFullKernelCofinalSource.actualOriginalCharacterValue observation nontrivial half h=_ at source
 linear_combination source+generated

/-- The complete forcing character discrepancy carries only its actual source-action and whole-material costs. -/
theorem actual_forcing_character_residual_error (h:ℝ) (n:Nat):
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c
 let w:=(star κ*κ)*(star D*D)
 ‖actualForcingCharacterResidual observation nontrivial half h n‖≤
 2*‖w‖*‖χ‖*‖a‖*actualFourierForcingPriceError c h n :=by
 dsimp only
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c
 let w:=(star κ*κ)*(star D*D)
 let cost:=actualFourierForcingPriceResidual c h n
 have source:=actual_original_Fourier_forcing_price_error c h n
 rw [actual_original_Fourier_forcing_price_residual] at source
 change ‖w*χ*star a*star cost+w*star χ*a*cost‖≤2*‖w‖*‖χ‖*‖a‖*actualFourierForcingPriceError c h n
 calc
  _≤‖w*χ*star a*star cost‖+‖w*star χ*a*cost‖:=norm_add_le _ _
  _≤_:=by
   simp only [norm_mul,norm_star]
   have paid:=mul_le_mul_of_nonneg_left source (show 0≤‖w‖*‖χ‖*‖a‖ by positivity)
   exact (add_le_add paid paid).trans_eq (by ring)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierForcingCofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
