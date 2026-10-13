import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteMCofinalSource.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMCofinalSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance cofinalMCharacterPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualCharacterSourceRead (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (kprice fprice:ℂ):ℂ:=
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 let W:=star D*D
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
 let T:=star κ*κ
 T*W*characterPrice*star a*star
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h+
    OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h)-
 T*W*star characterPrice*a*
   (OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h-
    OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h)-
 characterPrice*(T*W*(2*star a)*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)-
   T*W*A*OriginalKInsideDebtRSource.actualWavePaPairPrice observation nontrivial half h nonnegative bounded-
   A*star a*(T*W*(OriginalKPositionQuarterFTCAction.actualPositionQuarterPairPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterPairPrice observation nontrivial half h+star (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h)*OriginalKQuarterTailPhysicalSource.actualQuarterTailPairPrice observation nontrivial half)+κ*D*star (kprice+fprice)))+
 star characterPrice*(T*W*(2*a)*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)+
   T*W*A*OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded+
   A*a*(T*W*(OriginalKPositionQuarterFTCAction.actualPositionQuarterSiblingPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterSiblingPrice observation nontrivial half h+OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*OriginalKQuarterTailPhysicalSource.actualQuarterTailSiblingPrice observation nontrivial half)+star κ*star D*(kprice-fprice)))

def actualFiniteSourceCharacter (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 actualCharacterSourceRead observation nontrivial half h nonnegative bounded
 (actualFiniteKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n)
 (actualFiniteFKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n)

def actualCharacterSourceResidual (h:ℝ) (n:Nat):ℂ:=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let κD:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let kcost:=κD*actualMSourceTateResidual c h n*actualMSourceKResponsePrice c
 let fcost:=κD*actualMSourceTateResidual c h n*actualMSourceFKResponsePrice c
 characterPrice*A*star a*κD*star (kcost+fcost)+
 star characterPrice*A*a*star κD*(kcost-fcost)

/-- The independent original character consumes the actual finite complete M producer and its source-generated residual on both own physical feet. -/
theorem actual_original_finite_source_character (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c
 (star κ*κ)*(star D*D)*(OriginalKSourceScaledMaximalResponse.Return.sourceA observation*
  OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h)=
 actualFiniteSourceCharacter observation nontrivial half h nonnegative bounded n+
 actualCharacterSourceResidual observation nontrivial half h n :=by
 have source:=OriginalKGapKernelGreenSource.actual_original_Green_two_mean_character observation nontrivial half h nonnegative bounded
 have prices:=actual_complete_M_finite_price_residuals (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n
 unfold actualMSourceWeight at prices
 have first:OriginalKGapKernelGreenSource.actualGreenKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h=
  actualFiniteKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n+
  (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)*
   OriginalKCommonGapKernelSource.actualCommonDeterminant (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))*
  actualMSourceTateResidual (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n*
  actualMSourceKResponsePrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) :=by
  linear_combination prices.1
 have second:OriginalKGapKernelGreenSource.actualGreenFKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h=
  actualFiniteFKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n+
  (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)*
   OriginalKCommonGapKernelSource.actualCommonDeterminant (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))*
  actualMSourceTateResidual (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n*
  actualMSourceFKResponsePrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) :=by
  linear_combination prices.2
 dsimp only at source ⊢
 rw [first,second] at source
 rw [source]
 unfold actualFiniteSourceCharacter actualCharacterSourceRead actualCharacterSourceResidual
 dsimp only
 simp only [star_add,star_mul,star_sub]
 ring

/-- The exact character residual carries the same source geometry and its two own response factors. -/
theorem actual_character_source_residual_bound (h:ℝ) (n:Nat) :
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let characterPrice:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let weight:=actualMSourceWeight c
 ‖actualCharacterSourceResidual observation nontrivial half h n‖≤
 (2*‖characterPrice‖*‖A‖*‖a‖*‖weight‖^2*
  (‖actualMSourceKResponsePrice c‖+‖actualMSourceFKResponsePrice c‖))*‖actualMSourceRead c h‖*
 ((1/4:ℝ)^n*((4/3:ℝ)*‖OriginalRieszSource.Response.eta‖)) :=by
 dsimp only
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let w:=actualMSourceWeight c
 let r:=actualMSourceTateResidual c h n
 have addBound:‖w*r*actualMSourceKResponsePrice c+w*r*actualMSourceFKResponsePrice c‖≤
  ‖w‖*‖r‖*(‖actualMSourceKResponsePrice c‖+‖actualMSourceFKResponsePrice c‖) :=by
  exact (norm_add_le _ _).trans_eq (by rw [norm_mul,norm_mul,norm_mul,norm_mul];ring)
 have subBound:‖w*r*actualMSourceKResponsePrice c-w*r*actualMSourceFKResponsePrice c‖≤
  ‖w‖*‖r‖*(‖actualMSourceKResponsePrice c‖+‖actualMSourceFKResponsePrice c‖) :=by
  exact (norm_sub_le _ _).trans_eq (by rw [norm_mul,norm_mul,norm_mul,norm_mul];ring)
 have literal:actualCharacterSourceResidual observation nontrivial half h n=
  χ*A*star a*w*star (w*r*actualMSourceKResponsePrice c+w*r*actualMSourceFKResponsePrice c)+
  star χ*A*a*star w*(w*r*actualMSourceKResponsePrice c-w*r*actualMSourceFKResponsePrice c) :=rfl
 rw [literal]
 calc
  _≤‖χ*A*star a*w*star (w*r*actualMSourceKResponsePrice c+w*r*actualMSourceFKResponsePrice c)‖+
    ‖star χ*A*a*star w*(w*r*actualMSourceKResponsePrice c-w*r*actualMSourceFKResponsePrice c)‖ :=norm_add_le _ _
  _≤2*‖χ‖*‖A‖*‖a‖*‖w‖^2*(‖actualMSourceKResponsePrice c‖+‖actualMSourceFKResponsePrice c‖)*‖r‖ :=by
   simp only [norm_mul,norm_star]
   have first:=mul_le_mul_of_nonneg_left addBound
    (show 0≤‖χ‖*‖A‖*‖a‖*‖w‖ by positivity)
   have second:=mul_le_mul_of_nonneg_left subBound
    (show 0≤‖χ‖*‖A‖*‖a‖*‖w‖ by positivity)
   exact (add_le_add first second).trans_eq (by ring)
  _≤_ :=by
   have source:=mul_le_mul_of_nonneg_left (actual_complete_M_source_error c h n)
    (show 0≤2*‖χ‖*‖A‖*‖a‖*‖w‖^2*(‖actualMSourceKResponsePrice c‖+‖actualMSourceFKResponsePrice c‖) by positivity)
   exact source.trans_eq (by ring)

/-- The independent character consumes both complete M source closures, retaining its original weights and all other inventories. -/
theorem actual_complete_source_character_tendsto (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2):
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c
 Tendsto (actualFiniteSourceCharacter observation nontrivial half h nonnegative bounded) atTop
  (𝓝 ((star κ*κ)*(star D*D)*(OriginalKSourceScaledMaximalResponse.Return.sourceA observation*
   OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h))) :=by
 have prices:=actual_complete_M_finite_prices_tendsto (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h
 have target:=OriginalKGapKernelGreenSource.actual_original_Green_two_mean_character observation nontrivial half h nonnegative bounded
 dsimp only at target ⊢
 rw [target]
 have reader:Continuous (fun (value : Prod ℂ ℂ)=>
  actualCharacterSourceRead observation nontrivial half h nonnegative bounded value.1 value.2) :=by
  unfold actualCharacterSourceRead
  dsimp only
  fun_prop
 have generated:=(reader.tendsto _).comp (prices.1.prodMk_nhds prices.2)
 exact generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMCofinalSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
