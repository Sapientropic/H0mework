import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPrimitivePhysicalSourceAction.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPrimitivePhysicalSourceAction
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance primitivePhysicalCharacterComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)

def actualPrimitiveCharacterRead (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (kprice fprice forcingPrice kforcingPrice pairPrice siblingPrice:ℂ):ℂ:=
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
   T*W*A*OriginalKInsideDebtRSource.actualWavePaPairPrice observation nontrivial half h nonnegative bounded-
   A*star a*(T*W*(OriginalKPositionQuarterFTCAction.actualPositionQuarterPairPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterPairPrice observation nontrivial half h+star (OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h)*OriginalKQuarterTailPhysicalSource.actualQuarterTailPairPrice observation nontrivial half)+κ*D*star (kprice+fprice)))+
 star characterPrice*(star κ*W*(2*a)*siblingPrice+
   T*W*A*OriginalKInsideDebtRSource.actualWavePaSiblingPrice observation nontrivial half h nonnegative bounded+
   A*a*(T*W*(OriginalKPositionQuarterFTCAction.actualPositionQuarterSiblingPrice observation nontrivial half h+OriginalKFourierQuarterRplusAction.actualFourierQuarterSiblingPrice observation nontrivial half h+OriginalKInsideDebtRSource.actualPositionTailCoefficient observation nontrivial half h*OriginalKQuarterTailPhysicalSource.actualQuarterTailSiblingPrice observation nontrivial half)+star κ*star D*(kprice-fprice)))

def actualFinitePrimitiveCharacter (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 actualPrimitiveCharacterRead observation nontrivial half h nonnegative bounded
 (OriginalKCompleteMCofinalSource.actualFiniteKMeanDebtPrice c h n)
 (OriginalKFullKernelCofinalSource.actualDoubleFiniteFKMeanDebtPrice c h n)
 (OriginalKFourierForcingCofinalAction.actualFiniteFourierForcingPrice c h n)
 (actualFiniteKForcingPrice observation nontrivial half h n)
 (actualFinitePrimitivePairPrice observation nontrivial half h n)
 (actualFinitePrimitiveSiblingPrice observation nontrivial half h n)

def actualPrimitiveCharacterResidual (h:ℝ) (n:Nat):ℂ:=
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let W:=star D*D
 let κ:=Physical.actualResponseKappa c
 let w:=star κ*κ*W
 let kcost:=actualKForcingPriceResidual observation nontrivial half h n
 let paircost:=actualPrimitivePairPriceResidual observation nontrivial half h n
 let siblingcost:=actualPrimitiveSiblingPriceResidual observation nontrivial half h n
 w*χ*star a*star kcost-w*star χ*a*kcost-
 χ*κ*W*(2*star a)*paircost+star χ*star κ*W*(2*a)*siblingcost

/-- Existing whole-kappa character weights consume the actual generated primitive two-foot action and own K forcing source price; no new weight or kappa division is supplied. -/
theorem actual_current_primitive_character_residual (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 OriginalKFourierForcingCofinalAction.actualFiniteForcingCharacter observation nontrivial half h nonnegative bounded n-
 actualFinitePrimitiveCharacter observation nontrivial half h nonnegative bounded n=
 actualPrimitiveCharacterResidual observation nontrivial half h n :=by
 have k:=actual_original_K_Ward_finite_residual observation nontrivial half h n
 have primitive:=actual_original_primitive_two_price_residuals observation nontrivial half h n
 have originalK:OriginalKSourceScaledMaximalResponse.originalKForcingWard observation nontrivial half h=
  actualFiniteKForcingPrice observation nontrivial half h n+actualKForcingPriceResidual observation nontrivial half h n :=by
  linear_combination k
 have pair:star (Physical.actualResponseKappa c)*OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
  (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)=
  actualFinitePrimitivePairPrice observation nontrivial half h n+actualPrimitivePairPriceResidual observation nontrivial half h n :=by
  linear_combination primitive.1
 have sibling:Physical.actualResponseKappa c*OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
  (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)=
  actualFinitePrimitiveSiblingPrice observation nontrivial half h n+actualPrimitiveSiblingPriceResidual observation nontrivial half h n :=by
  linear_combination primitive.2
 have pairEffect:=congrArg (fun price:ℂ=>
  (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
   (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h))*
  Physical.actualResponseKappa c*(star (OriginalKCommonGapKernelSource.actualCommonDeterminant c)*OriginalKCommonGapKernelSource.actualCommonDeterminant c)*
  (2*star (OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h))*price) pair
 have siblingEffect:=congrArg (fun price:ℂ=>
  star (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h*
   (pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h))*
  star (Physical.actualResponseKappa c)*(star (OriginalKCommonGapKernelSource.actualCommonDeterminant c)*OriginalKCommonGapKernelSource.actualCommonDeterminant c)*
  (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*price) sibling
 unfold OriginalKFourierForcingCofinalAction.actualFiniteForcingCharacter
  OriginalKFourierForcingCofinalAction.actualForcingCharacterRead
 rw [originalK]
 unfold actualFinitePrimitiveCharacter actualPrimitiveCharacterRead actualPrimitiveCharacterResidual
 dsimp only
 simp only [star_add,star_mul,star_sub] at pairEffect siblingEffect ⊢
 linear_combination -pairEffect+siblingEffect

/-- The complete original independent character keeps all four same-source residues and its existing zero-kappa branch. -/
theorem actual_original_finite_primitive_character (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 OriginalKFullKernelCofinalSource.actualOriginalCharacterValue observation nontrivial half h=
 actualFinitePrimitiveCharacter observation nontrivial half h nonnegative bounded n+
 actualPrimitiveCharacterResidual observation nontrivial half h n+
 OriginalKFourierForcingCofinalAction.actualForcingCharacterResidual observation nontrivial half h n+
 OriginalKFullKernelCofinalSource.actualFourierDualCharacterResidual observation nontrivial half h n+
 OriginalKCompleteMCofinalSource.actualCharacterSourceResidual observation nontrivial half h n :=by
 have source:=OriginalKFourierForcingCofinalAction.actual_original_finite_forcing_character observation nontrivial half h nonnegative bounded n
 have actual:=actual_current_primitive_character_residual observation nontrivial half h nonnegative bounded n
 linear_combination source+actual

def actualPrimitiveCharacterError (h:ℝ) (n:Nat):ℝ:=
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let W:=star D*D
 let κ:=Physical.actualResponseKappa c
 let w:=star κ*κ*W
 (‖w*χ*star a‖+‖w*star χ*a‖)*OriginalKFourierForcingCofinalAction.actualFourierForcingPriceError c h n+
 ‖χ*κ*W*(2*star a)‖*(‖K c+Fphysical (K c)‖*actualPrimitiveActionError observation nontrivial half h n)+
 ‖star χ*star κ*W*(2*a)‖*(‖K c-Fphysical (K c)‖*actualPrimitiveActionError observation nontrivial half h n)

/-- The full original character source discrepancy pays the same K forcing and both complete primitive action feet, preserving its existing weights. -/
theorem actual_primitive_character_residual_error (h:ℝ) (n:Nat):
 ‖actualPrimitiveCharacterResidual observation nontrivial half h n‖≤actualPrimitiveCharacterError observation nontrivial half h n :=by
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let W:=star D*D
 let κ:=Physical.actualResponseKappa c
 let w:=star κ*κ*W
 let kcost:=actualKForcingPriceResidual observation nontrivial half h n
 let paircost:=actualPrimitivePairPriceResidual observation nontrivial half h n
 let siblingcost:=actualPrimitiveSiblingPriceResidual observation nontrivial half h n
 have k:=actual_K_forcing_price_residual_error observation nontrivial half h n
 have feet:=actual_original_primitive_two_price_errors observation nontrivial half h n
 have triangle:‖w*χ*star a*star kcost-w*star χ*a*kcost-χ*κ*W*(2*star a)*paircost+
  star χ*star κ*W*(2*a)*siblingcost‖≤
  ‖w*χ*star a*star kcost‖+‖w*star χ*a*kcost‖+
  ‖χ*κ*W*(2*star a)*paircost‖+‖star χ*star κ*W*(2*a)*siblingcost‖:=by
  calc
   _≤‖w*χ*star a*star kcost-w*star χ*a*kcost-χ*κ*W*(2*star a)*paircost‖+
      ‖star χ*star κ*W*(2*a)*siblingcost‖:=norm_add_le _ _
   _≤(‖w*χ*star a*star kcost-w*star χ*a*kcost‖+‖χ*κ*W*(2*star a)*paircost‖)+
      ‖star χ*star κ*W*(2*a)*siblingcost‖:=add_le_add (norm_sub_le _ _) le_rfl
   _≤_:=add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl

 change ‖w*χ*star a*star kcost-w*star χ*a*kcost-χ*κ*W*(2*star a)*paircost+
  star χ*star κ*W*(2*a)*siblingcost‖≤
  (‖w*χ*star a‖+‖w*star χ*a‖)*OriginalKFourierForcingCofinalAction.actualFourierForcingPriceError c h n+
  ‖χ*κ*W*(2*star a)‖*(‖K c+Fphysical (K c)‖*actualPrimitiveActionError observation nontrivial half h n)+
  ‖star χ*star κ*W*(2*a)‖*(‖K c-Fphysical (K c)‖*actualPrimitiveActionError observation nontrivial half h n)
 refine triangle.trans ?_
 simp only [norm_mul,norm_star]
 have kfirst:=mul_le_mul_of_nonneg_left k (norm_nonneg (w*χ*star a))
 have ksecond:=mul_le_mul_of_nonneg_left k (norm_nonneg (w*star χ*a))
 have pair:=mul_le_mul_of_nonneg_left feet.1 (norm_nonneg (χ*κ*W*(2*star a)))
 have sibling:=mul_le_mul_of_nonneg_left feet.2 (norm_nonneg (star χ*star κ*W*(2*a)))
 simpa only [norm_mul,norm_star,add_mul] using add_le_add (add_le_add (add_le_add kfirst ksecond) pair) sibling

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPrimitivePhysicalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
