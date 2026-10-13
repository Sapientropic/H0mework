import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullKernelCofinalSource.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullKernelCofinalSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance kernelCofinalCharacterPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)

def actualDoubleFiniteSourceCharacter (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):ℂ:=
 OriginalKCompleteMCofinalSource.actualCharacterSourceRead observation nontrivial half h nonnegative bounded
  (CurrentM.actualFiniteKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n)
  (actualDoubleFiniteFKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n)

def actualFourierDualCharacterResidual (h:ℝ) (n:Nat):ℂ:=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let w:=CurrentM.actualMSourceWeight c
 let cost:=w*actualFiniteFourierDualPriceRead c h n*actualFourierDualSourceResidual c n
 χ*A*star a*w*star cost-star χ*A*a*star w*cost

/-- The current original character consumes the true finite FourierDual effect on its FK price slot, retaining both same-source residues in its complete body. -/
theorem actual_original_double_finite_source_character (h:ℝ) (nonnegative:0≤h) (bounded:h≤Real.log 2) (n:Nat):
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let D:=OriginalKCommonGapKernelSource.actualCommonDeterminant c
 let κ:=OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c
 (star κ*κ)*(star D*D)*(OriginalKSourceScaledMaximalResponse.Return.sourceA observation*
  OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h)=
 actualDoubleFiniteSourceCharacter observation nontrivial half h nonnegative bounded n+
 actualFourierDualCharacterResidual observation nontrivial half h n+
 OriginalKCompleteMCofinalSource.actualCharacterSourceResidual observation nontrivial half h n :=by
 have source:=OriginalKCompleteMCofinalSource.actual_original_finite_source_character observation nontrivial half h nonnegative bounded n
 have price:=actual_complete_M_Fourier_dual_finite_residual (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n
 have generated:CurrentM.actualFiniteFKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n=
  actualDoubleFiniteFKMeanDebtPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n+
  CurrentM.actualMSourceWeight (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)*
  actualFiniteFourierDualPriceRead (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n*
  actualFourierDualSourceResidual (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) n :=by
  linear_combination price
 dsimp only at source ⊢
 rw [source]
 unfold OriginalKCompleteMCofinalSource.actualFiniteSourceCharacter
 rw [generated]
 unfold actualDoubleFiniteSourceCharacter OriginalKCompleteMCofinalSource.actualCharacterSourceRead actualFourierDualCharacterResidual
 dsimp only
 unfold CurrentM.actualMSourceWeight
 simp only [star_mul,star_add,star_sub]
 ring

/-- The character's new FourierDual discrepancy is paid by the actual current finite M read and two whole source errors. -/
theorem actual_Fourier_dual_character_residual_error (h:ℝ) (n:Nat):
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let w:=CurrentM.actualMSourceWeight c
 ‖actualFourierDualCharacterResidual observation nontrivial half h n‖≤
 2*‖χ‖*‖A‖*‖a‖*‖w‖^2*‖actualFiniteFourierDualPriceRead c h n‖*actualFourierDualSourceError c n :=by
 dsimp only
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let a:=OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h
 let A:=OriginalKSourceScaledMaximalResponse.Return.sourceA observation
 let χ:=2*a*(pairedMellinTranslationCharacter observation.coordinate h-pairedMellinTranslationCharacter (star observation.coordinate) h)
 let w:=CurrentM.actualMSourceWeight c
 let cost:=w*actualFiniteFourierDualPriceRead c h n*actualFourierDualSourceResidual c n
 have error:‖cost‖≤‖w‖*‖actualFiniteFourierDualPriceRead c h n‖*actualFourierDualSourceError c n :=by
  have source:=actual_original_Fourier_dual_source_error c n
  rw [actual_original_Fourier_dual_source_residual] at source
  simpa only [cost,norm_mul] using mul_le_mul_of_nonneg_left source
   (show 0≤‖w‖*‖actualFiniteFourierDualPriceRead c h n‖ by positivity)
 have literal:actualFourierDualCharacterResidual observation nontrivial half h n=
  χ*A*star a*w*star cost-star χ*A*a*star w*cost :=rfl
 rw [literal]
 change ‖χ*A*star a*w*star cost-star χ*A*a*star w*cost‖≤
  2*‖χ‖*‖A‖*‖a‖*‖w‖^2*‖actualFiniteFourierDualPriceRead c h n‖*actualFourierDualSourceError c n
 calc
  _≤‖χ*A*star a*w*star cost‖+‖star χ*A*a*star w*cost‖ :=norm_sub_le _ _
  _≤_ :=by
   simp only [norm_mul,norm_star]
   have paid:=mul_le_mul_of_nonneg_left error
    (show 0≤‖χ‖*‖A‖*‖a‖*‖w‖ by positivity)
   exact (add_le_add paid paid).trans_eq (by ring)


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullKernelCofinalSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
