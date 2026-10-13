import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierForcingCofinalAction.Source
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
local instance forcingCofinalEffectPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


def actualForcingAction (c:BurnolCompletedMellinCoordinate) (h:ℝ):BurnolL2→L[ℂ]BurnolL2:=
 (2:ℂ) • (pairedBurnolMultiplicativeDilation h-
  pairedMellinTranslationCharacter (star c.value) h • ContinuousLinearMap.id ℂ BurnolL2)

def actualForcingFieldError (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℝ:=
 ‖actualForcingAction c h‖*Paid.actualWholeKernelSourceError c n

/-- The actual source update operates on the full ambient residual; its own action norm pays the full forcing-field error. -/
theorem actual_original_forcing_field_error (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):
 ‖OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h)-
 actualFiniteForcingField c h n‖≤actualForcingFieldError c h n :=by
 rw [actual_original_forcing_field_residual]
 change ‖actualForcingAction c h (Paid.actualWholeKernelSourceResidual c n)‖≤_
 have source:=Paid.actual_original_whole_kernel_source_error c n
 rw [Paid.actual_original_whole_kernel_source_residual] at source
 exact ((actualForcingAction c h).le_opNorm _).trans
  (mul_le_mul_of_nonneg_left source (norm_nonneg _))

theorem actual_forcing_field_error_tendsto (c:BurnolCompletedMellinCoordinate) (h:ℝ):
 Tendsto (actualForcingFieldError c h) atTop (𝓝 0) :=by
 unfold actualForcingFieldError
 simpa only [mul_zero] using (Paid.actual_whole_kernel_error_tendsto c).const_mul ‖actualForcingAction c h‖

def actualFiniteFourierForcingPrice (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℂ:=
 inner ℂ (fourierL2 (Paid.actualFiniteWholeKernelSource c n)) (actualFiniteForcingField c h n)

def actualFourierForcingPriceResidual (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℂ:=
 inner ℂ (fourierL2 (Paid.actualWholeKernelSourceResidual c n))
  (OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h))+
 inner ℂ (fourierL2 (Paid.actualFiniteWholeKernelSource c n)) (actualForcingFieldResidual c h n)

def actualFourierForcingPriceError (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):ℝ:=
 Paid.actualWholeKernelSourceError c n*
  ‖OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h)‖+
 (‖(K c:BurnolL2)‖+Paid.actualWholeKernelSourceError c n)*actualForcingFieldError c h n

/-- The source forcing field and its exact same ambient residue generate the full two-leg own-FK price effect. -/
theorem actual_original_Fourier_forcing_price_residual (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):
 inner ℂ (fourierL2 (K c:BurnolL2))
  (OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h))-
 actualFiniteFourierForcingPrice c h n=actualFourierForcingPriceResidual c h n :=by
 have first:=Paid.actual_original_whole_kernel_source_residual c n
 have second:=actual_original_forcing_field_residual c h n
 unfold actualFourierForcingPriceResidual
 rw [←first,←second,map_sub,inner_sub_left,inner_sub_right]
 unfold actualFiniteFourierForcingPrice
 ring

/-- Both feet retain their own actual whole-source and action error, without a physical-projection margin. -/
theorem actual_original_Fourier_forcing_price_error (c:BurnolCompletedMellinCoordinate) (h:ℝ) (n:Nat):
 ‖inner ℂ (fourierL2 (K c:BurnolL2))
  (OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h))-
 actualFiniteFourierForcingPrice c h n‖≤actualFourierForcingPriceError c h n :=by
 rw [actual_original_Fourier_forcing_price_residual]
 unfold actualFourierForcingPriceResidual actualFourierForcingPriceError
 have first:=Paid.actual_original_whole_kernel_source_error c n
 rw [Paid.actual_original_whole_kernel_source_residual] at first
 have second:=actual_original_forcing_field_error c h n
 rw [actual_original_forcing_field_residual] at second
 calc
  _≤‖inner ℂ (fourierL2 (Paid.actualWholeKernelSourceResidual c n))
    (OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h))‖+
    ‖inner ℂ (fourierL2 (Paid.actualFiniteWholeKernelSource c n)) (actualForcingFieldResidual c h n)‖:=norm_add_le _ _
  _≤‖Paid.actualWholeKernelSourceResidual c n‖*
    ‖OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h)‖+
    ‖Paid.actualFiniteWholeKernelSource c n‖*‖actualForcingFieldResidual c h n‖:=by
   apply add_le_add
   · simpa only [fourierL2.norm_map] using norm_inner_le_norm
      (fourierL2 (Paid.actualWholeKernelSourceResidual c n))
      (OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h))
   · simpa only [fourierL2.norm_map] using norm_inner_le_norm
      (fourierL2 (Paid.actualFiniteWholeKernelSource c n)) (actualForcingFieldResidual c h n)
  _≤_:=add_le_add (mul_le_mul_of_nonneg_right first (norm_nonneg _))
   (mul_le_mul (OriginalKFullKernelCofinalSource.actual_finite_whole_kernel_source_norm c n) second
    (norm_nonneg _) (by unfold Paid.actualWholeKernelSourceError;positivity))

theorem actual_Fourier_forcing_price_error_tendsto (c:BurnolCompletedMellinCoordinate) (h:ℝ):
 Tendsto (actualFourierForcingPriceError c h) atTop (𝓝 0) :=by
 have first:=Paid.actual_whole_kernel_error_tendsto c
 have second:=actual_forcing_field_error_tendsto c h
 have constant:Tendsto (fun _:Nat=>‖(K c:BurnolL2)‖) atTop (𝓝 ‖(K c:BurnolL2)‖):=tendsto_const_nhds
 have source:=(first.mul_const
  ‖OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h)‖).add
  ((constant.add first).mul second)
 unfold actualFourierForcingPriceError
 simpa only [zero_mul,mul_zero,add_zero] using source

theorem actual_original_Fourier_forcing_price_tendsto (c:BurnolCompletedMellinCoordinate) (h:ℝ):
 Tendsto (actualFiniteFourierForcingPrice c h) atTop
  (𝓝 (inner ℂ (fourierL2 (K c:BurnolL2))
    (OriginalRieszFiniteSource.forcingIntegral c h+OriginalRieszFiniteSource.forcingIntegral c (-h)))) :=by
 exact (((fourierL2.continuous.tendsto _).comp (Paid.actual_original_whole_kernel_source_tendsto c)).inner (𝕜:=ℂ)
  (actual_original_forcing_field_tendsto c h))

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)

/-- The original actual mixed finite-Ward action pays its full same-coordinate Fourier/mixed-energy price from this generated source field. -/
theorem actual_original_FK_Ward_finite_residual (h:ℝ) (n:Nat):
 OriginalKSourceScaledMaximalResponse.originalFKForcingWard observation nontrivial half h-
 actualFiniteFourierForcingPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n=
 actualFourierForcingPriceResidual (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n :=by
 have source:=actual_original_Fourier_forcing_price_residual
  (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n
 change inner ℂ (fourierL2 (K (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half):BurnolL2))
  (OriginalKSourceScaledMaximalResponse.originalForcingPair observation nontrivial half h)-
  actualFiniteFourierForcingPrice (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n=
  actualFourierForcingPriceResidual (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h n at source
 rw [OriginalKSourceScaledMaximalResponse.actual_original_mixed_energy_ward] at source
 exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierForcingCofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
