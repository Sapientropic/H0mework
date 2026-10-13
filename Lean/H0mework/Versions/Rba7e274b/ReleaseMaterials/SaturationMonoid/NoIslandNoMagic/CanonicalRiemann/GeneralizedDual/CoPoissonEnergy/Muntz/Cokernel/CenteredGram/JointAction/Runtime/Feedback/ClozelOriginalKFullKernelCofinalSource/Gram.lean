import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullKernelCofinalSource.Whole
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
local instance kernelCofinalGramPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "dual" => OriginalKQuarterTailPhysicalSource.actualStarSource

def actualFiniteFourierDual (c:BurnolCompletedMellinCoordinate) (n:Nat):ℂ:=
 inner ℂ (fourierL2 (actualFiniteWholeKernelSource c n)) (actualFiniteWholeKernelSource (dual c) n)

def actualFourierDualSourceResidual (c:BurnolCompletedMellinCoordinate) (n:Nat):ℂ:=
 inner ℂ (fourierL2 (actualWholeKernelSourceResidual c n)) (K (dual c):BurnolL2)+
 inner ℂ (fourierL2 (actualFiniteWholeKernelSource c n)) (actualWholeKernelSourceResidual (dual c) n)

def actualFourierDualSourceError (c:BurnolCompletedMellinCoordinate) (n:Nat):ℝ:=
 actualWholeKernelSourceError c n*‖(K (dual c):BurnolL2)‖+
 (‖(K c:BurnolL2)‖+actualWholeKernelSourceError c n)*actualWholeKernelSourceError (dual c) n

/-- The actual two full ambient source programmes generate the exact original FourierDual inventory residual, without a physical-candidate cast. -/
theorem actual_original_Fourier_dual_source_residual (c:BurnolCompletedMellinCoordinate) (n:Nat):
 OriginalKStaticKernelSourceGramSource.actualFourierDualGram c-actualFiniteFourierDual c n=
 actualFourierDualSourceResidual c n :=by
 have first:=actual_original_whole_kernel_source_residual c n
 have second:=actual_original_whole_kernel_source_residual (dual c) n
 unfold actualFourierDualSourceResidual
 rw [←first,←second,map_sub,inner_sub_left,inner_sub_right]
 unfold OriginalKStaticKernelSourceGramSource.actualFourierDualGram actualFiniteFourierDual
 ring

/-- The actual finite source norm retains its own whole carrier and exact original K reference; it supplies no positive physical margin. -/
theorem actual_finite_whole_kernel_source_norm (c:BurnolCompletedMellinCoordinate) (n:Nat):
 ‖actualFiniteWholeKernelSource c n‖≤‖(K c:BurnolL2)‖+actualWholeKernelSourceError c n :=by
 have source:=actual_original_whole_kernel_source_residual c n
 have actual:actualFiniteWholeKernelSource c n=(K c:BurnolL2)-actualWholeKernelSourceResidual c n :=by
  linear_combination (norm:=module) -source
 rw [actual]
 have error:=actual_original_whole_kernel_source_error c n
 rw [source] at error
 exact (norm_sub_le _ _).trans (add_le_add_right error _)

/-- Both original FourierDual legs pay their full source approximation error from the actual forcing-generated whole fields. -/
theorem actual_original_Fourier_dual_source_error (c:BurnolCompletedMellinCoordinate) (n:Nat):
 ‖OriginalKStaticKernelSourceGramSource.actualFourierDualGram c-actualFiniteFourierDual c n‖≤
 actualFourierDualSourceError c n :=by
 rw [actual_original_Fourier_dual_source_residual]
 unfold actualFourierDualSourceResidual actualFourierDualSourceError
 have first:=actual_original_whole_kernel_source_error c n
 have second:=actual_original_whole_kernel_source_error (dual c) n
 rw [actual_original_whole_kernel_source_residual] at first second
 calc
  _≤‖inner ℂ (fourierL2 (actualWholeKernelSourceResidual c n)) (K (dual c):BurnolL2)‖+
   ‖inner ℂ (fourierL2 (actualFiniteWholeKernelSource c n)) (actualWholeKernelSourceResidual (dual c) n)‖:=norm_add_le _ _
  _≤(‖actualWholeKernelSourceResidual c n‖*‖(K (dual c):BurnolL2)‖)+
   ‖actualFiniteWholeKernelSource c n‖*‖actualWholeKernelSourceResidual (dual c) n‖ :=by
   apply add_le_add
   · simpa only [fourierL2.norm_map] using norm_inner_le_norm (fourierL2 (actualWholeKernelSourceResidual c n)) (K (dual c):BurnolL2)
   · simpa only [fourierL2.norm_map] using norm_inner_le_norm (fourierL2 (actualFiniteWholeKernelSource c n)) (actualWholeKernelSourceResidual (dual c) n)
  _≤_ :=add_le_add
   (mul_le_mul_of_nonneg_right first (norm_nonneg _))
   (mul_le_mul (actual_finite_whole_kernel_source_norm c n) second (norm_nonneg _) (by unfold actualWholeKernelSourceError; positivity))

/-- The source errors of the actual two original materials converge to zero; the FourierDual value is not inserted in the source. -/
theorem actual_Fourier_dual_source_error_tendsto (c:BurnolCompletedMellinCoordinate):
 Tendsto (actualFourierDualSourceError c) atTop (𝓝 0) :=by
 have first:=actual_whole_kernel_error_tendsto c
 have second:=actual_whole_kernel_error_tendsto (dual c)
 have constant:Tendsto (fun _:Nat=>‖(K c:BurnolL2)‖) atTop (𝓝 ‖(K c:BurnolL2)‖):=tendsto_const_nhds
 have source:=(first.mul_const ‖(K (dual c):BurnolL2)‖).add ((constant.add first).mul second)
 unfold actualFourierDualSourceError
 simpa only [zero_mul,mul_zero,add_zero] using source

/-- The literal original FourierDual consumes the independently generated two whole source closures. -/
theorem actual_original_Fourier_dual_source_tendsto (c:BurnolCompletedMellinCoordinate):
 Tendsto (actualFiniteFourierDual c) atTop (𝓝 (OriginalKStaticKernelSourceGramSource.actualFourierDualGram c)) :=by
 have source:=(((fourierL2.continuous.tendsto _).comp (actual_original_whole_kernel_source_tendsto c)).inner (𝕜:=ℂ)
  (actual_original_whole_kernel_source_tendsto (dual c)))
 exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullKernelCofinalSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
