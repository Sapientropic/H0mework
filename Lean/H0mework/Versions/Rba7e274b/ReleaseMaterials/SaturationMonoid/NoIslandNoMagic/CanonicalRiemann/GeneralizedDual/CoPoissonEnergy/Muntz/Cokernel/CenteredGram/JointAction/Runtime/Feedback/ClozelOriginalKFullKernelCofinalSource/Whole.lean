import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullKernelCofinalSource.Source
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
local instance kernelCofinalWholePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "S" => burnolMeanZeroTruncatedFourierSquare
local notation "b" => burnolRieszSingleFourierSource

def actualWholeKernelCorrection : M→L[ℂ]BurnolL2 :=
 OriginalKResponseCofinalSourceAction.actualWholeRead.comp T-
 fourierL2.toLinearIsometry.toContinuousLinearMap.comp OriginalKResponseCofinalSourceAction.actualWholeRead

def actualFiniteWholeKernelSource (c:BurnolCompletedMellinCoordinate) (n:Nat):BurnolL2:=
 OriginalRieszSourceGreen.gapState c+actualWholeKernelCorrection (actualFiniteKernelSource c n)

def actualWholeKernelSourceResidual (c:BurnolCompletedMellinCoordinate) (n:Nat):BurnolL2:=
 actualWholeKernelCorrection ((S^n) (b c))

/-- The complete same original source is reconstructed in its ambient carrier; the physical target is not an input to the finite source. -/
theorem actual_original_whole_kernel_read (c:BurnolCompletedMellinCoordinate):
 (K c:BurnolL2)=OriginalRieszSourceGreen.gapState c+actualWholeKernelCorrection (b c) :=by
 have source:=OriginalRieszSource.Kernel.original_kernel_reconstruction c
 exact source.trans (by
  unfold actualWholeKernelCorrection
  change _=burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula c)+
   (burnolQuarterZeroExtension (T (b c):BurnolQuarterIntervalL2)-
    fourierL2 (burnolQuarterZeroExtension (b c:BurnolQuarterIntervalL2)))
  module)

/-- The source-generated finite ambient material retains the exact same correction residual; it is not declared physical. -/
theorem actual_original_whole_kernel_source_residual (c:BurnolCompletedMellinCoordinate) (n:Nat):
 (K c:BurnolL2)-actualFiniteWholeKernelSource c n=actualWholeKernelSourceResidual c n :=by
 rw [actual_original_whole_kernel_read]
 unfold actualFiniteWholeKernelSource actualWholeKernelSourceResidual
 have source:=congrArg actualWholeKernelCorrection (actual_kernel_source_residual c n)
 rw [map_sub] at source
 linear_combination (norm:=module) source

def actualWholeKernelSourceError (c:BurnolCompletedMellinCoordinate) (n:Nat):ℝ:=
 ‖actualWholeKernelCorrection‖*((1/4:ℝ)^n*((4/3:ℝ)*‖actualFourierKernelForcing c‖))

/-- Only the actual ambient source correction norm controls this same occurrence residual; no projected margin is borrowed. -/
theorem actual_original_whole_kernel_source_error (c:BurnolCompletedMellinCoordinate) (n:Nat):
 ‖(K c:BurnolL2)-actualFiniteWholeKernelSource c n‖≤actualWholeKernelSourceError c n :=by
 rw [actual_original_whole_kernel_source_residual]
 unfold actualWholeKernelSourceResidual actualWholeKernelSourceError
 have source:=actual_kernel_source_error c n
 rw [actual_kernel_source_residual] at source
 exact (actualWholeKernelCorrection.le_opNorm _).trans
  (mul_le_mul_of_nonneg_left source (norm_nonneg _))

/-- The original full K is consumed as the limit of its actual ambient source programme, before any physical Gram read. -/
theorem actual_original_whole_kernel_source_tendsto (c:BurnolCompletedMellinCoordinate):
 Tendsto (actualFiniteWholeKernelSource c) atTop (𝓝 (K c:BurnolL2)) :=by
 have constant:Tendsto (fun _:Nat=>OriginalRieszSourceGreen.gapState c) atTop (𝓝 (OriginalRieszSourceGreen.gapState c)):=tendsto_const_nhds
 have source:=constant.add
  ((actualWholeKernelCorrection.continuous.tendsto _).comp (actual_kernel_source_tendsto c))
 rw [←actual_original_whole_kernel_read] at source
 exact source

/-- The actual ambient source error converges by its paid geometric source action; this is not a zero-residual constructor. -/
theorem actual_whole_kernel_error_tendsto (c:BurnolCompletedMellinCoordinate):
 Tendsto (actualWholeKernelSourceError c) atTop (𝓝 0) :=by
 have source:=((tendsto_pow_atTop_nhds_zero_of_lt_one
  (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)).mul_const
  ((4/3:ℝ)*‖actualFourierKernelForcing c‖)).const_mul ‖actualWholeKernelCorrection‖
 unfold actualWholeKernelSourceError
 simpa only [zero_mul,mul_zero] using source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullKernelCofinalSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
