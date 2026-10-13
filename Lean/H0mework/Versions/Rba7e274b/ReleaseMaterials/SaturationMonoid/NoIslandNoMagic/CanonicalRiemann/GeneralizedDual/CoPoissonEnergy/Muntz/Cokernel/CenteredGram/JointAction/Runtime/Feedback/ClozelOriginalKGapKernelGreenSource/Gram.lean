import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapKernelGreenSource.Assemble
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapKernelGreenSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance gapKernelGramComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "q" => (1/4:ℝ)
local notation "b" => burnolRieszSingleFourierSource
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "g" => Gap.actualGapResponse
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "s" => OriginalKConstantContactSourceAction.ConstantSource.seed

def actualGapSourceCorrection : BurnolL2 :=
 fourierL2 (burnolQuarterZeroExtension (g:BurnolQuarterIntervalL2))-
 burnolQuarterZeroExtension (T g:BurnolQuarterIntervalL2)

/-- The actual physical G and its complete correction are restrictions of the same original seed source. -/
theorem actual_original_gap_source_split :
 (2:ℂ) • s=(G:BurnolL2)+(2:ℂ) • actualGapSourceCorrection :=by
 have source:=OriginalKGapProjectionEulerSource.actual_gap_mean_whole_source
 unfold OriginalKGapProjectionEulerSource.actualGapWhole at source
 unfold actualGapSourceCorrection
 linear_combination (norm:=module) -source

/-- The actual seed correction is orthogonal only after the same dependent physical projection has been consumed. -/
theorem actual_gap_correction_physical_orthogonal (physical : BurnolPaAmbientCarrier) :
 inner ℂ actualGapSourceCorrection (physical:BurnolL2)=0 :=by
 have source:=congrArg (fun field:BurnolL2=>inner ℂ field (physical:BurnolL2)) actual_original_gap_source_split
 have projection:inner ℂ s (physical:BurnolL2)=inner ℂ (burnolEvenAmbientProjection s) physical :=
  ((evenBurnolClosedFace q).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right physical s).symm
 simp only [inner_add_left,inner_smul_left,starRingEnd_apply,star_ofNat] at source
 rw [projection,OriginalKCoupledPhysicalRFieldSource.actual_seed_projected_field,inner_smul_left] at source
 norm_num [starRingEnd_apply] at source
 linear_combination -source / 2

/-- The complete same-inverse correction Gram is read before the actual physical G/K Gram. -/
theorem actual_kernel_gap_correction_Gram (c : BurnolCompletedMellinCoordinate) :
 inner ℂ (OriginalRieszSourceGreen.sourceCorrection c) actualGapSourceCorrection=
 inner ℂ (b c) g-inner ℂ (T (b c)) (T g) :=by
 have crossed:inner ℂ (fourierL2 (burnolQuarterZeroExtension (b c:BurnolQuarterIntervalL2)))
  (burnolQuarterZeroExtension (T g:BurnolQuarterIntervalL2))=inner ℂ (T (b c)) (T g) :=by
  calc
   _=star (inner ℂ (burnolQuarterZeroExtension (T g:BurnolQuarterIntervalL2))
    (fourierL2 (burnolQuarterZeroExtension (b c:BurnolQuarterIntervalL2)))) :=(inner_conj_symm _ _).symm
   _=star (inner ℂ (T g) (T (b c))) :=by rw [OriginalRieszSourceGreen.extension_fourier_pairing]
   _=_ :=inner_conj_symm _ _
 unfold OriginalRieszSourceGreen.sourceCorrection actualGapSourceCorrection
 rw [inner_sub_left,inner_sub_right,inner_sub_right,fourierL2.inner_map_map,
  OriginalRieszSourceGreen.quarter_extension_inner,crossed,OriginalRieszSourceGreen.extension_fourier_pairing,
  OriginalRieszSourceGreen.quarter_extension_inner]
 change (inner ℂ (b c) g-inner ℂ (T (b c)) (T g))-(inner ℂ (T (b c)) (T g)-inner ℂ (T (b c)) (T g))=_
 ring

/-- Original seed and same-inverse correction fields generate the complete physical G/K Gram without a caller-supplied mean. -/
theorem actual_original_gap_kernel_Gram (c : BurnolCompletedMellinCoordinate) :
 c.value*inner ℂ (K c) G=
 (1/2:ℂ)*(star (OriginalRieszSource.Kernel.A c)*Gap.actualGapA-
  star (OriginalRieszSource.Kernel.beta c)*Gap.actualGapBeta) :=by
 have green:=actual_gap_kernel_correction_Green c
 have source:=congrArg (fun right:BurnolL2=>inner ℂ (OriginalRieszSourceGreen.gapState c) right)
  actual_original_gap_source_split
 rw [OriginalRieszSourceGreen.gapState_eq_kernel_add_correction] at source
 simp only [inner_add_left,inner_add_right,inner_smul_right] at source
 have bOrthogonal:inner ℂ (OriginalRieszSourceGreen.sourceCorrection c) (G:BurnolL2)=0 :=by
  rw [OriginalRieszSourceGreen.sourceCorrection_eq_generated]
  exact burnolAmbientEvenMeanZeroCorrection_inner_physical_eq_zero _ G
 have gOrthogonal:inner ℂ (K c:BurnolL2) actualGapSourceCorrection=0 :=
  inner_eq_zero_symm.mp (actual_gap_correction_physical_orthogonal (K c))
 rw [bOrthogonal,gOrthogonal,actual_kernel_gap_correction_Gram] at source
 have seedPrice:inner ℂ (OriginalRieszSourceGreen.gapState c) s=
  (1/2:ℂ)*star (OriginalRieszSource.GapEuler.gapMean q c) :=by
  have read:inner ℂ (OriginalRieszSourceGreen.gapState c) s=
   inner ℂ (burnolQuarterRestriction (OriginalRieszSourceGreen.gapState c)) (intervalConstant q) :=by
   exact (ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction _ _)
  rw [read,OriginalRieszSourceGreen.gapState_restriction,inner_smul_left]
  have unit:inner ℂ (intervalConstant q) (intervalConstant q)=(1/2:ℂ) :=by
   rw [L2.inner_def]
   have actual: (∫ x:ℝ,inner ℂ (intervalConstant q x) (intervalConstant q x) ∂(volume.restrict (symmetricInterval q)))=
    ∫ _:ℝ,(1:ℂ) ∂(volume.restrict (symmetricInterval q)) :=by
    apply integral_congr_ae
    filter_upwards [intervalConstant_coeFn q] with x atOne
    rw [atOne]
    norm_num
   rw [actual,integral_const]
   norm_num [symmetricInterval,real_smul]

  rw [unit]
  simp only [starRingEnd_apply]
  ring
 rw [←inner_add_left,←OriginalRieszSourceGreen.gapState_eq_kernel_add_correction,seedPrice] at source
 change c.value*inner ℂ (K c:BurnolL2) (G:BurnolL2)=_
 linear_combination -c.value*source-2*green

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKGapKernelGreenSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
