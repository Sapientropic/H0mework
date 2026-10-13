import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalPricing
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource.Pricing
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open SourceGeneratedComplexFeaturePerfectification
open scoped InnerProductSpace Topology

theorem ambient_R_positionGap (z : ℂ) (rightQuarter : 1/4 < z.re) (value : BurnolL2)
 (gap : value ∈ locallyConstantFace burnolUnscaledCommonGapRadius) :
 burnolDirectRightResolvent z value ∈ locallyConstantFace burnolUnscaledCommonGapRadius := by
 unfold burnolDirectRightResolvent
 apply (locallyConstantFace burnolUnscaledCommonGapRadius).neg_mem
 apply integral_mem_closedSubmodule
  {toSubmodule := locallyConstantFace burnolUnscaledCommonGapRadius,
   isClosed' := locallyConstantFace_isClosed burnolUnscaledCommonGapRadius}
 · exact burnolDirectRightResolventIntegrand_integrableOn z rightQuarter value
 · filter_upwards [ae_restrict_mem measurableSet_Ioi] with shift positive
   unfold burnolDirectRightResolventIntegrand
   apply (locallyConstantFace burnolUnscaledCommonGapRadius).smul_mem
   apply burnolMultiplicativeDilation_mem_locallyConstantFace_of_nonpositive
    burnolUnscaledCommonGapRadius (by norm_num [burnolUnscaledCommonGapRadius])
   · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr positive.le) (by norm_num)
   · exact gap

theorem ambient_R_scalar_action (z : ℂ) (rightQuarter : 1/4 < z.re)
 (value : BurnolL2) (gap : value ∈ locallyConstantFace burnolUnscaledCommonGapRadius)
 (w : ℂ) (wRight : 1/4 < w.re) (wBelow : w.re < 1/2) :
 burnolAmbientCompletedMellinEvaluator (burnolDivisionCompletedMellinCoordinate w wRight wBelow)
  (burnolDirectRightResolvent z value) =
 (-(1/(z+w-(1/2 : ℂ)))) *
 burnolAmbientCompletedMellinEvaluator (burnolDivisionCompletedMellinCoordinate w wRight wBelow) value := by
 let coordinate := burnolDivisionCompletedMellinCoordinate w wRight wBelow
 let read := burnolAmbientCompletedMellinEvaluator coordinate
 have decay : (((1/2 : ℂ)-z-w).re < 0) := by
  simp only [Complex.sub_re]
  norm_num
  linarith
 have integrable := burnolDirectRightResolventIntegrand_integrableOn z rightQuarter value
 have integralRead : read (burnolDirectRightResolvent z value) =
  -∫ h : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight z h *
   quarterDilationCharacter w (Real.exp h) * read value := by
  change read (-∫ h : ℝ in Ioi 0, burnolDirectRightResolventIntegrand z value h) = _
  rw [map_neg, ← read.integral_comp_comm integrable]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h positive
  change burnolAmbientCompletedMellinEvaluator coordinate
   (positiveMellinQuarterRightResolventWeight z h • burnolMultiplicativeDilation (-h/2) value) = _
  rw [map_smul, burnolAmbientCompletedMellinEvaluator_dilation_of_positionGap
   coordinate (-h/2) (by change 0 < h at positive; linarith) value gap]
  change positiveMellinQuarterRightResolventWeight z h *
   (Complex.exp (((2*w)-(1/2 : ℂ))*((-h/2 : ℝ) : ℂ)) * read value) = _
  rw [divisionJet_ambientDilationExp_eq_quarterCharacter]
  exact (mul_assoc _ _ _).symm
 rw [integralRead, integral_mul_const, positiveMellinQuarterRightResolvent_scalarKernel z w decay]
 exact (neg_mul (1/(z+w-(1/2 : ℂ))) (read value)).symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource.Pricing
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
