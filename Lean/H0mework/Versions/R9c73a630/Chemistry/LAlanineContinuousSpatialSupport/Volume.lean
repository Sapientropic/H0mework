import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousSpatialSupport.Sets

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSpatialSupport

open SourceGaussianModel SourceSignedEvaluator SourceRK4Replay SourceCellGeometry SourceChart
open ContinuousParameterMap IntervalParameterMap Set MeasureTheory

noncomputable section
attribute [local irreducible] parameterJacobian parameterMap

theorem spatialPatch_volume_eq_jacobian_integral (fields : SourceFieldLaw) :
    volume.real spatialPatch = ∫ p in cellDomain, (jacobianMatrix 0 4 p).det := by
  have changeVariables := integral_image_eq_integral_abs_det_fderiv_smul volume
    (s := cellDomain) measurableSet_Icc
    (fun p _ => (parameterMap_hasFDerivAt 0 4 p).hasFDerivWithinAt)
    (actual_chart_injOn fields) (fun _ : Point => (1 : ℝ))
  have scalarIntegral : volume.real spatialPatch =
      ∫ p in cellDomain, |(parameterJacobian 0 4 p).det| := by
    change (∫ x in spatialPatch, (1 : ℝ)) = _ at changeVariables
    simpa only [setIntegral_const, smul_eq_mul, mul_one] using changeVariables
  refine scalarIntegral.trans ?_
  apply setIntegral_congr_fun measurableSet_Icc
  intro p hp
  dsimp only
  rw [linearDet_eq_matrixDet, abs_of_pos (actual_jacobian_positive fields p hp)]

def generatedVolumeInterval : Pair :=
  integralPair generatedTargetDeterminant cellLowerQ cellUpperQ

theorem spatialPatch_volume_enclosure (fields : SourceFieldLaw) :
    Holds generatedVolumeInterval (volume.real spatialPatch) := by
  rw [spatialPatch_volume_eq_jacobian_integral fields]
  exact integralPair_contains generatedTargetDeterminant cellLowerQ cellUpperQ
    (fun axis => (cell_ordered axis).le) (fun p => (jacobianMatrix 0 4 p).det)
    (jacobianDet_contDiff 0 4).continuous (final_jacobian_contains fields)

theorem generatedDeterminant_lower_positive : 0 < generatedTargetDeterminant.1 := by
  rw [target_determinant_recomputed]
  exact lt_trans (by norm_num) source_determinant_lower

theorem generatedVolume_lower_positive : 0 < generatedVolumeInterval.1 :=
  mul_pos generatedDeterminant_lower_positive cellVolume_positive

theorem spatialPatch_volume_real_positive (fields : SourceFieldLaw) :
    0 < volume.real spatialPatch :=
  (Rat.cast_pos.mpr generatedVolume_lower_positive).trans_le (spatialPatch_volume_enclosure fields).1

theorem spatialPatch_volume_positive (fields : SourceFieldLaw) : 0 < volume spatialPatch :=
  (ENNReal.toReal_pos_iff.mp (spatialPatch_volume_real_positive fields)).1

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSpatialSupport
