import H0mework.Chemistry.LAlanineWholeCell.SpatialSupport

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellSpatial

open SourceGaussianModel SourceSignedEvaluator WholeCellPartition WholeCellReplay
open ContinuousParameterMap IntervalParameterMap Set MeasureTheory
open scoped BigOperators

noncomputable section
attribute [local irreducible] parameterMap parameterJacobian

def quarterVolumeInterval (q : Quarter) : Pair :=
  integralPair (generatedTargetDeterminant q) (quarterLowerQ q) (quarterUpperQ q)
def fullVolumeInterval : Pair :=
  (∑ q : Quarter, (quarterVolumeInterval q).1, ∑ q : Quarter, (quarterVolumeInterval q).2)

theorem full_volume_eq_jacobian_integral (fields : SourceFieldLaw) :
    volume.real fullPatch = ∫ p in fullDomain, (jacobianMatrix 0 4 p).det := by
  have changeVariables := integral_image_eq_integral_abs_det_fderiv_smul volume full_measurable
    (fun p _ => (parameterMap_hasFDerivAt 0 4 p).hasFDerivWithinAt)
    (actual_chart_injOn fields) (fun _ : Point => (1 : ℝ))
  have scalarIntegral : volume.real fullPatch = ∫ p in fullDomain, |(parameterJacobian 0 4 p).det| := by
    change (∫ x in fullPatch, (1 : ℝ)) = _ at changeVariables
    simpa only [setIntegral_const, smul_eq_mul, mul_one] using changeVariables
  refine scalarIntegral.trans ?_
  apply setIntegral_congr_fun full_measurable
  intro p hp
  dsimp only
  rw [SourceChart.linearDet_eq_matrixDet, abs_of_pos (full_jacobian_positive fields p hp)]

theorem full_determinant_integral_eq_quarters :
    (∫ p in fullDomain, (jacobianMatrix 0 4 p).det) =
      ∑ q : Quarter, ∫ p in quarterDomain q, (jacobianMatrix 0 4 p).det := by
  rw [fullDomain_eq_iUnion_quarters]
  have integrable : IntegrableOn (fun p => (jacobianMatrix 0 4 p).det) (⋃ q : Quarter, quarterDomain q) := by
    rw [← fullDomain_eq_iUnion_quarters]
    exact (jacobianDet_contDiff 0 4).continuous.continuousOn.integrableOn_compact full_compact
  simpa only [tsum_fintype] using
    integral_iUnion_ae (fun q => (quarter_measurable q).nullMeasurableSet) quarters_ae_disjoint integrable

theorem full_volume_enclosure (fields : SourceFieldLaw) : Holds fullVolumeInterval (volume.real fullPatch) := by
  rw [full_volume_eq_jacobian_integral fields, full_determinant_integral_eq_quarters]
  have each (q : Quarter) : Holds (quarterVolumeInterval q)
      (∫ p in quarterDomain q, (jacobianMatrix 0 4 p).det) :=
    integralPair_contains _ _ _ (fun axis => (quarter_ordered q axis).le)
      (fun p => (jacobianMatrix 0 4 p).det) (jacobianDet_contDiff 0 4).continuous
      (final_jacobian_contains fields q)
  constructor
  · change ((∑ q : Quarter, (quarterVolumeInterval q).1 : ℚ) : ℝ) ≤ _
    rw [Rat.cast_sum]
    exact Finset.sum_le_sum (fun q _ => (each q).1)
  · change _ ≤ ((∑ q : Quarter, (quarterVolumeInterval q).2 : ℚ) : ℝ)
    rw [Rat.cast_sum]
    exact Finset.sum_le_sum (fun q _ => (each q).2)

theorem source_volume_bounds :
    (293 / 10000000000 : ℚ) < fullVolumeInterval.1 ∧
      fullVolumeInterval.2 < (741 / 10000000000 : ℚ) := by
  unfold fullVolumeInterval quarterVolumeInterval
  simp only [target_determinant_recomputed]
  decide +kernel

theorem full_volume_strict (fields : SourceFieldLaw) :
    (293 / 10000000000 : ℝ) < volume.real fullPatch ∧
      volume.real fullPatch < (741 / 10000000000 : ℝ) := by
  have measured := full_volume_enclosure fields
  have lowQ : ((293 / 10000000000 : ℚ) : ℝ) < (fullVolumeInterval.1 : ℝ) :=
    Rat.cast_lt.mpr source_volume_bounds.1
  have highQ : (fullVolumeInterval.2 : ℝ) < ((741 / 10000000000 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr source_volume_bounds.2
  have low : (293 / 10000000000 : ℝ) < (fullVolumeInterval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using lowQ
  have high : (fullVolumeInterval.2 : ℝ) < (741 / 10000000000 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using highQ
  exact ⟨low.trans_le measured.1, measured.2.trans_lt high⟩

end
end LAlanine40K2025.BasinRefinement.WholeCellSpatial
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
