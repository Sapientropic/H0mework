import H0mework.Chemistry.LAlanineTrueFlowConservation.SourceOrientation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowQuantitative

open SourceGaussianModel SourceSignedEvaluator ContinuousGradient ContinuousSeed
open SourceCellGeometry WholeCellReplay TrueTubeActual TrueTubeWholeActual
open TrueFlowGeometry TrueFlowConservation Matrix
open scoped Matrix
noncomputable section

def seedTransverseUpper : ℚ := ∑ i : Fin 3,
  max (seedNormalQ i * ((TrueTubeSource.recordedField 0).gradient i).1)
      (seedNormalQ i * ((TrueTubeSource.recordedField 0).gradient i).2)

theorem source_seed_width_bounds :
    (1 / 5000 : ℚ) < reportedBandWidth.1 ∧
      reportedBandWidth.2 < 2001 / 10000000 := by decide +kernel

theorem source_seed_transverse_bounds :
    (94 / 1000 : ℚ) < transverseLower ∧ seedTransverseUpper < 1001 / 10000 := by
  decide +kernel

theorem actual_seed_width_bounds (p : BandPoint) :
    (1 / 5000 : ℝ) < bandWidth 4 (Geometry.Source.epsilon 0) (p.val 1) ∧
      bandWidth 4 (Geometry.Source.epsilon 0) (p.val 1) < 2001 / 10000000 := by
  have bound := bandWidth_in_source (seedParameter p.val) (seedParameter_inside p.val p.property)
  change Holds reportedBandWidth (bandWidth 4 (Geometry.Source.epsilon 0) (p.val 1)) at bound
  have lower : (1 / 5000 : ℝ) < (reportedBandWidth.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr source_seed_width_bounds.1
  have upper : (reportedBandWidth.2 : ℝ) < 2001 / 10000000 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr source_seed_width_bounds.2
  exact ⟨lower.trans_le bound.1, bound.2.trans_lt upper⟩

theorem actual_seed_transverse_bounds (p : BandPoint) :
    (94 / 1000 : ℝ) < seedNormal ⬝ᵥ
        sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val) ∧
      seedNormal ⬝ᵥ sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val) < 1001 / 10000 := by
  have field := (TrueTubeMatrix.all_first_fields 0 _
    ((TrueTubeChecks.initial_field_eq 0).symm ▸ actual_seed_initial 0 p.val p.property)).1
  have lower : (transverseLower : ℝ) ≤ seedNormal ⬝ᵥ
      sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val) := by
    simp only [transverseLower, Rat.cast_sum, Rat.cast_min, Rat.cast_mul, dotProduct]
    apply Finset.sum_le_sum
    intro i _
    by_cases sign : (0 : ℝ) ≤ (seedNormalQ i : ℝ)
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left (field i).1 sign)
    · exact (min_le_right _ _).trans
        (mul_le_mul_of_nonpos_left (field i).2 (le_of_lt (lt_of_not_ge sign)))
  have upper : seedNormal ⬝ᵥ sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val) ≤
      (seedTransverseUpper : ℝ) := by
    simp only [seedTransverseUpper, Rat.cast_sum, Rat.cast_max, Rat.cast_mul, dotProduct]
    apply Finset.sum_le_sum
    intro i _
    by_cases sign : (0 : ℝ) ≤ (seedNormalQ i : ℝ)
    · exact (mul_le_mul_of_nonneg_left (field i).2 sign).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left (field i).1 (le_of_lt (lt_of_not_ge sign))).trans
        (le_max_left _ _)
  have strictLower : (94 / 1000 : ℝ) < (transverseLower : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr source_seed_transverse_bounds.1
  have strictUpper : (seedTransverseUpper : ℝ) < 1001 / 10000 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr source_seed_transverse_bounds.2
  exact ⟨strictLower.trans_le lower, upper.trans_lt strictUpper⟩

/-- The original width and initial field give a uniform positive seed-volume bracket. -/
theorem seedFlowDerivative_det_bounds (p : BandPoint) :
    (188 / 10000000 : ℝ) < LinearMap.det (seedFlowDerivative p).toLinearMap ∧
      LinearMap.det (seedFlowDerivative p).toLinearMap < 201 / 10000000 := by
  rw [seedFlowDerivative_det]
  have widthBounds := actual_seed_width_bounds p
  have transverse := actual_seed_transverse_bounds p
  have positive : 0 < bandWidth 4 (Geometry.Source.epsilon 0) (p.val 1) := by
    linarith [widthBounds.1]
  have lower := mul_lt_mul_of_pos_left transverse.1 positive
  have upper := mul_lt_mul_of_pos_left transverse.2 positive
  constructor <;> nlinarith [widthBounds.1, widthBounds.2]

end
end LAlanine40K2025.BasinRefinement.TrueFlowQuantitative
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
