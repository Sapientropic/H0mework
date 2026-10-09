import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Weak.Test
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.GlobalSource.Differential.DeterminantBound

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource GlobalSource.Differential Set MeasureTheory
open _root_.LAlanineTrueFlowDifferential
noncomputable section

def pull (test : Test) (t : ℝ) (x : Point) : ℝ :=
  (responseMatrix x t).det * test.value (flow x (spatialStep*t))

def pullDerivative (test : Test) (t : ℝ) (x : Point) : ℝ :=
  (spatialStep*laplacian sourceTerms densityMatrix (flow x (spatialStep*t))*(responseMatrix x t).det) *
      test.value (flow x (spatialStep*t)) +
    (responseMatrix x t).det * test.derivative (flow x (spatialStep*t)) (field (flow x (spatialStep*t)))

theorem pull_derivative (test : Test) (x : Point) (t : Time) :
    HasDerivAt (fun s => pull test s x) (pullDerivative test t x) (t : ℝ) :=
  (response_determinant_evolution x t).mul ((test.hasFDerivAt _).comp_hasDerivAt (t : ℝ) (actual_derivative x t))

theorem pull_zero (test : Test) (x : Point) : pull test 0 x = test.value x := by
  simp only [pull,responseMatrix_starts,Matrix.det_one,one_mul,mul_zero,flow_starts]

theorem pullDerivative_zero (test : Test) (x : Point) :
    pullDerivative test 0 x = spatialStep *
      (laplacian sourceTerms densityMatrix x*test.value x + test.derivative x (sourceGradient x)) := by
  simp only [pullDerivative,responseMatrix_starts,Matrix.det_one,one_mul,mul_one,mul_zero,flow_starts,field,map_smul,smul_eq_mul]
  ring

theorem pull_integrable (test : Test) (t : Time) : IntegrableOn (pull test t) basin :=
  basin_pullback_integrable t test.value test.integrable.integrableOn

theorem pull_integral (test : Test) (t : Time) :
    (∫ x in basin, pull test t x) = ∫ x in basin, test.value x :=
  (basin_original_change_variables t test.value).symm

theorem field_bound (x : Point) : ‖field x‖ ≤ spatialStep*(GlobalSource.sourceSpeedBound : ℝ) := by
  rw [field,norm_smul,Real.norm_eq_abs,abs_of_pos spatialStep_positive]
  exact mul_le_mul_of_nonneg_left (GlobalSource.sourceGradient_uniform_bound x) spatialStep_positive.le

theorem pullDerivative_bound (test : Test) (A B : ℝ) (_apos : 0 ≤ A) (bpos : 0 ≤ B)
    (value : ∀ x, ‖test.value x‖ ≤ A) (derivative : ∀ x, ‖test.derivative x‖ ≤ B)
    (x : Point) (t : Time) :
    ‖pullDerivative test t x‖ ≤ 144*A+48*B*(spatialStep*(GlobalSource.sourceSpeedBound : ℝ)) := by
  unfold pullDerivative
  calc
    _ ≤ ‖spatialStep*laplacian sourceTerms densityMatrix (flow x (spatialStep*(t : ℝ)))*(responseMatrix x t).det‖*
          ‖test.value (flow x (spatialStep*(t : ℝ)))‖ +
        ‖(responseMatrix x t).det‖ * ‖test.derivative (flow x (spatialStep*(t : ℝ))) (field (flow x (spatialStep*(t : ℝ))))‖ := by
      exact (norm_add_le _ _).trans_eq (by simp only [norm_mul])
    _ ≤ 144*A+48*(B*(spatialStep*(GlobalSource.sourceSpeedBound : ℝ))) := by
      apply add_le_add
      · exact mul_le_mul (determinant_rate_bound x t) (value _) (norm_nonneg _) (by norm_num)
      · apply mul_le_mul (response_determinant_bound x t) _ (norm_nonneg _) (by norm_num)
        exact (test.derivative _).le_opNorm _ |>.trans (mul_le_mul (derivative _) (field_bound _) (norm_nonneg _) bpos)
    _ = _ := by ring

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Weak
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
