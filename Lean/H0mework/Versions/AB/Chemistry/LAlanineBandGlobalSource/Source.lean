import H0mework.Chemistry.LAlanineBandGlobalSource.Orbital
import H0mework.Versions.AB.Chemistry.LAlanineGradient.Model

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource

open SourceGaussianModel SourceFiniteData ContinuousGradient
open scoped BigOperators NNReal
noncomputable section

theorem actual_source_exponents_positive :
    ∀ j : Basis, (sourceTerms j).all (fun term => decide (0 < term.exponent)) = true := by
  decide +kernel

theorem source_exponents_positive (j : Basis) :
    ∀ term ∈ sourceTerms j, 0 < term.exponent := by
  simpa only [List.all_eq_true, decide_eq_true_eq] using actual_source_exponents_positive j

def sourceOrbitalBound (d : MultiIndex) (j : Basis) : ℝ≥0 := orbitalBound (sourceTerms j) d

theorem source_orbital_uniform_bound (d : MultiIndex) (j : Basis) (x : Point) :
    |orbital (sourceTerms j) d x| ≤ (sourceOrbitalBound d j : ℝ) :=
  orbital_uniform_bound _ (source_exponents_positive j) d x

def sourceBilinearBound (left right : MultiIndex) : ℝ≥0 :=
  ∑ i : Basis, ∑ j : Basis,
    ‖(densityMatrix i j : ℝ)‖₊ * sourceOrbitalBound left i * sourceOrbitalBound right j

theorem source_bilinear_uniform_bound (left right : MultiIndex) (x : Point) :
    |bilinear sourceTerms densityMatrix left right x| ≤ (sourceBilinearBound left right : ℝ) := by
  unfold bilinear
  calc
    _ ≤ ∑ i : Basis, |∑ j : Basis, (densityMatrix i j : ℝ) *
        orbital (sourceTerms i) left x * orbital (sourceTerms j) right x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Basis, ∑ j : Basis,
        |(densityMatrix i j : ℝ)| * (sourceOrbitalBound left i : ℝ) * (sourceOrbitalBound right j : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (source_orbital_uniform_bound left i x) (abs_nonneg _))
        (source_orbital_uniform_bound right j x) (abs_nonneg _) (by positivity)
    _ = _ := by simp only [sourceBilinearBound, NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]

def sourceFirstBound (left right : MultiIndex) (axis : Fin 3) : ℝ≥0 :=
  sourceBilinearBound (raise left axis) right + sourceBilinearBound left (raise right axis)

theorem source_first_uniform_bound (left right : MultiIndex) (axis : Fin 3) (x : Point) :
    |firstBilinear sourceTerms densityMatrix left right axis x| ≤ (sourceFirstBound left right axis : ℝ) :=
  (abs_add_le _ _).trans (add_le_add
    (source_bilinear_uniform_bound (raise left axis) right x)
    (source_bilinear_uniform_bound left (raise right axis) x))

end
end LAlanine40K2025.BasinRefinement.GlobalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
