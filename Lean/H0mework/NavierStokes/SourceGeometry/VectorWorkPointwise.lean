import H0mework.NavierStokes.Fourier.FullVorticityStretching

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator

noncomputable section

private theorem vector_linear_apply_sum (D : PhysicalSpace →L[ℝ] PhysicalSpace)
    (v : PhysicalSpace) (i : Coordinate) :
    D v i = ∑ j : Coordinate, v j * D (EuclideanSpace.single j 1) i := by
  rw [← (EuclideanSpace.basisFun Coordinate ℝ).sum_repr v, map_sum]
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    map_smul, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, PiLp.single_apply, mul_ite, mul_one,
    mul_zero, Fintype.sum_ite_eq]

theorem fderiv_norm_le_gradient (field : PhysicalSpace → PhysicalSpace)
    (x v : PhysicalSpace) :
    ‖fderiv ℝ field x v‖ ≤ ‖v‖ * Real.sqrt (gradientDissipation field x) := by
  have nonneg : 0 ≤ gradientDissipation field x := by
    unfold gradientDissipation
    positivity
  have bound : ‖fderiv ℝ field x v‖ ^ 2 ≤
      ‖v‖ ^ 2 * gradientDissipation field x := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    unfold gradientDissipation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [vector_linear_apply_sum]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => v j) (fun j => fderiv ℝ field x (EuclideanSpace.single j 1) i)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt nonneg] using bound

theorem source_transport_pointwise (u omega : PhysicalSpace → PhysicalSpace)
    (U : ℝ) (uBound : ∀ x, ‖u x‖ ≤ U) (x : PhysicalSpace) :
    |inner ℝ (u x) (fderiv ℝ omega x (omega x))| ≤
      U * (‖omega x‖ * Real.sqrt (gradientDissipation omega x)) := by
  calc
    |inner ℝ (u x) (fderiv ℝ omega x (omega x))| ≤
        ‖u x‖ * ‖fderiv ℝ omega x (omega x)‖ := abs_real_inner_le_norm _ _
    _ ≤ U * ‖fderiv ℝ omega x (omega x)‖ :=
      mul_le_mul_of_nonneg_right (uBound x) (norm_nonneg _)
    _ ≤ U * (‖omega x‖ * Real.sqrt (gradientDissipation omega x)) :=
      mul_le_mul_of_nonneg_left (fderiv_norm_le_gradient omega x (omega x))
        ((norm_nonneg _).trans (uBound x))

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
