import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsPolarFrameTransport
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Polar

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem sqrt_sub_one_le (x : ℝ) (positive : 0 ≤ x) : |Real.sqrt x - 1| ≤ |x - 1| := by
  have square := Real.sq_sqrt positive
  have rootPositive := Real.sqrt_nonneg x
  have factor : x - 1 = (Real.sqrt x - 1) * (Real.sqrt x + 1) := by nlinarith
  rw [factor, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt x + 1)]
  nlinarith [abs_nonneg (Real.sqrt x - 1)]

theorem sqrt_residual_norm (A : Matrix ι ι ℂ) (positive : 0 ≤ A) :
    ‖CFC.sqrt A - 1‖ ≤ ‖A - 1‖ := by
  have selfAdjoint : IsSelfAdjoint A := positive.isSelfAdjoint
  have sqrtRead : CFC.sqrt A = cfc Real.sqrt A := by
    rw [CFC.sqrt_eq_real_sqrt A positive, cfcₙ_eq_cfc]
  have difference (f : ℝ → ℝ) (continuous : Continuous f) :
      cfc (fun x => f x - 1) A = cfc f A - 1 := by
    rw [cfc_sub f (fun _ => 1) A continuous.continuousOn continuous_const.continuousOn,
      cfc_const_one ℝ A selfAdjoint]
  rw [sqrtRead, ← difference Real.sqrt Real.continuous_sqrt]
  apply norm_cfc_le (norm_nonneg _)
  intro x inSpectrum
  have scalar := sqrt_sub_one_le x (spectrum_nonneg_of_nonneg positive inSpectrum)
  have raw := norm_apply_le_norm_cfc (fun x : ℝ => x - 1) A inSpectrum
    (continuous_id.sub continuous_const).continuousOn selfAdjoint
  have rawIdentity : cfc (fun x : ℝ => x - 1) A = A - 1 := by
    exact (difference (fun x : ℝ => x) continuous_id).trans
      (congrArg (fun B : Matrix ι ι ℂ => B - 1) (cfc_id' ℝ A selfAdjoint))
  rw [rawIdentity] at raw
  have scalarNorm : ‖Real.sqrt x - 1‖ ≤ ‖x - 1‖ := by simpa only [Real.norm_eq_abs] using scalar
  exact scalarNorm.trans raw

theorem projectionResidual_norm_le_gram (C : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    ‖projectionResidual C‖ ≤ ‖star C * C - 1‖ := by
  rw [residual_norm C close, CFC.abs]
  exact sqrt_residual_norm _ (star_mul_self_nonneg C)

theorem transport_error_le (C X : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    ‖transport C X - C * X * star C‖ ≤ ‖star C * C - 1‖ * ‖X‖ * (1 + ‖C‖) := by
  nontriviality (Matrix ι ι ℂ)
  have unitNorm : ‖matrix C‖ = 1 := CStarRing.norm_of_mem_unitary (matrix_mem_unitary C close)
  have factor : transport C X - C * X * star C =
      (matrix C - C) * X * star (matrix C) + C * X * star (matrix C - C) := by
    unfold transport
    simp only [star_sub]
    noncomm_ring
  have difference : ‖matrix C - C‖ = ‖projectionResidual C‖ := norm_sub_rev _ _
  rw [factor]
  calc
    _ ≤ ‖(matrix C - C) * X * star (matrix C)‖ + ‖C * X * star (matrix C - C)‖ := norm_add_le _ _
    _ ≤ (‖matrix C - C‖ * ‖X‖) * ‖star (matrix C)‖ +
        (‖C‖ * ‖X‖) * ‖star (matrix C - C)‖ :=
      add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
    _ = ‖projectionResidual C‖ * ‖X‖ * (1 + ‖C‖) := by
      rw [norm_star, norm_star, unitNorm, difference]
      ring
    _ ≤ _ := by gcongr; exact projectionResidual_norm_le_gram C close

theorem transport_error_le_close (C X : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    ‖transport C X - C * X * star C‖ ≤
      ‖star C * C - 1‖ * ‖X‖ * (2 + ‖C - 1‖) := by
  nontriviality (Matrix ι ι ℂ)
  have near : ‖C‖ ≤ ‖C - 1‖ + 1 := by
    calc
      _ = ‖(C - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖C - 1‖ + ‖(1 : Matrix ι ι ℂ)‖ := norm_add_le _ _
      _ = _ := by rw [norm_one]
  exact (transport_error_le C X close).trans
    (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

end
end LAlanine40K2025.ElectronicFrame.Polar
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
