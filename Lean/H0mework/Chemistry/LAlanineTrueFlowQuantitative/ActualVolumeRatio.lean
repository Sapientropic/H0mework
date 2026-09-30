import H0mework.Chemistry.LAlanineTrueFlowQuantitative.ActualBounds
import H0mework.Chemistry.LAlanineTrueFlowConservation.SourceOrientation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowQuantitative

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceFiniteData TrueFlowDifferential TrueFlowGeometry
open TrueFlowConservation TrueTubeWholeActual Set
noncomputable section

theorem log_actual_determinant_derivative (p : BandPoint) (s : Time) :
    HasDerivWithinAt (fun t => Real.log (evolvingJacobian p t).det)
      (laplacian sourceTerms densityMatrix (fullFlow p s))
      (Icc (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ) := by
  have derivative := (evolvingJacobian_determinant_evolution p s).log
    (evolvingJacobian_det_ne_zero p s)
  have same : actualPath p s = fullFlow p (s : ℝ) := rfl
  rw [same] at derivative
  simpa only [mul_div_cancel_right₀ _ (evolvingJacobian_det_ne_zero p s)] using derivative

theorem log_actual_determinant_variation (p : BandPoint) (s : Time) :
    |Real.log (evolvingJacobian p s).det - Real.log (evolvingJacobian p 0).det| ≤ 3 / 8 := by
  have estimate := (convex_Icc (-(1 / 2) : ℝ) (1 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t inside => log_actual_determinant_derivative p ⟨t, inside⟩)
    (show ∀ t ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      ‖laplacian sourceTerms densityMatrix (fullFlow p t)‖ ≤ (3 / 4 : ℝ) from by
      intro t inside
      have bounds := fullFlow_laplacian_bounds p t inside
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨bounds.1.le, bounds.2.le.trans (by norm_num)⟩)
    (show (0 : ℝ) ∈ Icc (-(1 / 2) : ℝ) (1 / 2) from by constructor <;> norm_num) s.property
  have time : |(s : ℝ)| ≤ (1 / 2 : ℝ) := abs_le.mpr s.property
  simp only [Real.norm_eq_abs, sub_zero] at estimate
  exact estimate.trans (by nlinarith)

/-- Actual volume distortion is bounded relative to the original seed frame, at every closed time. -/
theorem actual_determinant_seed_bounds (p : BandPoint) (s : Time) :
    Real.exp (-(3 / 8) : ℝ) * LinearMap.det (seedFlowDerivative p).toLinearMap ≤
      (evolvingJacobian p s).det ∧
    (evolvingJacobian p s).det ≤
      Real.exp (3 / 8 : ℝ) * LinearMap.det (seedFlowDerivative p).toLinearMap := by
  have ratio_pos : 0 < (evolvingJacobian p s).det / (evolvingJacobian p 0).det :=
    div_pos (evolvingJacobian_det_pos p s) (by
      rw [evolvingJacobian_zero, LinearMap.det_toMatrix']
      exact seedFlowDerivative_det_pos p)
  have log_ratio : |Real.log ((evolvingJacobian p s).det / (evolvingJacobian p 0).det)| ≤ 3 / 8 := by
    rw [Real.log_div (evolvingJacobian_det_ne_zero p s)
      (by rw [evolvingJacobian_zero, LinearMap.det_toMatrix']; exact (seedFlowDerivative_det_pos p).ne')]
    exact log_actual_determinant_variation p s
  have lower := Real.exp_le_exp.mpr (abs_le.mp log_ratio).1
  have upper := Real.exp_le_exp.mpr (abs_le.mp log_ratio).2
  rw [Real.exp_log ratio_pos] at lower upper
  rw [evolvingJacobian_zero, LinearMap.det_toMatrix'] at lower upper
  exact ⟨(le_div_iff₀ (seedFlowDerivative_det_pos p)).mp lower,
    (div_le_iff₀ (seedFlowDerivative_det_pos p)).mp upper⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowQuantitative
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
