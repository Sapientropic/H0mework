import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.GlobalLaplace
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Positive damping controls the actual time moments required by the uniform coupling remainder. -/
set_option autoImplicit false
open Set MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
noncomputable section

theorem damping_moment_integrable (degree : ℕ) (damping : ℝ) (positive : 0<damping) :
    IntegrableOn (fun t : ℝ => Real.exp (-damping*t)*t^degree) (Ioi 0) := by
  have generated := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (degree : ℝ)) (p := 1) (b := damping)
    (by have h : 0≤(degree : ℝ) := Nat.cast_nonneg degree; linarith) (by norm_num) positive
  simpa only [Real.rpow_one,Real.rpow_natCast,mul_comm] using generated

theorem damping_moment_integral (degree : ℕ) (damping : ℝ) (positive : 0<damping) :
    (∫ t : ℝ in Ioi 0, Real.exp (-damping*t)*t^degree)=
      damping⁻¹^(degree+1)*(degree.factorial : ℝ) := by
  have generated := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (degree : ℝ)+1) (r := damping)
    (by positivity) positive
  have exponent : (degree : ℝ)+1=((degree+1 : ℕ) : ℝ) := by norm_num
  rw [add_sub_cancel_right,exponent,Real.rpow_natCast] at generated
  have gamma := Real.Gamma_nat_eq_factorial degree
  rw [← exponent,gamma] at generated
  simpa only [Real.rpow_natCast,neg_mul,mul_neg,one_div,mul_comm] using generated

theorem firstOrder_uniform_bound (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) (M : ℝ)
    (bounded : ∀ t≥0, ‖perturbation t‖≤M) (u : MatterL2) (time : ℝ) (future : 0≤time) :
    ‖firstOrder perturbation time u‖≤M*time*‖u‖ := by
  apply (firstOrder_bound perturbation continuousPerturbation u time).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
  rw [responseBound,abs_of_nonneg (intervalIntegral.integral_nonneg future (fun t _ => norm_nonneg (perturbation t)))]
  have compare := intervalIntegral.integral_mono_on future
    (continuousPerturbation.norm.intervalIntegrable (μ := volume) 0 time)
    (continuous_const.intervalIntegrable (μ := volume) 0 time)
    (fun t member => bounded t member.1)
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm] using compare

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
