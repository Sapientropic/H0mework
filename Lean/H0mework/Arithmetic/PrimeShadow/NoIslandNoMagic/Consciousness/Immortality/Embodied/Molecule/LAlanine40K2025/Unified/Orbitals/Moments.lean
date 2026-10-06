import H0mework.Chemistry.LAlanineBandGlobalSource.Primitive
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement GaussianPrimitive GlobalSource MeasureTheory Polynomial
noncomputable section

def moment (alpha : ℝ) (n : ℕ) : ℝ := ∫ x : ℝ, x^n * Real.exp (-alpha*x^2)

theorem moment_integrable (alpha : ℝ) (positive : 0 < alpha) (n : ℕ) :
    Integrable (fun x : ℝ => x^n * Real.exp (-alpha*x^2)) := by
  convert! gaussian_integrable positive ((X : Polynomial ℝ)^n) using 1
  funext x
  simp only [GaussianPrimitive.gaussian,eval_pow,eval_X]

theorem gaussian_jet_integral_zero (alpha : ℝ) (positive : 0 < alpha) (p : Polynomial ℝ) :
    (∫ x : ℝ, gaussian alpha (jetPolynomial alpha p) x) = 0 :=
  integral_eq_zero_of_hasDerivAt_of_integrable (gaussian_hasDerivAt p alpha)
    (gaussian_integrable positive _) (gaussian_integrable positive _)

theorem moment_zero (alpha : ℝ) : moment alpha 0 = Real.sqrt (Real.pi/alpha) := by
  simpa only [moment,pow_zero,one_mul] using integral_gaussian alpha

theorem moment_one (alpha : ℝ) (positive : 0 < alpha) : moment alpha 1 = 0 := by
  have zero := gaussian_jet_integral_zero alpha positive 1
  have form : gaussian alpha (jetPolynomial alpha 1) =
      fun x : ℝ => (-2*alpha) * (x * Real.exp (-alpha*x^2)) := by
    funext x
    simp [GaussianPrimitive.gaussian,jetPolynomial]
    ring
  rw [form,integral_const_mul] at zero
  have ha : -2*alpha ≠ 0 := by positivity
  have result := (mul_eq_zero.mp zero).resolve_left ha
  simpa only [moment,pow_one] using result

theorem moment_step (alpha : ℝ) (positive : 0 < alpha) (n : ℕ) :
    moment alpha (n+2) = (n+1 : ℝ)/(2*alpha) * moment alpha n := by
  have zero := gaussian_jet_integral_zero alpha positive ((X : Polynomial ℝ)^(n+1))
  have form : gaussian alpha (jetPolynomial alpha ((X : Polynomial ℝ)^(n+1))) =
      fun x : ℝ => (n+1 : ℝ) * (x^n * Real.exp (-alpha*x^2)) -
        (2*alpha) * (x^(n+2) * Real.exp (-alpha*x^2)) := by
    funext x
    simp only [GaussianPrimitive.gaussian,jetPolynomial,derivative_X_pow_succ,
      eval_sub,eval_mul,eval_C,eval_pow,eval_X]
    simp only [pow_succ]
    ring
  rw [form,integral_sub ((moment_integrable alpha positive n).const_mul _)
    ((moment_integrable alpha positive (n+2)).const_mul _),integral_const_mul,integral_const_mul] at zero
  change (n+1 : ℝ)*moment alpha n - (2*alpha)*moment alpha (n+2) = 0 at zero
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero (by norm_num) positive.ne')).mpr
  nlinarith

end
end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
