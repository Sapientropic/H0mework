import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaussianPlaneSource
import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceClockPhiTwoStepGaussianMoment
open MeasureTheory ProbabilityTheory
private abbrev γ := gaussianReal 0 1
private def noise (V t θ : ℝ) (z : ℝ × ℝ) : ℝ :=
  -Real.log ((V+18*t)/V)/6+
    Real.sqrt (Real.log ((V+18*t)/V)/9)*(z.1*Real.cos θ+z.2*Real.sin θ)

theorem actual_two_step_exponential_moment (V t s q θ φ : ℝ)
    (hV : 0 < V) (ht : 0 < t) (hs : 0 < s) :
    Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) =>
      Real.exp (q*(noise V t θ z.1+noise (V+18*t) s φ z.2)))
      ((γ.prod γ).prod (γ.prod γ)) ∧
    (∫z : (ℝ×ℝ)×(ℝ×ℝ),
      Real.exp (q*(noise V t θ z.1+noise (V+18*t) s φ z.2))
        ∂(γ.prod γ).prod (γ.prod γ)) =
          Real.rpow ((V+18*(s+t))/V) (q*(q-3)/18) := by
  have hW : 0 < V+18*t := by positivity
  have h1 := SourceClockPhiGaussianPlaneSource.actual_rotated_heat_exponential_moment V t q θ hV ht
  have h2 := SourceClockPhiGaussianPlaneSource.actual_rotated_heat_exponential_moment (V+18*t) s q φ hW hs
  have hi : Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => Real.exp (q*noise V t θ z.1)*
      Real.exp (q*noise (V+18*t) s φ z.2)) ((γ.prod γ).prod (γ.prod γ)) := by
    simpa only [noise] using h1.1.mul_prod h2.1
  have he (z : (ℝ×ℝ)×(ℝ×ℝ)) :
      Real.exp (q*(noise V t θ z.1+noise (V+18*t) s φ z.2)) =
        Real.exp (q*noise V t θ z.1)*Real.exp (q*noise (V+18*t) s φ z.2) := by
    rw [mul_add,Real.exp_add]
  constructor
  · simpa only [he] using hi
  · simp_rw [he]
    erw [integral_prod_mul (μ:=γ.prod γ) (ν:=γ.prod γ)
      (fun z : ℝ×ℝ => Real.exp (q*noise V t θ z))
      (fun z : ℝ×ℝ => Real.exp (q*noise (V+18*t) s φ z))]
    change (∫z : ℝ×ℝ, Real.exp (q*noise V t θ z) ∂γ.prod γ)*
      (∫z : ℝ×ℝ, Real.exp (q*noise (V+18*t) s φ z) ∂γ.prod γ) = _
    have hm1 : (∫z : ℝ×ℝ, Real.exp (q*noise V t θ z) ∂γ.prod γ) =
        Real.rpow ((V+18*t)/V) (q*(q-3)/18) := h1.2
    have hm2 : (∫z : ℝ×ℝ, Real.exp (q*noise (V+18*t) s φ z) ∂γ.prod γ) =
        Real.rpow (((V+18*t)+18*s)/(V+18*t)) (q*(q-3)/18) := h2.2
    rw [hm1,hm2]
    change (((V+18*t)/V)^(q*(q-3)/18:ℝ))*
      (((V+18*t+18*s)/(V+18*t))^(q*(q-3)/18:ℝ)) = _
    rw [←Real.mul_rpow]
    · congr 1
      field_simp [hV.ne',hW.ne']
      ring
    · exact (div_pos hW hV).le
    · exact (div_pos (by positivity) hW).le
end LowEnergy.SourceClockPhiTwoStepGaussianMoment
