import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

namespace OriginalRieszFiniteResponse.Integration

open Complex MeasureTheory
open scoped Topology
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

theorem finite_response (value forcing : ℝ → ℂ) (coefficient : ℂ)
    (action : ∀ time : ℝ, HasDerivAt value (forcing time - coefficient * value time) time)
    (continuousForcing : Continuous forcing) (endpoint : ℝ) :
    value endpoint = Complex.exp (-coefficient * (endpoint : ℂ)) * value 0 +
      ∫ time : ℝ in (0 : ℝ)..endpoint,
        Complex.exp (-coefficient * ((endpoint : ℂ) - (time : ℂ))) * forcing time := by
  let weight := fun time : ℝ => Complex.exp (coefficient * (time : ℂ))
  have derivative (time : ℝ) : HasDerivAt (fun t : ℝ => weight t * value t)
      (weight time * forcing time) time := by
    have exponential := ((Complex.ofRealCLM.hasDerivAt (x := time)).const_mul coefficient).cexp
    have actual := exponential.mul (action time)
    convert! actual using 1
    simp only [weight, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
    ring
  have continuousWeight : Continuous weight := by
    unfold weight
    exact (continuous_const.mul Complex.continuous_ofReal).cexp
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time _ => derivative time) ((continuousWeight.mul continuousForcing).intervalIntegrable 0 endpoint)
  have normalized :
      Complex.exp (-coefficient * (endpoint : ℂ)) * weight endpoint = 1 := by
    dsimp only [weight]
    rw [← Complex.exp_add]
    simp
  have base : weight 0 = 1 := by simp [weight]
  have read := congrArg (fun z : ℂ => Complex.exp (-coefficient * (endpoint : ℂ)) * z) integral
  rw [mul_sub, ← mul_assoc, normalized, one_mul, base, one_mul,
    ← intervalIntegral.integral_const_mul] at read
  have kernel (time : ℝ) :
      Complex.exp (-coefficient * (endpoint : ℂ)) * (weight time * forcing time) =
      Complex.exp (-coefficient * ((endpoint : ℂ) - (time : ℂ))) * forcing time := by
    dsimp only [weight]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp only [kernel] at read
  exact (eq_add_of_sub_eq read.symm).trans (add_comm _ _)

end
end OriginalRieszFiniteResponse.Integration
