import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! A source-valued mode response is a genuine Bochner convolution, so the same causal channel can consume complete quantum current operators. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem mode_derivative (rate : ℂ) (time : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (rate*(t : ℂ))) (rate*Complex.exp (rate*(time : ℂ))) time := by
  have linear := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt time (hasDerivAt_id time)
  have differentiated := (linear.const_mul rate).cexp
  simpa only [Function.comp_apply,Complex.ofRealCLM_apply,id_eq,Complex.ofReal_one,mul_one,mul_comm] using differentiated

def forcedVector (rate : ℂ) (source : ℝ → E) (time : ℝ) : E :=
  Complex.exp (rate*(time : ℂ)) • (∫ r in (0 : ℝ)..time, Complex.exp (-rate*(r : ℂ)) • source r)

omit [CompleteSpace E] in
theorem forcedVector_initial (rate : ℂ) (source : ℝ → E) : forcedVector rate source 0=0 := by
  simp [forcedVector]

theorem forcedVector_derivative (rate : ℂ) (source : ℝ → E) (continuousSource : Continuous source) (time : ℝ) :
    HasDerivAt (forcedVector rate source) (rate • forcedVector rate source time+source time) time := by
  have regular : Continuous (fun t : ℝ => Complex.exp (-rate*(t : ℂ)) • source t) := by fun_prop
  have integral := intervalIntegral.integral_hasDerivAt_right
    (regular.intervalIntegrable (μ := volume) 0 time)
    regular.aestronglyMeasurable.stronglyMeasurableAtFilter regular.continuousAt
  have generated := (mode_derivative rate time).smul integral
  have cancel : Complex.exp (rate*(time : ℂ))*Complex.exp (-rate*(time : ℂ))=1 := by
    rw [← Complex.exp_add]
    have zero : rate*(time : ℂ)+ -rate*(time : ℂ)=0 := by ring
    rw [zero,Complex.exp_zero]
  unfold forcedVector
  convert! generated using 1
  simp only [smul_smul,cancel,one_smul,add_comm]

omit [CompleteSpace E] in
theorem forcedVector_convolution (rate : ℂ) (source : ℝ → E) (time : ℝ) :
    forcedVector rate source time=∫ r in (0 : ℝ)..time, Complex.exp (rate*((time-r : ℝ) : ℂ)) • source r := by
  rw [forcedVector,← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [smul_smul,← Complex.exp_add]
  congr 2
  push_cast
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
