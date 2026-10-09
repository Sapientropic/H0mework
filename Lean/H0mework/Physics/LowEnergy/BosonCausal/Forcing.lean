import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual zero-initial forced modes are Bochner integrals, with their ODE
and the retarded convolution identity derived rather than supplied. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
open MeasureTheory
noncomputable section

def forcedMode (rate : ℂ) (source : ℝ → ℂ) (time : ℝ) : ℂ :=
  Complex.exp (rate*(time : ℂ))*(∫ s : ℝ in (0 : ℝ)..time, Complex.exp (-rate*(s : ℂ))*source s)

theorem forcedMode_zero (rate : ℂ) (source : ℝ → ℂ) : forcedMode rate source 0=0 := by
  simp [forcedMode]

private theorem complex_mode_derivative (rate : ℂ) (time : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (rate*(t : ℂ))) (rate*Complex.exp (rate*(time : ℂ))) time := by
  have linear := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt time (hasDerivAt_id time)
  have exponent := (linear.const_mul rate).cexp
  simpa only [Function.comp_apply,Complex.ofRealCLM_apply,id_eq,Complex.ofReal_one,mul_one,mul_comm] using exponent

theorem forcedMode_derivative (rate : ℂ) (source : ℝ → ℂ) (continuousSource : Continuous source) (time : ℝ) :
    HasDerivAt (forcedMode rate source) (rate*forcedMode rate source time+source time) time := by
  have regular : Continuous (fun t : ℝ => Complex.exp (-rate*(t : ℂ))*source t) := by fun_prop
  have integral := intervalIntegral.integral_hasDerivAt_right
    (regular.intervalIntegrable (μ := volume) 0 time)
    regular.aestronglyMeasurable.stronglyMeasurableAtFilter regular.continuousAt
  have generated := (complex_mode_derivative rate time).mul integral
  unfold forcedMode
  convert! generated using 1
  have cancel : Complex.exp (rate*(time : ℂ))*Complex.exp (-rate*(time : ℂ))=1 := by
    rw [← Complex.exp_add]
    have zero : rate*(time : ℂ)+ -rate*(time : ℂ)=0 := by ring
    rw [zero,Complex.exp_zero]
  calc
    _ = (rate*Complex.exp (rate*(time : ℂ)))*
        (∫ s : ℝ in (0 : ℝ)..time, Complex.exp (-rate*(s : ℂ))*source s)+source time := by ring
    _ = _ := by rw [mul_assoc,← mul_assoc (Complex.exp (rate*(time : ℂ))),cancel,one_mul]

theorem forcedMode_convolution (rate : ℂ) (source : ℝ → ℂ) (time : ℝ) :
    forcedMode rate source time=∫ s : ℝ in (0 : ℝ)..time, Complex.exp (rate*((time-s : ℝ) : ℂ))*source s := by
  rw [forcedMode,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

def zeroPastMode (rate : ℂ) (source : ℝ → ℂ) (time : ℝ) : ℂ :=
  if 0≤time then forcedMode rate source time else 0

theorem zeroPastMode_past (rate : ℂ) (source : ℝ → ℂ) (time : ℝ) (past : time<0) :
    zeroPastMode rate source time=0 := by simp [zeroPastMode,not_le.mpr past]

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
