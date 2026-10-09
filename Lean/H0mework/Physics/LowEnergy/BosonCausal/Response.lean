import H0mework.Physics.LowEnergy.BosonCausal.Forcing
import H0mework.Physics.LowEnergy.BosonCausal.Source

/-! Actual source convolutions generate the two second-order response fields;
the instantaneous term acts directly, as the unit-mass contact requires. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
open MeasureTheory
noncomputable section

def pairForced (rate : ℂ) (source : ℝ → ℂ) (time : ℝ) : ℂ :=
  (forcedMode rate source time-forcedMode (-rate) source time)/(2*rate)

def pairVelocity (rate : ℂ) (source : ℝ → ℂ) (time : ℝ) : ℂ :=
  (forcedMode rate source time+forcedMode (-rate) source time)/2

theorem pairForced_derivative (rate : ℂ) (nonzero : rate≠0)
    (source : ℝ → ℂ) (continuousSource : Continuous source) (time : ℝ) :
    HasDerivAt (pairForced rate source) (pairVelocity rate source time) time := by
  have generated := ((forcedMode_derivative rate source continuousSource time).sub
    (forcedMode_derivative (-rate) source continuousSource time)).div_const (2*rate)
  unfold pairForced pairVelocity
  convert! generated using 1
  field_simp [nonzero]
  ring

theorem pairVelocity_derivative (rate : ℂ)
    (source : ℝ → ℂ) (continuousSource : Continuous source) (time : ℝ) :
    HasDerivAt (pairVelocity rate source) (rate^2*pairForced rate source time+source time) time := by
  have generated := ((forcedMode_derivative rate source continuousSource time).add
    (forcedMode_derivative (-rate) source continuousSource time)).div_const 2
  unfold pairForced pairVelocity
  convert! generated using 1
  field_simp
  ring

theorem pairForced_initial (rate : ℂ) (source : ℝ → ℂ) : pairForced rate source 0=0 ∧ pairVelocity rate source 0=0 := by
  simp [pairForced,pairVelocity,forcedMode_zero]

def responseTo (source : ℝ → ℂ) (time : ℝ) : ℂ :=
  contact*source time+oscillationWeight*pairForced (Complex.I*(oscillation : ℂ)) source time+
    growthWeight*pairForced (growth : ℂ) source time

def causalResponseTo (source : ℝ → ℂ) (time : ℝ) : ℂ := if 0≤time then responseTo source time else 0

theorem response_zero_past (source : ℝ → ℂ) (time : ℝ) (past : time<0) : causalResponseTo source time=0 := by
  simp [causalResponseTo,not_le.mpr past]

theorem response_initial (source : ℝ → ℂ) : responseTo source 0=contact*source 0 := by
  simp [responseTo,pairForced_initial]

theorem responseTo_generated_second_order (source : ℝ → ℂ) (continuousSource : Continuous source) (time : ℝ) :
    HasDerivAt (pairForced (Complex.I*(oscillation : ℂ)) source)
      (pairVelocity (Complex.I*(oscillation : ℂ)) source time) time ∧
    HasDerivAt (pairVelocity (Complex.I*(oscillation : ℂ)) source)
      (-(648/125 : ℂ)*pairForced (Complex.I*(oscillation : ℂ)) source time+source time) time ∧
    HasDerivAt (pairForced (growth : ℂ) source) (pairVelocity (growth : ℂ) source time) time ∧
    HasDerivAt (pairVelocity (growth : ℂ) source)
      ((50/3 : ℂ)*pairForced (growth : ℂ) source time+source time) time := by
  have onz : Complex.I*(oscillation : ℂ)≠0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr oscillation_positive.ne')
  have gnz : (growth : ℂ)≠0 := Complex.ofReal_ne_zero.mpr growth_positive.ne'
  have os : (Complex.I*(oscillation : ℂ))^2= -(648/125 : ℂ) := by
    rw [mul_pow,Complex.I_sq,← Complex.ofReal_pow,oscillation_squared]
    norm_num
  have gs : (growth : ℂ)^2=(50/3 : ℂ) := by rw [← Complex.ofReal_pow,growth_squared]; norm_num
  refine ⟨pairForced_derivative _ onz _ continuousSource time,?_,pairForced_derivative _ gnz _ continuousSource time,?_⟩
  · simpa only [os] using pairVelocity_derivative (Complex.I*(oscillation : ℂ)) source continuousSource time
  · simpa only [gs] using pairVelocity_derivative (growth : ℂ) source continuousSource time

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
