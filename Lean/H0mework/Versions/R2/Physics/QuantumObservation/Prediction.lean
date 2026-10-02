import H0mework.Versions.R2.Physics.QuantumObservation.Interference
import H0mework.Versions.R2.Physics.QuantumDynamics.Coherence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! A prediction of the already fixed classical source. The observation does
not feed into the source parameters, field equations, preparation or evolution. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Observation

open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage9DEF.Dynamics

noncomputable section

theorem source_frequency_squared : frequency ^ 2 = 972 / 3125 := by
  have form : frequency = 3 * lapse * spinScale / 5 := by
    unfold frequency gaugeScale
    ring
  rw [form]
  calc
    (3 * lapse * spinScale / 5) ^ 2 =
      9 * lapse ^ 2 * spinScale ^ 2 / 25 := by ring
    _ = 972 / 3125 := by rw [lapse_sq, spinScale_sq]; norm_num

theorem coherentWeight_cos (point : BasePoint) :
    coherentWeight point = Real.cos (point 0 * frequency) ^ 2 := by
  rw [coherentWeight_formula]
  have average : (upperPhase point + lowerPhase point) / 2 =
      (Real.cos (point 0 * frequency) : ℂ) := by
    unfold upperPhase lowerPhase phase
    have exponent (r : ℝ) :
        (point 0 : ℂ) * ((r : ℂ) * Complex.I) =
          ((point 0 * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
    simp_rw [exponent, Complex.exp_ofReal_mul_I]
    simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  rw [average]
  rw [Complex.normSq_ofReal, pow_two]

/-- The first dark contact in the source's coordinate-time units. -/
def darkTime : ℝ := Real.pi / (2 * frequency)

theorem darkTime_positive : 0 < darkTime :=
  div_pos Real.pi_pos (mul_pos (by norm_num) frequency_positive)

theorem prediction_dark : coherentWeight (timeDisplacement darkTime) = 0 := by
  rw [coherentWeight_cos, timeDisplacement_zero]
  have phase_at : darkTime * frequency = Real.pi / 2 := by
    unfold darkTime
    field_simp [ne_of_gt frequency_positive]
  rw [phase_at, Real.cos_pi_div_two]
  norm_num

theorem prediction_return : coherentWeight (timeDisplacement (2 * darkTime)) = 1 := by
  rw [coherentWeight_cos, timeDisplacement_zero]
  have phase_at : 2 * darkTime * frequency = Real.pi := by
    unfold darkTime
    field_simp [ne_of_gt frequency_positive]
  rw [phase_at, Real.cos_pi]
  norm_num

theorem prediction_excludes_dephasing :
    coherentWeight (timeDisplacement darkTime) ≠ exclusiveWeight (timeDisplacement darkTime) := by
  rw [prediction_dark, exclusiveWeight_formula]
  norm_num

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Observation
