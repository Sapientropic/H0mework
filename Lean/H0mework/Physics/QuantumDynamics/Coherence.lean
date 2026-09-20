import H0mework.Physics.QuantumDynamics.TimeJet
import H0mework.Physics.QuantumState.StateSource

/-! The cross-chirality matrix entry is an actual density readout. Its physical
time derivative is nonzero, excluding a trajectory containing only global phase. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Dynamics

open Matrix ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9C.Material.SpinPair Source State

noncomputable section

def coherence (point : BasePoint) : ℂ := density point (0, 1) (2, 1)

theorem coherence_eq_vector (point : BasePoint) :
    coherence point = vector point (0, 1) * star (vector point (2, 1)) := by
  rw [coherence, density_eq_pureMatrix]
  rfl

theorem phase_rate_add (first second : ℝ) (point : BasePoint) :
    phase (first + second) point = phase first point * phase second point := by
  simp [phase, add_mul, mul_add, Complex.exp_add]

theorem coherence_formula (point : BasePoint) :
    coherence point = phase (2 * frequency) point / 4 := by
  rw [coherence_eq_vector]
  change (upperPhase point / 2) * star (lowerPhase point / 2) = _
  rw [star_div₀, star_ofNat, lowerPhase, phase_star, neg_neg]
  rw [show 2 * frequency = frequency + frequency by ring, phase_rate_add]
  unfold upperPhase
  ring

theorem coherence_zero : coherence 0 = 1 / 4 := by
  rw [coherence_formula, phase_zero]

theorem frequency_positive : 0 < frequency := by
  have difference : 0 < spinScale - gaugeScale := by
    rw [gaugeScale]
    nlinarith [spinScale_pos]
  exact mul_pos (div_pos (mul_pos (by norm_num) lapse_pos) (by norm_num)) difference

theorem coherence_hasDerivAt (time : ℝ) :
    HasDerivAt (fun t : ℝ => coherence (timeDisplacement t))
      (coherence (timeDisplacement time) * ((2 * frequency : ℝ) : ℂ) * Complex.I) time := by
  have value := ((phaseCoefficient_hasDerivAt time (0, 1)).mul
    (phaseCoefficient_hasDerivAt time (0, 1))).mul_const (1 / 4)
  have same_derivative :
      ((phaseCoefficient (timeDisplacement time) (0, 1) * generator (0, 1)) *
        phaseCoefficient (timeDisplacement time) (0, 1) +
        phaseCoefficient (timeDisplacement time) (0, 1) *
          (phaseCoefficient (timeDisplacement time) (0, 1) * generator (0, 1))) * (1 / 4) =
      coherence (timeDisplacement time) * ((2 * frequency : ℝ) : ℂ) * Complex.I := by
    rw [coherence_formula]
    rw [show 2 * frequency = frequency + frequency by ring, phase_rate_add]
    change ((phase frequency (timeDisplacement time) * ((frequency : ℂ) * Complex.I)) *
      phase frequency (timeDisplacement time) + phase frequency (timeDisplacement time) *
        (phase frequency (timeDisplacement time) * ((frequency : ℂ) * Complex.I))) * (1 / 4) = _
    push_cast
    ring
  have same_function :
      (fun t : ℝ => coherence (timeDisplacement t)) =
        (fun t : ℝ => phaseCoefficient (timeDisplacement t) (0, 1) *
          phaseCoefficient (timeDisplacement t) (0, 1) * (1 / 4)) := by
    funext t
    rw [coherence_formula]
    rw [show 2 * frequency = frequency + frequency by ring, phase_rate_add]
    change phase frequency (timeDisplacement t) * phase frequency (timeDisplacement t) / 4 =
      phase frequency (timeDisplacement t) * phase frequency (timeDisplacement t) * (1 / 4)
    ring
  rw [same_function]
  exact value.congr_deriv same_derivative

theorem coherence_derivative_ne_zero (time : ℝ) :
    coherence (timeDisplacement time) * ((2 * frequency : ℝ) : ℂ) * Complex.I ≠ 0 := by
  apply mul_ne_zero _ Complex.I_ne_zero
  apply mul_ne_zero
  · rw [coherence_formula]
    exact div_ne_zero (Complex.exp_ne_zero _) (by norm_num)
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos (by norm_num) frequency_positive))

theorem coherence_globalPhase (point reference : BasePoint) (scalar : ℂ)
    (unit : star scalar * scalar = 1)
    (same : vector point = scalar • vector reference) :
    coherence point = coherence reference := by
  rw [coherence_eq_vector, coherence_eq_vector, same]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul]
  calc
    _ = (star scalar * scalar) *
      (vector reference (0, 1) * star (vector reference (2, 1))) := by ring
    _ = _ := by rw [unit, one_mul]

theorem not_only_global_phase :
    ¬ (∀ time : ℝ, ∃ scalar : ℂ, star scalar * scalar = 1 ∧
      vector (timeDisplacement time) = scalar • vector 0) := by
  intro only_phase
  have constant : (fun time : ℝ => coherence (timeDisplacement time)) =
      (fun _ : ℝ => coherence 0) := by
    funext time
    obtain ⟨scalar, unit, same⟩ := only_phase time
    exact coherence_globalPhase _ _ scalar unit same
  have actual_derivative := coherence_hasDerivAt 0
  rw [constant] at actual_derivative
  exact coherence_derivative_ne_zero 0
    (actual_derivative.unique (hasDerivAt_const 0 (coherence 0)))

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Dynamics
