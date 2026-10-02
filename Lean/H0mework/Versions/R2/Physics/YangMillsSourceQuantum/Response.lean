import H0mework.Versions.R2.Physics.YangMillsSourceQuantum.Time
import H0mework.Versions.R2.Physics.QuantumObservation.Prediction

/-! The original clock's source-generated dark step reads the energy above
its existing bottom on the complete mother carrier. -/

set_option autoImplicit false
open scoped InnerProductSpace

namespace SaturationMonoid.PhysicsCore.YangMills.NativeSource

open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage9DEF
open Stage10.GaugeSpectrum FullPairing
noncomputable section

private theorem phase_dark (r : ℝ) (h : r = frequency ∨ r = -frequency) :
    phase r (Dynamics.timeDisplacement Observation.darkTime) =
      if r = frequency then Complex.I else -Complex.I := by
  have angle : Observation.darkTime * frequency = Real.pi/2 := by
    unfold Observation.darkTime
    field_simp [Dynamics.frequency_positive.ne']
  have neg_ne : -frequency ≠ frequency := by linarith [Dynamics.frequency_positive]
  rcases h with h | h <;> subst r
  · simp [phase, Dynamics.timeDisplacement_zero]
    have exponent : (Observation.darkTime : ℂ) * ((frequency : ℂ)*Complex.I) =
        ((Real.pi/2 : ℝ) : ℂ)*Complex.I := by
      rw [← mul_assoc, ← Complex.ofReal_mul, angle]
    rw [exponent, Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
    norm_num
  · simp only [if_neg neg_ne, phase, Dynamics.timeDisplacement_zero]
    have exponent : (Observation.darkTime : ℂ) * (((-frequency : ℝ) : ℂ)*Complex.I) =
        ((-(Real.pi/2) : ℝ) : ℂ)*Complex.I := by
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_neg, angle]
    rw [exponent, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    norm_num

theorem centered_dark_apply (v : Hilbert) (i : FullPairing.Index) :
    Quantum.Time.centered time (-frequency)
      (Multiplicative.ofAdd Observation.darkTime) v i =
        if i.1.val < 2 then v i else -v i := by
  have neg_ne : -frequency ≠ frequency := by linarith [Dynamics.frequency_positive]
  have scalar : Quantum.Generator.energyPhase (-frequency) Observation.darkTime = -Complex.I := by
    have source := phase_dark (-frequency) (Or.inr rfl)
    simp only [if_neg neg_ne] at source
    simpa only [Quantum.Generator.energyPhase, phase, Dynamics.timeDisplacement_zero, mul_assoc] using source
  change Quantum.Generator.energyPhase (-frequency) Observation.darkTime * clock Observation.darkTime v i = _
  rw [scalar, clock_apply]
  unfold spinRate Dynamics.rate
  by_cases upper : i.1.val < 2
  · rw [if_pos upper, if_pos upper, phase_dark _ (Or.inl rfl)]
    simp [← mul_assoc]
  · rw [if_neg upper, if_neg upper, phase_dark _ (Or.inr rfl), if_neg neg_ne]
    simp [← mul_assoc]

private theorem shifted_hamiltonian_apply (v : Hilbert) (i : FullPairing.Index) :
    (Quantum.Generator.hamiltonianOperator time (point v) + (frequency : ℂ) • v) i =
      if i.1.val < 2 then 0 else (2 * frequency : ℝ) * v i := by
  rw [hamiltonian_point]
  change Complex.I * velocity v i + (frequency : ℂ)*v i = _
  rw [velocity_apply]
  unfold spinRate Dynamics.rate
  by_cases upper : i.1.val ≤ 1 <;> simp [upper]
  all_goals ring_nf
  all_goals simp
  all_goals ring

theorem centered_pairing_response (v w : Hilbert) :
    inner ℂ (Quantum.Generator.hamiltonianOperator time (point v) + (frequency : ℂ) • v) w =
      ((frequency / 2 : ℝ) : ℂ) *
        inner ℂ
          (Quantum.Time.centered time (-frequency) (Multiplicative.ofAdd Observation.darkTime) v - v)
          (Quantum.Time.centered time (-frequency) (Multiplicative.ofAdd Observation.darkTime) w - w) := by
  let d (z : Hilbert) := Quantum.Time.centered time (-frequency)
    (Multiplicative.ofAdd Observation.darkTime) z - z
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change w i * star ((Quantum.Generator.hamiltonianOperator time (point v) +
    (frequency : ℂ) • v) i) = ((frequency/2 : ℝ) : ℂ) * (d w i * star (d v i))
  have difference (z : Hilbert) : d z i = (if i.1.val < 2 then z i else -z i) - z i := by
    change (Quantum.Time.centered time (-frequency) (Multiplicative.ofAdd Observation.darkTime) z) i - z i = _
    rw [centered_dark_apply]
  rw [shifted_hamiltonian_apply, difference, difference]
  by_cases upper : i.1.val < 2
  · simp [upper]
  · simp [upper, star_mul, Complex.conj_ofReal]
    ring

theorem centered_energy_response (v : Hilbert) :
    (inner ℂ (Quantum.Generator.hamiltonianOperator time (point v) + (frequency : ℂ) • v) v).re =
      frequency / 2 *
        ‖Quantum.Time.centered time (-frequency)
          (Multiplicative.ofAdd Observation.darkTime) v - v‖^2 := by
  have re := congrArg Complex.re (centered_pairing_response v v)
  let d := Quantum.Time.centered time (-frequency)
    (Multiplicative.ofAdd Observation.darkTime) v - v
  have norm : (inner ℂ d d).re = ‖d‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) d
  change (inner ℂ (Quantum.Generator.hamiltonianOperator time (point v) + (frequency : ℂ) • v) v).re =
    (((frequency / 2 : ℝ) : ℂ) * inner ℂ d d).re at re
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, norm] using re

end
end SaturationMonoid.PhysicsCore.YangMills.NativeSource
