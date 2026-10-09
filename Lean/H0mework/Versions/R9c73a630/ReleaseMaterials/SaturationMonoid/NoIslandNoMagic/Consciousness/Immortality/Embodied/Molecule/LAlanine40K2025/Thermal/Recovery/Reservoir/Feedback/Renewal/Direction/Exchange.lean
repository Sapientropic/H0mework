import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.ExchangeComparison
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.TransitionProbability

/-! # Conditional exchange energy and the near-return bound

These local matrix calculations retain the exchange coherence of arbitrary correlated inputs.
The weighted bound normalizes a positive conditional block internally and restores its actual mass.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction

open Collision Load.Producer.StrictThermal
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem raw_expansion (rho : JointMatrix ι) (c s : ℝ) :
    partialSwap c s * rho * (partialSwap c s)ᴴ =
      c ^ 2 • rho + s ^ 2 • (swapOperator * rho * swapOperator) +
        (c * s) • (Complex.I • (rho * swapOperator - swapOperator * rho)) := by
  rw [partialSwap_adjoint]
  simp only [partialSwap, sub_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_mul]
  ring_nf
  simp [Complex.I_sq]

theorem swapped_system (rho : JointMatrix ι) :
    systemReduce (swapOperator * rho * swapOperator) = bathReduce rho := by
  ext i j
  change (∑ a : ι, ((swapOperator * rho * swapOperator : JointMatrix ι)) (i, a) (j, a)) =
    ∑ a : ι, rho (a, i) (a, j)
  simp only [mul_swap_apply, swap_mul_apply]

/-- The energy contraction of the full exchange commutator, before any diagonal readout. -/
def coherence (H : SystemMatrix ι) (rho : JointMatrix ι) : ℝ :=
  energy (Matrix.kronecker H 1) (Complex.I • (rho * swapOperator - swapOperator * rho))

omit [DecidableEq ι] in
theorem energy_real_smul (H rho : SystemMatrix ι) (a : ℝ) :
    energy H (a • rho) = a * energy H rho := by
  simp only [energy, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem exchange_energy (H : SystemMatrix ι) (rho : JointMatrix ι) (angle : ℝ) :
    energy H (systemReduce (Quantum.conjugation (Exchange.exchangeUnitary angle) rho)) =
      Real.cos angle ^ 2 * energy H (systemReduce rho) +
        Real.sin angle ^ 2 * energy H (bathReduce rho) +
        (Real.cos angle * Real.sin angle) * coherence H rho := by
  rw [← Exchange.left_energy]
  simp only [Quantum.conjugation_apply, Exchange.exchangeUnitary, Matrix.star_eq_conjTranspose]
  rw [raw_expansion]
  simp only [Load.Producer.HeatProbability.energy_add_right,
    energy_real_smul]
  rw [Exchange.left_energy, Exchange.left_energy, swapped_system]
  rfl

section Bound
variable [Nonempty ι]

omit [Nonempty ι] in
theorem exchange_pi_conjugation (rho : JointMatrix ι) :
    Quantum.conjugation (Exchange.exchangeUnitary Real.pi) rho = rho := by
  simp [Quantum.conjugation_apply, Exchange.exchangeUnitary, partialSwap]

theorem exchange_pi_error (epsilon : ℝ) :
    ‖(Exchange.exchangeUnitary (ι := ι) (Real.pi - epsilon) : JointMatrix ι) -
      (Exchange.exchangeUnitary (ι := ι) Real.pi : JointMatrix ι)‖ ≤ 2 * |epsilon| := by
  have difference :
      (Exchange.exchangeUnitary (ι := ι) (Real.pi - epsilon) : JointMatrix ι) -
        (Exchange.exchangeUnitary (ι := ι) Real.pi : JointMatrix ι) =
      ((1 - Real.cos epsilon : ℝ) : ℂ) • 1 -
        (Complex.I * (Real.sin epsilon : ℂ)) • swapOperator := by
    change partialSwap (Real.cos (Real.pi - epsilon)) (Real.sin (Real.pi - epsilon)) -
      partialSwap (Real.cos Real.pi) (Real.sin Real.pi) = _
    simp only [Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi, Real.sin_pi,
      partialSwap, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero,
      mul_zero, zero_smul, sub_zero, Complex.ofReal_sub]
    module
  rw [difference]
  calc
    _ ≤ ‖((1 - Real.cos epsilon : ℝ) : ℂ) • (1 : JointMatrix ι)‖ +
      ‖(Complex.I * (Real.sin epsilon : ℂ)) • (swapOperator : JointMatrix ι)‖ := norm_sub_le _ _
    _ = |1 - Real.cos epsilon| + |Real.sin epsilon| := by
      rw [norm_smul, norm_smul, norm_one, swap_norm, mul_one, mul_one,
        Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
      simp only [Real.norm_eq_abs]
    _ ≤ |epsilon| + |epsilon| := add_le_add
      (by simpa only [Real.cos_zero, sub_zero, abs_sub_comm] using
        Real.abs_cos_sub_cos_le epsilon 0) Real.abs_sin_le_abs
    _ = _ := by ring

omit [Nonempty ι] in
theorem weighted_observable_error (O rho : SystemMatrix ι) (positive : rho.PosSemidef)
    (U V : Matrix.unitaryGroup ι ℂ) :
    |energy O (Quantum.conjugation U rho) - energy O (Quantum.conjugation V rho)| ≤
      2 * ‖O‖ * ‖(U : SystemMatrix ι) - V‖ * rho.trace.re := by
  let p := rho.trace.re
  have nonnegative : 0 ≤ p := (Complex.nonneg_iff.mp positive.trace_nonneg).1
  have traceReal : rho.trace = (p : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp positive.trace_nonneg).2.symm
  by_cases zero : p = 0
  · have rhoZero := positive.trace_eq_zero_iff.mp (traceReal.trans (by simp [zero]))
    simp [rhoZero, Quantum.conjugation_apply, energy]
  let normalized : SystemMatrix ι := p⁻¹ • rho
  have normalizedPositive : normalized.PosSemidef := positive.smul (inv_nonneg.mpr nonnegative)
  have normalizedTrace : normalized.trace = 1 := by
    dsimp only [normalized]
    rw [Matrix.trace_smul, traceReal]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr zero)
  have bound := Exchange.unitary_observable_error O normalized normalizedPositive normalizedTrace U V
  have read (W : Matrix.unitaryGroup ι ℂ) :
      energy O (Quantum.conjugation W normalized) = p⁻¹ * energy O (Quantum.conjugation W rho) := by
    simp only [normalized, Quantum.conjugation_apply, Matrix.mul_smul, Matrix.smul_mul,
      energy_real_smul]
  change |energy O (Quantum.conjugation U normalized) -
    energy O (Quantum.conjugation V normalized)| ≤ _ at bound
  rw [read, read, ← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr nonnegative)] at bound
  have paid := mul_le_mul_of_nonneg_left bound nonnegative
  rw [← mul_assoc, mul_inv_cancel₀ zero, one_mul] at paid
  simpa only [mul_comm, p] using paid

theorem near_pi_energy_error (H : SystemMatrix ι) (rho : JointMatrix ι)
    (positive : rho.PosSemidef) (epsilon : ℝ) :
    |energy H (systemReduce (Quantum.conjugation
      (Exchange.exchangeUnitary (Real.pi - epsilon)) rho)) - energy H (systemReduce rho)| ≤
        4 * ‖H‖ * |epsilon| * rho.trace.re := by
  have bound := weighted_observable_error (Matrix.kronecker H 1) rho positive
    (Exchange.exchangeUnitary (Real.pi - epsilon)) (Exchange.exchangeUnitary Real.pi)
  rw [exchange_pi_conjugation, Exchange.left_energy, Exchange.left_energy] at bound
  refine bound.trans ?_
  have normH := NonUnitalStarAlgHom.norm_apply_le (Load.Producer.StrictThermal.tensorLeft (κ := ι)) H
  change ‖Matrix.kronecker H 1‖ ≤ ‖H‖ at normH
  have normU := exchange_pi_error (ι := ι) epsilon
  have mass : 0 ≤ rho.trace.re := (Complex.nonneg_iff.mp positive.trace_nonneg).1
  calc
    _ ≤ 2 * ‖H‖ * (2 * |epsilon|) * rho.trace.re := by gcongr
    _ = _ := by ring

end Bound

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
