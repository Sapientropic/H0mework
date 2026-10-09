import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Algebra

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks

open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
theorem energy_norm_mass (O rho : Matrix ι ι ℂ) (positive : rho.PosSemidef) :
    |energy O rho| ≤ ‖O‖ * rho.trace.re := by
  let p := rho.trace.re
  have nonnegative : 0 ≤ p := (Complex.nonneg_iff.mp positive.trace_nonneg).1
  have traceReal : rho.trace = (p : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp positive.trace_nonneg).2.symm
  by_cases zero : p = 0
  · have rhoZero := positive.trace_eq_zero_iff.mp (traceReal.trans (by simp [zero]))
    simp [rhoZero, energy]
  let normalized : Matrix ι ι ℂ := p⁻¹ • rho
  have normalizedPositive : normalized.PosSemidef := positive.smul (inv_nonneg.mpr nonnegative)
  have normalizedTrace : normalized.trace = 1 := by
    dsimp only [normalized]
    rw [Matrix.trace_smul, traceReal]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr zero)
  have bound := Load.Producer.StrictThermal.energy_abs_le_norm O normalized
    normalizedPositive normalizedTrace
  change |energy O (p⁻¹ • rho)| ≤ ‖O‖ at bound
  rw [energy_real_smul, abs_mul, abs_of_nonneg (inv_nonneg.mpr nonnegative)] at bound
  have paid := mul_le_mul_of_nonneg_left bound nonnegative
  rw [← mul_assoc, mul_inv_cancel₀ zero, one_mul] at paid
  simpa only [mul_comm, p] using paid

theorem uniform_block_error [Fintype κ] {label : ι → κ} {O : Matrix ι ι ℂ}
    (kept : Preserves label O) (rho : Matrix ι ι ℂ) (positive : rho.PosSemidef)
    (approximation : ∀ k, Matrix {i // label i = k} {i // label i = k} ℂ)
    (epsilon : ℝ) (bounded : ∀ k, ‖restrict label k O - approximation k‖ ≤ epsilon) :
    |energy O rho - ∑ k, energy (approximation k) (restrict label k rho)| ≤
      epsilon * rho.trace.re := by
  have each k : |energy (restrict label k O) (restrict label k rho) -
      energy (approximation k) (restrict label k rho)| ≤
      epsilon * (restrict label k rho).trace.re := by
    have blockPositive : (restrict label k rho).PosSemidef := positive.submatrix Subtype.val
    have raw := energy_norm_mass (restrict label k O - approximation k) _ blockPositive
    rw [Load.Producer.HeatProbability.energy_sub_left] at raw
    exact raw.trans (mul_le_mul_of_nonneg_right (bounded k)
      (Complex.nonneg_iff.mp blockPositive.trace_nonneg).1)
  rw [energy_eq_sum_restrict kept, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k, |energy (restrict label k O) (restrict label k rho) -
      energy (approximation k) (restrict label k rho)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, epsilon * (restrict label k rho).trace.re := Finset.sum_le_sum (fun k _ => each k)
    _ = _ := by rw [← Finset.mul_sum, ← Complex.re_sum, ← trace_eq_sum_restrict]


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
