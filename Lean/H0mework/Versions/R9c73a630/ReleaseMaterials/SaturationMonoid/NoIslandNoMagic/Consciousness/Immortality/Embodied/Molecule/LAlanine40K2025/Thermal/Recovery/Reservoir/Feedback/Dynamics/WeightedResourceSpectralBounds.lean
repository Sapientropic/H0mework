import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.SpectralReservoir

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Resource

open Collision
open scoped Matrix ComplexOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem energy_weighted_spectral_bounds (H rho : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (positive : rho.PosSemidef) :
    hH.eigenvalues (Spectrum.lastIndex (ι := ι)) * rho.trace.re ≤ energy H rho ∧
      energy H rho ≤ hH.eigenvalues (Spectrum.firstIndex (ι := ι)) * rho.trace.re := by
  let p := rho.trace.re
  have nonnegative : 0 ≤ p := (Complex.nonneg_iff.mp positive.trace_nonneg).1
  have traceReal : rho.trace = (p : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp positive.trace_nonneg).2.symm
  by_cases zero : p = 0
  · have rhoZero := positive.trace_eq_zero_iff.mp (traceReal.trans (by simp [zero]))
    simp [rhoZero, energy]
  have positiveMass : 0 < p := lt_of_le_of_ne nonnegative (Ne.symm zero)
  let normalized := p⁻¹ • rho
  have normalizedPositive : normalized.PosSemidef := positive.smul (inv_nonneg.mpr nonnegative)
  have normalizedTrace : normalized.trace = 1 := by
    dsimp only [normalized]
    rw [Matrix.trace_smul, traceReal]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr zero)
  have source := Spectrum.energy_spectral_bounds H normalized hH normalizedPositive normalizedTrace
  have read : p * energy H normalized = energy H rho := by
    change p * ((H * (p⁻¹ • rho)).trace.re) = (H * rho).trace.re
    rw [Matrix.mul_smul, Matrix.trace_smul]
    simp only [Complex.smul_re, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ zero, one_mul]
  constructor
  · have bound := mul_le_mul_of_nonneg_left source.1 positiveMass.le
    rw [read] at bound
    simpa only [mul_comm, p] using bound
  · have bound := mul_le_mul_of_nonneg_left source.2 positiveMass.le
    rw [read] at bound
    simpa only [mul_comm, p] using bound

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Resource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
