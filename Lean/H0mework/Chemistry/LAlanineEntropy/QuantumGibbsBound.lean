import H0mework.Chemistry.LAlanineEntropy.SpectralEntropy
import H0mework.Chemistry.LAlanineThermalDynamics.PartialSwapEnergyPopulation

/-! # The Gibbs free-energy bound for a complete quantum state, including coherence -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Quantum

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population
open scoped ComplexOrder ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
theorem diagonalEnergy_eq_mean (energies : ι → ℝ) (rho : SystemMatrix ι)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    energy (Matrix.diagonal (fun i => (energies i : ℂ))) rho =
      meanEnergy energies (diagonalPMF rho positive normalized) := by
  simp only [energy, meanEnergy, diagonalPMF_toReal, Matrix.trace, Matrix.diag,
    Matrix.diagonal_mul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- Coherence is retained in spectralEntropy; only the energy measurement is coarse-grained. -/
theorem quantumGibbs_freeEnergy_nonnegative (energies : ι → ℝ) (beta : ℝ)
    (rho : SystemMatrix ι) (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    0 ≤ beta * (energy (Matrix.diagonal (fun i => (energies i : ℂ))) rho -
        meanEnergy energies (gibbsPMF energies beta)) -
      (spectralEntropy rho positive normalized - entropy (gibbsPMF energies beta)) := by
  let measured := diagonalPMF rho positive normalized
  have measuredBound : 0 ≤ realKL measured (gibbsPMF energies beta) := ENNReal.toReal_nonneg
  rw [realKL_gibbs] at measuredBound
  have equilibrium := realKL_gibbs energies beta (gibbsPMF energies beta)
  simp only [realKL, InformationTheory.klDiv_self, ENNReal.toReal_zero] at equilibrium
  have retained := spectralEntropy_le_diagonal rho positive normalized
  rw [diagonalEnergy_eq_mean energies rho positive normalized]
  dsimp only [measured] at measuredBound
  nlinarith

end

end LAlanine40K2025.Thermal.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
