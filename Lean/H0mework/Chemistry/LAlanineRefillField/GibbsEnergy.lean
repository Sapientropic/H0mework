import H0mework.Chemistry.LAlanineRefillField.GramEnergy
import Mathlib.Analysis.Complex.ExponentialBounds
import H0mework.Chemistry.LAlanineEntropy.QuantumGibbsBound

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.GibbsEnergy

open Collision Population Quantum Propagation.Interface Propagation.Source
open scoped Matrix ComplexOrder
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem entropy_nonnegative (p : PMF ι) : 0 ≤ entropy p := by
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i _
  have upper : (p i).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) (p.coe_le_one i)
  exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
    (Real.log_nonpos ENNReal.toReal_nonneg upper)

variable [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [DecidableEq ι] in
theorem entropy_le_log_card (p : PMF ι) : entropy p ≤ Real.log (Fintype.card ι) := by
  have bound : 0 ≤ realKL p (gibbsPMF (fun _ : ι => 0) 1) := ENNReal.toReal_nonneg
  rw [realKL_gibbs] at bound
  simp only [meanEnergy, zero_mul, Finset.sum_const_zero, mul_zero, add_zero,
    partitionFunction, mul_zero, Real.exp_zero,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at bound
  linarith

theorem gibbs_mean_le_probe (energies : ι → ℝ) (rho : Matrix ι ι ℂ)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1) :
    meanEnergy energies (gibbsPMF energies 1) ≤
      energy (Matrix.diagonal (fun i => (energies i : ℂ))) rho + Real.log (Fintype.card ι) := by
  have bound := quantumGibbs_freeEnergy_nonnegative energies 1 rho positive normalized
  have retained : 0 ≤ spectralEntropy rho positive normalized := entropy_nonnegative _
  have equilibrium := entropy_le_log_card (gibbsPMF energies 1)
  linarith

theorem log_ninetyEight_lt_five : Real.log (98 : ℝ) < 5 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 98)).mpr
  have lower : (8 / 3 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have powered : (8 / 3 : ℝ) ^ 5 < (Real.exp 1) ^ 5 := by gcongr
  have exponential : Real.exp (5 : ℝ) = (Real.exp 1) ^ 5 := by
    simp
  rw [exponential]
  norm_num at powered
  linarith

def basisProbe : Matrix Basis Basis ℂ :=
  Matrix.diagonal (fun i => ((PMF.pure (0 : Basis) i).toReal : ℂ))

theorem basisProbe_positive : basisProbe.PosSemidef := diagonal_pmf_positive _

theorem basisProbe_trace : basisProbe.trace = 1 := diagonal_pmf_trace _

theorem basisProbe_energy : energy (activeMatrix electronicSource) basisProbe =
    (activeMatrix electronicSource 0 0).re := by
  simp [energy, basisProbe, Matrix.trace, Matrix.diag, Matrix.mul_diagonal,
    PMF.pure_apply, apply_ite]

theorem source_bath_mean_lt_neg_thirteen :
    energy Thermal.Source.energyHamiltonian Thermal.Source.bathCurrent < -13 := by
  have probePositive := Preparation.energyCoordinates_posSemidef basisProbe_positive
  have probeTrace := (Preparation.energyCoordinates_trace basisProbe).trans basisProbe_trace
  have upper := gibbs_mean_le_probe Preparation.sourceEnergies
    (Preparation.energyCoordinates basisProbe) probePositive probeTrace
  have read : energy Thermal.Source.energyHamiltonian (Preparation.energyCoordinates basisProbe) =
      (activeMatrix electronicSource 0 0).re := by
    have invariant := Work.Capacity.energy_unitary_conjugation
      (activeMatrix electronicSource) basisProbe (star Preparation.sourceEnergyFrame)
    change energy (Quantum.conjugation (star Preparation.sourceEnergyFrame) (activeMatrix electronicSource))
      (Quantum.conjugation (star Preparation.sourceEnergyFrame) basisProbe) = _ at invariant
    rw [Powered.Source.sourceHamiltonian_in_shared_frame] at invariant
    rw [Powered.Source.sourceCoordinates_as_conjugation] at invariant
    rw [invariant, basisProbe_energy]
  have bathRead : energy Thermal.Source.energyHamiltonian Thermal.Source.bathCurrent =
      meanEnergy Preparation.sourceEnergies (gibbsPMF Preparation.sourceEnergies 1) := by
    simp [energy, Thermal.Source.energyHamiltonian, Thermal.Source.bathCurrent,
      Thermal.Source.bathPopulation, Thermal.Source.inverseTemperature, meanEnergy,
      Matrix.trace, Matrix.diag, Complex.re_sum, Complex.mul_re]
  change meanEnergy Preparation.sourceEnergies (gibbsPMF Preparation.sourceEnergies 1) ≤
    energy Thermal.Source.energyHamiltonian (Preparation.energyCoordinates basisProbe) + Real.log 98 at upper
  rw [read] at upper
  rw [bathRead]
  linarith [SourcePrimitive.source_H00_lt, log_ninetyEight_lt_five]

end
end LAlanine40K2025.Thermal.Recovery.GibbsEnergy
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
