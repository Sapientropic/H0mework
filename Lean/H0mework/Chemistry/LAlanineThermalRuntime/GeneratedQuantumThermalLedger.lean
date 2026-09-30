import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedThermalCollision
import H0mework.Chemistry.LAlanineEntropy.QuantumSubadditivity
import H0mework.Chemistry.LAlanineEntropy.QuantumGibbsBound
import H0mework.Chemistry.LAlanineEntropy.SpectralTensorEntropy

/-! # Complete quantum entropy disposition of the same molecular collision -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Preparation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Quantum
open scoped ComplexOrder ENNReal

noncomputable section

def sourceSystemEntropy : ℝ := spectralEntropy systemCurrent systemCurrent_posSemidef systemCurrent_trace
def sourceBathEntropy : ℝ := spectralEntropy bathCurrent bathCurrent_posSemidef bathCurrent_trace
def targetSystemEntropy : ℝ := spectralEntropy generatedSystem generatedSystem_posSemidef generatedSystem_trace
def targetBathEntropy : ℝ := spectralEntropy generatedBath generatedBath_posSemidef generatedBath_trace
def targetJointEntropy : ℝ := spectralEntropy generatedJoint generatedJoint_posSemidef generatedJoint_trace

def collisionUnitary : Matrix.unitaryGroup (Basis × Basis) ℂ :=
  ⟨partialSwap exchangeCosine exchangeSine, partialSwap_unitary _ _ exchange_normalized⟩

theorem sourceProduct_trace : (Matrix.kronecker systemCurrent bathCurrent).trace = 1 := by
  dsimp only [Matrix.kronecker]
  rw [Matrix.trace_kronecker, systemCurrent_trace, bathCurrent_trace, mul_one]

theorem targetJointEntropy_preserved : targetJointEntropy = sourceSystemEntropy + sourceBathEntropy := by
  have invariant := spectralEntropy_unitary_conjugation (Matrix.kronecker systemCurrent bathCurrent)
    (systemCurrent_posSemidef.kronecker bathCurrent_posSemidef) sourceProduct_trace collisionUnitary
  have additive := spectralEntropy_kronecker systemCurrent bathCurrent
    systemCurrent_posSemidef bathCurrent_posSemidef systemCurrent_trace bathCurrent_trace
  exact invariant.trans additive

theorem sourceBathEntropy_eq_population : sourceBathEntropy = entropy bathPopulation :=
  spectralEntropy_diagonal bathPopulation

theorem sourceBathEnergy_eq_population : energy energyHamiltonian bathCurrent =
    meanEnergy sourceEnergies bathPopulation := by
  simp only [energy, energyHamiltonian, bathCurrent, Matrix.trace, Matrix.diag, Matrix.diagonal_mul,
    Matrix.diagonal_apply_eq, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, meanEnergy]

def quantumMutualInformation : ℝ := targetSystemEntropy + targetBathEntropy - targetJointEntropy

theorem quantumMutualInformation_nonnegative : 0 ≤ quantumMutualInformation :=
  sub_nonneg.mpr (quantum_entropy_subadditive generatedJoint generatedJoint_posSemidef generatedJoint_trace)

/-- Excess bath free energy, including its full spectral entropy rather than only populations. -/
def bathGibbsExcess : ℝ := inverseTemperature * bathHeat - (targetBathEntropy - sourceBathEntropy)

theorem bathGibbsExcess_nonnegative : 0 ≤ bathGibbsExcess := by
  have bound := quantumGibbs_freeEnergy_nonnegative sourceEnergies inverseTemperature generatedBath
    generatedBath_posSemidef generatedBath_trace
  unfold bathGibbsExcess bathHeat targetBathEntropy
  rw [sourceBathEntropy_eq_population, sourceBathEnergy_eq_population]
  exact bound

def quantumEntropyProduction : ℝ :=
  targetSystemEntropy - sourceSystemEntropy - inverseTemperature * systemHeat

/-- Correlation and disturbed bath are both paid by the same actual joint successor. -/
theorem fullQuantumEntropy_disposition :
    quantumEntropyProduction = quantumMutualInformation + bathGibbsExcess := by
  have exchange : bathHeat = -systemHeat := by linarith [generatedHeat_conserved]
  unfold quantumEntropyProduction quantumMutualInformation bathGibbsExcess
  rw [targetJointEntropy_preserved, exchange]
  ring

theorem collisionQuantum_clausius : 0 ≤ quantumEntropyProduction := by
  rw [fullQuantumEntropy_disposition]
  exact add_nonneg quantumMutualInformation_nonnegative bathGibbsExcess_nonnegative

end

end LAlanine40K2025.Thermal.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
