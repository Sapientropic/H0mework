import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedThermalInputs
import H0mework.Chemistry.LAlanineThermalDynamics.PartialSwapEnergyPopulation
import H0mework.Chemistry.LAlanineEntropy.FiniteThermalEntropy

/-! # The actual molecular preparation generates both targets and its population heat ledger -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Preparation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population
open scoped ComplexOrder ENNReal

noncomputable section

def generatedJoint : JointMatrix Basis := jointNext systemCurrent bathCurrent exchangeCosine exchangeSine
def generatedSystem : Matrix Basis Basis ℂ := systemReduce generatedJoint
def generatedBath : Matrix Basis Basis ℂ := bathReduce generatedJoint

theorem generatedJoint_posSemidef : generatedJoint.PosSemidef :=
  jointNext_posSemidef _ _ _ _ systemCurrent_posSemidef bathCurrent_posSemidef

theorem generatedJoint_trace : generatedJoint.trace = 1 := by
  rw [generatedJoint, jointNext_trace _ _ _ _ exchange_normalized, systemCurrent_trace, bathCurrent_trace]
  exact one_mul 1

theorem generatedSystem_posSemidef : generatedSystem.PosSemidef :=
  systemReduce_posSemidef _ generatedJoint_posSemidef

theorem generatedBath_posSemidef : generatedBath.PosSemidef :=
  bathReduce_posSemidef _ generatedJoint_posSemidef

theorem generatedSystem_trace : generatedSystem.trace = 1 := by
  rw [generatedSystem, systemReduce_trace, generatedJoint_trace]

theorem generatedBath_trace : generatedBath.trace = 1 := by
  rw [generatedBath, bathReduce_trace, generatedJoint_trace]

theorem generatedSystem_diagonal_nonnegative (i : Basis) : 0 ≤ (generatedSystem i i).re :=
  (Complex.nonneg_iff.mp generatedSystem_posSemidef.diag_nonneg).1

theorem generatedSystem_diagonal_normalized : ∑ i, (generatedSystem i i).re = 1 := by
  have trace := congrArg Complex.re generatedSystem_trace
  simpa only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.one_re] using trace

def generatedPopulation : PMF Basis :=
  PMF.ofFintype (fun i => ENNReal.ofReal (generatedSystem i i).re) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => generatedSystem_diagonal_nonnegative i),
      generatedSystem_diagonal_normalized, ENNReal.ofReal_one])

theorem generatedPopulation_toReal (i : Basis) :
    (generatedPopulation i).toReal = (generatedSystem i i).re :=
  ENNReal.toReal_ofReal (generatedSystem_diagonal_nonnegative i)

theorem generatedSystem_population_mixing (i : Basis) :
    (generatedSystem i i).re =
      exchangeCosine ^ 2 * (systemPopulation i).toReal +
        exchangeSine ^ 2 * (bathPopulation i).toReal := by
  rw [systemPopulation_toReal]
  exact systemPopulation_mixing systemCurrent (fun i => (bathPopulation i).toReal)
    exchangeCosine exchangeSine systemCurrent_trace (pmf_sum_toReal bathPopulation) i

theorem exchangeProbability_range : 0 ≤ exchangeSine ^ 2 ∧ exchangeSine ^ 2 ≤ 1 :=
  ⟨(collisionProbability_range _ _ exchange_normalized).1,
    (collisionProbability_range _ _ exchange_normalized).2.1⟩

theorem generatedPopulation_eq_collisionMixture :
    generatedPopulation = mixPMF systemPopulation bathPopulation (exchangeSine ^ 2)
      exchangeProbability_range.1 exchangeProbability_range.2 := by
  ext i
  apply (ENNReal.toReal_eq_toReal_iff' (generatedPopulation.apply_ne_top i)
    ((mixPMF _ _ _ _ _).apply_ne_top i)).mp
  rw [generatedPopulation_toReal, generatedSystem_population_mixing, mixPMF_apply_toReal,
    (collisionProbability_range _ _ exchange_normalized).2.2]

def systemHeat : ℝ := energy energyHamiltonian generatedSystem - energy energyHamiltonian systemCurrent
def bathHeat : ℝ := energy energyHamiltonian generatedBath - energy energyHamiltonian bathCurrent

theorem generatedHeat_conserved : systemHeat + bathHeat = 0 :=
  heatBalance energyHamiltonian systemCurrent bathCurrent exchangeCosine exchangeSine
    exchange_normalized systemCurrent_trace bathCurrent_trace

private theorem diagonalEnergy (state : Matrix Basis Basis ℂ) :
    energy energyHamiltonian state = ∑ i, sourceEnergies i * (state i i).re := by
  simp only [energy, energyHamiltonian, Matrix.trace, Matrix.diag, Matrix.diagonal_mul,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem systemHeat_eq_population : systemHeat =
    ∑ i, sourceEnergies i * ((generatedPopulation i).toReal - (systemPopulation i).toReal) := by
  simp only [systemHeat, diagonalEnergy, generatedPopulation_toReal, systemPopulation_toReal,
    mul_sub, Finset.sum_sub_distrib]

theorem collisionKL_heatEntropy_commutes :
    realKL systemPopulation bathPopulation - realKL generatedPopulation bathPopulation =
      entropy generatedPopulation - entropy systemPopulation - inverseTemperature * systemHeat := by
  rw [systemHeat_eq_population]
  exact klHeatEntropy_commutes sourceEnergies inverseTemperature systemPopulation generatedPopulation

theorem collisionPopulation_clausius :
    0 ≤ entropy generatedPopulation - entropy systemPopulation - inverseTemperature * systemHeat := by
  rw [systemHeat_eq_population]
  have fromDPI := mix_clausius sourceEnergies inverseTemperature systemPopulation
    (exchangeSine ^ 2) exchangeProbability_range.1 exchangeProbability_range.2
  change 0 ≤ entropy (mixPMF systemPopulation bathPopulation _ _ _) - entropy systemPopulation -
    inverseTemperature * ∑ i, sourceEnergies i *
      (((mixPMF systemPopulation bathPopulation _ _ _) i).toReal - (systemPopulation i).toReal) at fromDPI
  rw [← generatedPopulation_eq_collisionMixture] at fromDPI
  exact fromDPI

end

end LAlanine40K2025.Thermal.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
