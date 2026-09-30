import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedGramPreparation
import H0mework.Chemistry.LAlanineEntropy.FiniteGibbsPopulation

/-!
# One registered thermal preparation on the source-generated energy frame

Inverse temperature is in inverse Hartree. The exchange coefficients specify
one integrated interaction, not an unmeasured collision duration. The 40 K
crystallographic geometry does not supply a bath temperature.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Source

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Preparation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population
open scoped ComplexOrder ENNReal

noncomputable section

def inverseTemperature : ℝ := 1
def exchangeCosine : ℝ := 3 / 5
def exchangeSine : ℝ := 4 / 5

theorem inverseTemperature_positive : 0 < inverseTemperature := by norm_num [inverseTemperature]

theorem exchange_normalized : exchangeCosine ^ 2 + exchangeSine ^ 2 = 1 := by
  norm_num [exchangeCosine, exchangeSine]

def systemCurrent : Matrix Basis Basis ℂ := preparedEnergyDensity (collisionCurrentTime : ℝ)

theorem systemCurrent_posSemidef : systemCurrent.PosSemidef := preparedEnergyDensity_posSemidef _

theorem systemCurrent_trace : systemCurrent.trace = 1 := preparedEnergyDensity_trace _

def systemPopulation : PMF Basis :=
  PMF.ofFintype (fun i => ENNReal.ofReal (preparedPopulation (collisionCurrentTime : ℝ) i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun i _ => preparedPopulation_nonnegative (collisionCurrentTime : ℝ) i),
      preparedPopulation_normalized]
    simp)

theorem systemPopulation_toReal (i : Basis) :
    (systemPopulation i).toReal = (systemCurrent i i).re := by
  change (ENNReal.ofReal (preparedPopulation (collisionCurrentTime : ℝ) i)).toReal = _
  rw [ENNReal.toReal_ofReal (preparedPopulation_nonnegative _ _)]
  rfl

def bathPopulation : PMF Basis := gibbsPMF sourceEnergies inverseTemperature

def bathCurrent : Matrix Basis Basis ℂ :=
  Matrix.diagonal (fun i => ((bathPopulation i).toReal : ℂ))

theorem bathCurrent_posSemidef : bathCurrent.PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  exact Complex.zero_le_real.mpr ENNReal.toReal_nonneg

theorem bathCurrent_trace : bathCurrent.trace = 1 := by
  rw [bathCurrent, Matrix.trace_diagonal, ← Complex.ofReal_sum, pmf_sum_toReal]
  rfl

theorem bathPopulation_positive (i : Basis) : 0 < (bathPopulation i).toReal :=
  gibbsPMF_real_positive _ _ _

theorem bathPopulation_log (i : Basis) :
    Real.log (bathPopulation i).toReal =
      -inverseTemperature * sourceEnergies i -
        Real.log (partitionFunction sourceEnergies inverseTemperature) :=
  log_gibbsPMF _ _ _

def energyHamiltonian : Matrix Basis Basis ℂ :=
  Matrix.diagonal (fun i => (sourceEnergies i : ℂ))

theorem bath_commutes_with_energy : energyHamiltonian * bathCurrent = bathCurrent * energyHamiltonian := by
  rw [energyHamiltonian, bathCurrent, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end

end LAlanine40K2025.Thermal.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
