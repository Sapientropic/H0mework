import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedRememberedPair
import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedQuantumThermalLedger

/-!
# Cumulative entropy follows the remembered pair, not a reset bath

The reference is the original prepared product. A later step's entropy balance
is a signed change of correlation and bath free energy; neither is reset to zero.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Producer

open Preparation Collision Population Quantum
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open scoped ComplexOrder

noncomputable section

def rememberedSystemEntropy (elapsed : ℝ) : ℝ :=
  spectralEntropy (rememberedSystem elapsed) (rememberedSystem_posSemidef elapsed) (rememberedSystem_trace elapsed)
def rememberedBathEntropy (elapsed : ℝ) : ℝ :=
  spectralEntropy (rememberedBath elapsed) (rememberedBath_posSemidef elapsed) (rememberedBath_trace elapsed)
def rememberedJointEntropy (elapsed : ℝ) : ℝ :=
  spectralEntropy (rememberedJoint elapsed) (rememberedJoint_posSemidef elapsed) (rememberedJoint_trace elapsed)

def rememberedSystemHeat (elapsed : ℝ) : ℝ :=
  energy energyHamiltonian (rememberedSystem elapsed) - energy energyHamiltonian systemCurrent
def rememberedBathHeat (elapsed : ℝ) : ℝ :=
  energy energyHamiltonian (rememberedBath elapsed) - energy energyHamiltonian bathCurrent

theorem rememberedHeat_conserved (elapsed : ℝ) :
    rememberedSystemHeat elapsed + rememberedBathHeat elapsed = 0 := by
  have total := rememberedPair_reducedEnergy elapsed
  have original := generatedHeat_conserved
  unfold rememberedSystemHeat rememberedBathHeat
  unfold systemHeat bathHeat at original
  linarith

theorem rememberedJointEntropy_preserved (elapsed : ℝ) :
    rememberedJointEntropy elapsed = sourceSystemEntropy + sourceBathEntropy :=
  (rememberedJoint_entropy elapsed).trans targetJointEntropy_preserved

def rememberedCorrelation (elapsed : ℝ) : ℝ :=
  rememberedSystemEntropy elapsed + rememberedBathEntropy elapsed - rememberedJointEntropy elapsed

theorem rememberedCorrelation_nonnegative (elapsed : ℝ) : 0 ≤ rememberedCorrelation elapsed :=
  sub_nonneg.mpr (quantum_entropy_subadditive (rememberedJoint elapsed)
    (rememberedJoint_posSemidef elapsed) (rememberedJoint_trace elapsed))

def rememberedBathGibbsExcess (elapsed : ℝ) : ℝ :=
  inverseTemperature * rememberedBathHeat elapsed - (rememberedBathEntropy elapsed - sourceBathEntropy)

theorem rememberedBathGibbsExcess_nonnegative (elapsed : ℝ) : 0 ≤ rememberedBathGibbsExcess elapsed := by
  have bound := quantumGibbs_freeEnergy_nonnegative sourceEnergies inverseTemperature (rememberedBath elapsed)
    (rememberedBath_posSemidef elapsed) (rememberedBath_trace elapsed)
  unfold rememberedBathGibbsExcess rememberedBathHeat rememberedBathEntropy
  rw [sourceBathEntropy_eq_population, sourceBathEnergy_eq_population]
  exact bound

def rememberedEntropyProduction (elapsed : ℝ) : ℝ :=
  rememberedSystemEntropy elapsed - sourceSystemEntropy - inverseTemperature * rememberedSystemHeat elapsed

theorem rememberedQuantumEntropy_disposition (elapsed : ℝ) :
    rememberedEntropyProduction elapsed = rememberedCorrelation elapsed + rememberedBathGibbsExcess elapsed := by
  have exchange : rememberedBathHeat elapsed = -rememberedSystemHeat elapsed := by
    linarith [rememberedHeat_conserved elapsed]
  unfold rememberedEntropyProduction rememberedCorrelation rememberedBathGibbsExcess
  rw [rememberedJointEntropy_preserved, exchange]
  ring

theorem rememberedQuantum_clausius (elapsed : ℝ) : 0 ≤ rememberedEntropyProduction elapsed := by
  rw [rememberedQuantumEntropy_disposition]
  exact add_nonneg (rememberedCorrelation_nonnegative elapsed) (rememberedBathGibbsExcess_nonnegative elapsed)

/-- This step readout retains the actual incoming state and can have either sign. -/
def rememberedStepEntropy (current target : ℝ) : ℝ :=
  rememberedSystemEntropy target - rememberedSystemEntropy current - inverseTemperature *
    (energy energyHamiltonian (rememberedSystem target) - energy energyHamiltonian (rememberedSystem current))

theorem rememberedStepEntropy_eq_difference (current target : ℝ) :
    rememberedStepEntropy current target = rememberedEntropyProduction target - rememberedEntropyProduction current := by
  unfold rememberedStepEntropy rememberedEntropyProduction rememberedSystemHeat
  ring

theorem rememberedStepEntropy_disposition (current target : ℝ) :
    rememberedStepEntropy current target =
      (rememberedCorrelation target - rememberedCorrelation current) +
      (rememberedBathGibbsExcess target - rememberedBathGibbsExcess current) := by
  rw [rememberedStepEntropy_eq_difference, rememberedQuantumEntropy_disposition,
    rememberedQuantumEntropy_disposition]
  ring

end

end LAlanine40K2025.Thermal.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
