import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.SourceGeneratedLAlanineLoadFreeEnergy

/-! # Changed actual environment energy forces a strict Gibbs cost -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer

open Population
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Quantum
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open scoped ComplexOrder ENNReal

noncomputable section

theorem quantumGibbs_freeEnergy_pos_of_energy_ne {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (energies : ι → ℝ) (beta : ℝ) (rho : Collision.SystemMatrix ι)
    (positive : rho.PosSemidef) (normalized : rho.trace = 1)
    (changed : Collision.energy (Matrix.diagonal (fun i => (energies i : ℂ))) rho ≠
      meanEnergy energies (gibbsPMF energies beta)) :
    0 < beta * (Collision.energy (Matrix.diagonal (fun i => (energies i : ℂ))) rho -
        meanEnergy energies (gibbsPMF energies beta)) -
      (spectralEntropy rho positive normalized - entropy (gibbsPMF energies beta)) := by
  let measured := diagonalPMF rho positive normalized
  have different : measured ≠ gibbsPMF energies beta := by
    intro equal
    apply changed
    rw [diagonalEnergy_eq_mean energies rho positive normalized]
    exact congrArg (meanEnergy energies) equal
  have klPositive : 0 < realKL measured (gibbsPMF energies beta) := by
    apply ENNReal.toReal_pos
    · intro zero
      exact different (PMF.toMeasure_injective (InformationTheory.klDiv_eq_zero_iff.mp zero))
    · exact gibbs_kl_finite energies beta measured
  rw [realKL_gibbs] at klPositive
  have equilibrium := realKL_gibbs energies beta (gibbsPMF energies beta)
  simp only [realKL, InformationTheory.klDiv_self, ENNReal.toReal_zero] at equilibrium
  have retained := spectralEntropy_le_diagonal rho positive normalized
  rw [diagonalEnergy_eq_mean energies rho positive normalized]
  dsimp only [measured] at klPositive
  nlinarith

theorem loadGibbsExcess_pos_of_environment_changed (current : LoadState)
    (changed : environmentEnergy current.joint ≠ environmentEnergy loadInitialState.joint) :
    0 < loadGibbsExcess current := by
  rw [loadEnvironmentEnergy_initial] at changed
  have energyChanged : Collision.energy (Matrix.diagonal (fun i => (environmentEnergies i : ℂ)))
      (controllerReduce current.joint) ≠ meanEnergy environmentEnergies environmentPMF := by
    simpa only [environmentEnergy, controllerEnergy, environmentHamiltonian_eq] using changed
  exact quantumGibbs_freeEnergy_pos_of_energy_ne environmentEnergies 1 (controllerReduce current.joint)
    (controllerReduce_posSemidef _ current.positive)
    ((controllerReduce_trace _).trans current.normalized) energyChanged

theorem loadEntropy_pos_of_environment_changed (current : LoadState)
    (changed : environmentEnergy current.joint ≠ environmentEnergy loadInitialState.joint) :
    0 < loadEntropyProduction current := by
  have gibbs := loadGibbsExcess_pos_of_environment_changed current changed
  have mutualNonnegative : 0 ≤ loadMutualInformation current :=
    Load.Quantum.jointMutualInformation_nonnegative _ _ _ _ _ _
  rw [loadEntropy_disposition]
  linarith

end

end LAlanine40K2025.Thermal.Load.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
