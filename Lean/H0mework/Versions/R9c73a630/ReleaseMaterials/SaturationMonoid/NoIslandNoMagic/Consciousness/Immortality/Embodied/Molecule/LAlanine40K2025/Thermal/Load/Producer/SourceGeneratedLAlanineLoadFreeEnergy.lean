import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.SourceGeneratedLAlanineLoadCurrent

/-! # Binding-accounted free-energy readout of the actual load occurrence

At the source-fixed inverse temperature one, the complete PC marginal supplies its
entropy and free energy. PC includes its original interaction; the CE boundary energy
is retained separately. The actual energy and entropy producers pay every balance.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open scoped Matrix ComplexOrder

noncomputable section

/-- Full spectral entropy of the actual PC marginal, retaining its coherence. -/
def loadPCEntropy (current : LoadState) : ℝ :=
  Thermal.Quantum.spectralEntropy (systemReduce current.joint)
    (systemReduce_posSemidef _ current.positive)
    ((systemReduce_trace _).trans current.normalized)

/-- The source fixes β = 1 and PC energy includes the original PC interaction. -/
def loadPCFreeEnergy (current : LoadState) : ℝ := pcEnergy current.joint - loadPCEntropy current

/-- This balance includes the actual CE binding energy and permits any energy zero point. -/
def loadBindingAccountedFreeEnergy (current : LoadState) : ℝ :=
  loadPCFreeEnergy current + boundaryEnergy current.joint

theorem environmentHamiltonian_eq :
    controllerHamiltonian 2 = Matrix.diagonal (fun i => (environmentEnergies i : ℂ)) := by
  unfold controllerHamiltonian
  congr 1
  funext i
  fin_cases i <;> norm_num [environmentEnergies]

/-- Reads the entropy producer using the same environmental energy as the actual energy ledger. -/
theorem loadEntropy_energyRead (current : LoadState) :
    loadEntropyProduction current = loadPCEntropy current -
      Thermal.Quantum.spectralEntropy loadParentCurrent.joint
        loadParentCurrent.positive loadParentCurrent.normalized +
      (environmentEnergy current.joint - Population.meanEnergy environmentEnergies environmentPMF) := by
  simp only [loadEntropyProduction, Load.Quantum.entropyProduction,
    Load.Quantum.environmentEnergyChange, one_mul, loadPCEntropy,
    environmentEnergy, controllerEnergy, environmentHamiltonian_eq]
  rfl

/-- Every actual next exchanges signed entropy production for binding-accounted free energy. -/
theorem loadStateNext_freeEnergyBalance (current : LoadState) :
    loadBindingAccountedFreeEnergy (loadStateNext current) -
      loadBindingAccountedFreeEnergy current =
        -(loadEntropyProduction (loadStateNext current) - loadEntropyProduction current) := by
  have balance := loadStateNext_energyBalance current
  rw [loadEntropy_energyRead, loadEntropy_energyRead]
  unfold loadBindingAccountedFreeEnergy loadPCFreeEnergy
  linarith

private theorem loadPCEntropy_initial :
    loadPCEntropy loadInitialState = Thermal.Quantum.spectralEntropy loadParentCurrent.joint
      loadParentCurrent.positive loadParentCurrent.normalized := by
  simp only [loadPCEntropy, loadInitialState_received, loadInitialJoint,
    systemReduce_tensor, environmentState_trace, one_smul]

theorem loadEnvironmentEnergy_initial :
    environmentEnergy loadInitialState.joint =
      Population.meanEnergy environmentEnergies environmentPMF := by
  simp only [environmentEnergy, controllerEnergy, loadInitialState_received,
    loadInitialJoint, controllerReduce_tensor, loadParentCurrent.normalized, one_smul,
    environmentHamiltonian_eq, Collision.energy, environmentState,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Population.meanEnergy,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- The once-prepared Gibbs environment and the actual PC origin pay zero initial production. -/
theorem loadEntropy_initial_zero : loadEntropyProduction loadInitialState = 0 := by
  rw [loadEntropy_energyRead, loadPCEntropy_initial, loadEnvironmentEnergy_initial]
  ring

/-- The first actual load step pays its complete entropy production from this free-energy account. -/
theorem loadFirst_entropy_paid :
    loadEntropyProduction (loadStateNext loadInitialState) =
      loadBindingAccountedFreeEnergy loadInitialState -
        loadBindingAccountedFreeEnergy (loadStateNext loadInitialState) := by
  have balance := loadStateNext_freeEnergyBalance loadInitialState
  rw [loadEntropy_initial_zero] at balance
  linarith

/-- The first actual debit is nonnegative by the source-generated Gibbs entropy disposition. -/
theorem loadFirst_freeEnergyDebit_nonnegative :
    0 ≤ loadBindingAccountedFreeEnergy loadInitialState -
      loadBindingAccountedFreeEnergy (loadStateNext loadInitialState) := by
  rw [← loadFirst_entropy_paid]
  exact loadEntropy_nonnegative _

end

end LAlanine40K2025.Thermal.Load.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
