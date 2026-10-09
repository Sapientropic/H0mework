import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Producer.SourceGeneratedReservoirWork

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Thermo

open Load.Source Load.Producer Powered.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Current
open scoped Matrix ComplexOrder
noncomputable section

def systemEntropy (current : State) : ℝ := Quantum.spectralEntropy (systemReduce current.joint)
  (systemReduce_posSemidef _ current.positive) ((systemReduce_trace _).trans current.normalized)

def referenceEntropy : ℝ := Quantum.spectralEntropy referencePair referencePair_positive referencePair_trace

def freeEnergy (current : State) : ℝ :=
  Readout.pcEnergy current + Readout.donorEnergy current - systemEntropy current + Physical.boundaryEnergy current

theorem entropy_energy_read (current : State) :
    Current.entropyProduction current = systemEntropy current - referenceEntropy +
      (EnergyLedger.environmentEnergy current - Population.meanEnergy environmentEnergies environmentPMF) := by
  simp only [Current.entropyProduction, Load.Quantum.entropyProduction, Load.Quantum.environmentEnergyChange,
    one_mul, systemEntropy, referenceEntropy, EnergyLedger.environmentEnergy, environmentHamiltonian_eq]
  rfl

theorem complete_account (current : State) :
    freeEnergy current + Current.entropyProduction current =
      Physical.baselineEnergy current - referenceEntropy - Population.meanEnergy environmentEnergies environmentPMF := by
  rw [entropy_energy_read, EnergyLedger.baseline_split]
  unfold freeEnergy
  ring

theorem supply_systemEntropy (current : State) : systemEntropy (supplyNext current) = systemEntropy current := by
  unfold systemEntropy
  apply Quantum.spectralEntropy_eq_of_charpoly
  rw [supplyNext_pair]
  exact Work.Capacity.conjugated_charpoly _ _

theorem supply_entropy (current : State) : Current.entropyProduction (supplyNext current) = Current.entropyProduction current := by
  rw [entropy_energy_read, entropy_energy_read, supply_systemEntropy, EnergyLedger.supply_environment_energy]

theorem supply_net_account (current : State) :
    (freeEnergy (supplyNext current) - freeEnergy current) +
      (Current.entropyProduction (supplyNext current) - Current.entropyProduction current) = Physical.sourceWork current := by
  rw [Physical.sourceWork_actual]
  linarith [complete_account current, complete_account (supplyNext current)]

theorem load_net_account (current : State) :
    (freeEnergy (loadNext current) - freeEnergy current) +
      (Current.entropyProduction (loadNext current) - Current.entropyProduction current) = 0 := by
  have after := complete_account (loadNext current)
  rw [EnergyLedger.load_preserves_baseline] at after
  linarith [complete_account current]

def donorEntropy : ℝ := Quantum.spectralEntropy Source.donor Source.donor_positive Source.donor_trace

theorem reference_entropy_split :
    referenceEntropy = Quantum.spectralEntropy loadParentCurrent.joint
      loadParentCurrent.positive loadParentCurrent.normalized + donorEntropy :=
  Quantum.spectralEntropy_kronecker loadParentCurrent.joint Source.donor
    loadParentCurrent.positive Source.donor_positive loadParentCurrent.normalized Source.donor_trace

theorem initial_systemEntropy : systemEntropy initial = loadPCEntropy Source.received + donorEntropy := by
  unfold systemEntropy
  simp only [initial_pair, Source.pairOrigin]
  exact Quantum.spectralEntropy_kronecker (Load.Producer.RecoveryLedger.pcRead Source.received).joint Source.donor
    (Load.Producer.RecoveryLedger.pcRead Source.received).positive Source.donor_positive
    (Load.Producer.RecoveryLedger.pcRead Source.received).normalized Source.donor_trace

theorem initial_environmentEnergy :
    EnergyLedger.environmentEnergy initial = Load.Source.environmentEnergy Source.received.joint := by
  rw [EnergyLedger.environment_body, initial_body]

theorem initial_retains_paid_entropy : Current.entropyProduction initial = loadEntropyProduction Source.received := by
  rw [entropy_energy_read, initial_systemEntropy, reference_entropy_split, initial_environmentEnergy,
    loadEntropy_energyRead Source.received]
  ring

theorem first_retains_paid_entropy :
    Current.entropyProduction (supplyNext initial) = loadEntropyProduction Source.received := by
  rw [supply_entropy, initial_retains_paid_entropy]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Thermo
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
