import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Producer.SourceGeneratedPointerThermalReference

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Live

open Load.Source Powered.Dynamics Collision
open scoped Matrix ComplexOrder
noncomputable section

attribute [local irreducible] thermalJoint sourceInitial

def systemEntropy (current : State) : ℝ :=
  Quantum.spectralEntropy (Powered.Dynamics.systemReduce (thermalJoint current))
    (Powered.Dynamics.systemReduce_posSemidef _ (thermalJoint_positive current))
    ((Powered.Dynamics.systemReduce_trace _).trans (thermalJoint_trace current))

def referenceEntropy : ℝ :=
  Quantum.spectralEntropy referenceSystem referenceSystem_positive referenceSystem_trace

def environmentEnergy (current : State) : ℝ :=
  energy (Matrix.diagonal (fun e => (environmentEnergies e : ℂ)))
    (controllerReduce (thermalJoint current))

def freeEnergy (current : State) : ℝ :=
  baselineEnergy current - environmentEnergy current - systemEntropy current

theorem entropy_energy_read (current : State) :
    entropyProduction current = systemEntropy current - referenceEntropy +
      (environmentEnergy current - Population.meanEnergy environmentEnergies environmentPMF) := by
  simp only [entropyProduction, Load.Quantum.entropyProduction, Load.Quantum.environmentEnergyChange,
    systemEntropy, referenceEntropy, environmentEnergy, thermalJoint_generated, one_mul]
  rfl

theorem complete_account (current : State) :
    freeEnergy current + entropyProduction current =
      baselineEnergy current - referenceEntropy - Population.meanEnergy environmentEnergies environmentPMF := by
  rw [entropy_energy_read]
  unfold freeEnergy
  ring

theorem measureNext_net_account (current : State) :
    (freeEnergy (measureNext current) - freeEnergy current) +
      (entropyProduction (measureNext current) - entropyProduction current) = measurementWork current := by
  rw [measurementWork_actual]
  linarith [complete_account current, complete_account (measureNext current)]

theorem loadNext_net_account (current : State) :
    (freeEnergy (loadNext current) - freeEnergy current) +
      (entropyProduction (loadNext current) - entropyProduction current) = 0 := by
  have next := complete_account (loadNext current)
  rw [loadNext_preserves_baseline] at next
  linarith [complete_account current]

theorem initial_reference_entropy : referenceEntropy = Thermo.referenceEntropy :=
  prepared_entropy Current.referencePair Current.referencePair_positive Current.referencePair_trace

theorem initial_baseline_energy : baselineEnergy initial = Physical.baselineEnergy received := by
  rw [baselineEnergy_split, initial_joint, sourceInitial_pointerEnergy]
  have body : bodyRead sourceInitial = received.joint := by
    rw [sourceInitial, prepared_bodyRead]
  rw [body, add_zero]
  rfl

theorem initial_freeEnergy : freeEnergy initial = Thermo.freeEnergy received := by
  have old := Thermo.complete_account received
  have extended := complete_account initial
  rw [initial_baseline_energy, initial_reference_entropy, initial_entropyProduction] at extended
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Live
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
