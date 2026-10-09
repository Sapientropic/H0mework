import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input.Pair

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
open Propagation.Interface Load.Source Powered.Dynamics
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def baseBody : LoadedJoint := Matrix.kronecker (chargedInput pairPreparation) environmentState

def completeReceivedWord : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  receivedWord * Load.Quantum.localUnitary (Load.Quantum.localUnitary pairWord 1) 1

theorem prepared_body_from_pair : preparedBody=Quantum.conjugation
    (Load.Quantum.localUnitary (Load.Quantum.localUnitary pairWord 1) 1) baseBody := by
  have charged : chargedInput Powered.Producer.sourceReceivedPair=
      Quantum.conjugation (Load.Quantum.localUnitary pairWord 1) (chargedInput pairPreparation) := by
    rw [source_pair_from_preparation]
    exact tensor_left_action pairWord pairPreparation excitedController
  rw [preparedBody,charged]
  exact tensor_left_action (Load.Quantum.localUnitary pairWord 1) (chargedInput pairPreparation) environmentState

theorem original_received_full_word : Source.received.joint=Quantum.conjugation completeReceivedWord baseBody := by
  rw [original_received_from_preparation,prepared_body_from_pair,Environment.conjugation_comp]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Input
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
