import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.Coordinates

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem finite_body_energy_norm (O : LoadedJoint) (hermitian : O.IsHermitian) :
    |energy O Actions.finiteReceivedBody| ≤ (1+(53/10^7 : ℝ))*‖O‖ := by
  let back := Quantum.conjugation (star installedLoadFrame) O
  have norm : ‖back‖=‖O‖ := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint (star installedLoadFrame)) O
  have herm : back.IsHermitian := Prepared.conjugation_hermitian (star installedLoadFrame) O hermitian
  have forward : Quantum.conjugation installedLoadFrame back=O := Supply.conjugation_undo installedLoadFrame O
  have comparison := Actions.original_finite_received_energy_error back herm
  rw [forward,norm] at comparison
  have source := energy_abs_le_norm back Source.received.joint Source.received.positive Source.received.normalized
  rw [norm] at source
  have triangle := abs_add_le (energy O Actions.finiteReceivedBody-energy back Source.received.joint)
    (energy back Source.received.joint)
  rw [sub_add_cancel,abs_sub_comm] at triangle
  nlinarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
