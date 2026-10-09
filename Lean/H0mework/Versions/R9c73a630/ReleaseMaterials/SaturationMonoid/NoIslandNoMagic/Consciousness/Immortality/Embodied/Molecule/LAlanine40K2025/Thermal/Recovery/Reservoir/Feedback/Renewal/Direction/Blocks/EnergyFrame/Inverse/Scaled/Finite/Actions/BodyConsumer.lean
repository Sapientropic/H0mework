import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions.Body
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.NetConsumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
open Collision Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

set_option maxRecDepth 4096 in
theorem received_body_energy_error (O : LoadedJoint) :
    |energy O (Quantum.conjugation calculatedReceivedWord preparedInput)-energy O finiteReceivedBody| ≤ (12/10^8 : ℝ)*‖O‖ := by
  have read : energy O (Quantum.conjugation calculatedReceivedWord preparedInput)-energy O finiteReceivedBody=
      energy O (Quantum.conjugation calculatedReceivedWord preparedInput-finiteReceivedBody) := by
    simp only [energy,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]
  rw [read]
  have bound := Input.energy_dimension_norm O (Quantum.conjugation calculatedReceivedWord preparedInput-finiteReceivedBody)
  have scaled := mul_le_mul_of_nonneg_left finite_received_body_error
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 38416) (norm_nonneg O))
  norm_num [PairController,Basis] at bound
  exact bound.trans (scaled.trans (by nlinarith [norm_nonneg O]))

theorem original_finite_received_energy_error (O : LoadedJoint) (hermitian : O.IsHermitian) :
    |energy O Source.received.joint-energy (Quantum.conjugation installedLoadFrame O) finiteReceivedBody| ≤ (53/10^7 : ℝ)*‖O‖ := by
  have input := Prepared.source_received_finite_energy_error O hermitian
  rw [received_read_in_calculated_frame] at input
  change |energy O Source.received.joint-energy (Quantum.conjugation installedLoadFrame O)
    (Quantum.conjugation calculatedReceivedWord preparedInput)| ≤ (51/10^7 : ℝ)*‖O‖ at input
  have body := received_body_energy_error (Quantum.conjugation installedLoadFrame O)
  have norm : ‖Quantum.conjugation installedLoadFrame O‖=‖O‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint installedLoadFrame) O
  rw [norm] at body
  have triangle := abs_sub_le (energy O Source.received.joint)
    (energy (Quantum.conjugation installedLoadFrame O) (Quantum.conjugation calculatedReceivedWord preparedInput))
    (energy (Quantum.conjugation installedLoadFrame O) finiteReceivedBody)
  linarith [norm_nonneg O]

def receivedNetGain : ℝ := energy (Quantum.conjugation installedLoadFrame Prepared.loadedNetObservable) finiteReceivedBody

theorem source_finite_received_net_cost :
    |(Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceEleven)-Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceNine))-
      receivedNetGain| ≤ (7/10^7 : ℝ) := by
  rw [Prepared.source_loaded_net_read]
  have paid := original_finite_received_energy_error Prepared.loadedNetObservable Prepared.loaded_net_hermitian
  exact paid.trans ((mul_le_mul_of_nonneg_left Prepared.loaded_net_norm (show (0 : ℝ) ≤ 53/10^7 by norm_num)).trans (by norm_num))

theorem original_finite_received_net_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      receivedNetGain| ≤ (78/10^7 : ℝ) := by
  have triangle := abs_sub_le
    (Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))
    (Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceEleven)-Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceNine))
    receivedNetGain
  linarith [SquareRoot.Full.source_original_PC_gain_error,source_finite_received_net_cost]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
