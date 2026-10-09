import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.Ancilla

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
open Collision Load.Source Load.Producer.StrictThermal Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def donorReadout (O : Current.FullJoint) : LoadedJoint :=
  ancillaReadout Source.donor Source.donor_positive (O.submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm)

theorem donor_readout_energy (O : Current.FullJoint) (rho : LoadedJoint) :
    energy O (Incidence.receivedJoint rho Source.donor)=energy (donorReadout O) rho := by
  have unshuffle : (Incidence.receivedJoint rho Source.donor).submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm=
      Matrix.kronecker rho Source.donor := by
    ext i j
    change (Matrix.kronecker rho Source.donor) (Incidence.bodyReservoir (Incidence.bodyReservoir.symm i))
      (Incidence.bodyReservoir (Incidence.bodyReservoir.symm j))=_
    simp only [Equiv.apply_symm_apply]
  rw [← Input.reindex_energy Incidence.bodyReservoir.symm O (Incidence.receivedJoint rho Source.donor),unshuffle,ancilla_readout_energy]
  rfl

theorem donor_readout_norm (O : Current.FullJoint) (hermitian : O.IsHermitian) : ‖donorReadout O‖ ≤ ‖O‖ := by
  apply (ancilla_readout_norm Source.donor Source.donor_positive Source.donor_trace _ (hermitian.submatrix Incidence.bodyReservoir.symm)).trans
  exact le_of_eq (Finite.reindex_norm Incidence.bodyReservoir.symm O)

theorem donor_readout_hermitian (O : Current.FullJoint) (hermitian : O.IsHermitian) :
    (donorReadout O).IsHermitian :=
  ancilla_readout_hermitian Source.donor Source.donor_positive _ (hermitian.submatrix Incidence.bodyReservoir.symm)

def supplyReadout (O : Current.FullJoint) : LoadedJoint :=
  donorReadout (Quantum.conjugation (star (Current.pulse (nativeClockStep : ℝ))) O)

theorem supply_readout_energy (O : Current.FullJoint) :
    energy O Thermal.Recovery.Reservoir.Pointer.received.joint=energy (supplyReadout O) Source.received.joint := by
  rw [Thermal.Recovery.Reservoir.Pointer.received,Current.supplyNext_joint,Current.initial_receives_actual]
  have read : energy O (Quantum.conjugation (Current.pulse (nativeClockStep : ℝ)) (Incidence.receivedJoint Source.received.joint Source.donor))=
      energy (Quantum.conjugation (star (Current.pulse (nativeClockStep : ℝ))) O) (Incidence.receivedJoint Source.received.joint Source.donor) :=
    energy_pullback O _ _
  rw [read,donor_readout_energy]
  rfl

theorem supply_readout_norm (O : Current.FullJoint) (hermitian : O.IsHermitian) : ‖supplyReadout O‖ ≤ ‖O‖ := by
  have h := conjugation_hermitian (star (Current.pulse (nativeClockStep : ℝ))) O hermitian
  apply (donor_readout_norm _ h).trans
  exact le_of_eq (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ Current.FullJoint (star (Current.pulse (nativeClockStep : ℝ)))) O)

theorem supply_readout_hermitian (O : Current.FullJoint) (hermitian : O.IsHermitian) :
    (supplyReadout O).IsHermitian :=
  donor_readout_hermitian _ (conjugation_hermitian (star (Current.pulse (nativeClockStep : ℝ))) O hermitian)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
