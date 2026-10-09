import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.Donor

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
open Collision Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem original_finite_donor_energy_error (O : Current.FullJoint) :
    |energy (Prepared.donorReadout O) Source.received.joint-energy (finiteDonorReadout O) Source.received.joint| ≤
      (19208/10^9 : ℝ)*‖O‖ := by
  have original : energy (Prepared.donorReadout O) Source.received.joint=
      energy (O.submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm)
        (Matrix.kronecker Source.received.joint Source.donor) :=
    (Prepared.ancilla_readout_energy Source.donor Source.donor_positive _ Source.received.joint).symm
  rw [original,finite_donor_readout_energy,Input.energy_tensor_sub_right]
  have bound := Input.tensor_energy_norm_right (O.submatrix Incidence.bodyReservoir.symm Incidence.bodyReservoir.symm)
    (Source.donor-sourceFiniteDonor) Source.received.joint (Source.donor_positive.isHermitian.sub finite_donor_positive.isHermitian)
    Source.received.positive
  rw [Source.received.normalized,Complex.one_re,mul_one,Finite.reindex_norm] at bound
  norm_num [PairController,Basis] at bound
  apply bound.trans
  have scaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left original_finite_donor_error (show (0 : ℝ) ≤ 19208 by norm_num)) (norm_nonneg O)
  simpa only [div_eq_mul_inv,mul_assoc,one_mul] using scaled

def suppliedNetObservable : Current.FullJoint :=
  Quantum.conjugation (star (Current.pulse (nativeClockStep : ℝ))) (Prepared.pointerReadout Prepared.finiteRootGain)

def finiteLoadedNetObservable : LoadedJoint := finiteDonorReadout suppliedNetObservable

theorem supplied_net_hermitian : suppliedNetObservable.IsHermitian :=
  Prepared.conjugation_hermitian _ _ (Prepared.pointer_readout_hermitian _ Prepared.finite_root_gain_hermitian)

theorem supplied_net_norm : ‖suppliedNetObservable‖ ≤ (124/1000 : ℝ) := by
  have same := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ Current.FullJoint (star (Current.pulse (nativeClockStep : ℝ))))
    (Prepared.pointerReadout Prepared.finiteRootGain)
  exact same.le.trans ((Prepared.pointer_readout_norm _ Prepared.finite_root_gain_hermitian).trans Prepared.finite_root_gain_norm)

theorem finite_loaded_net_hermitian : finiteLoadedNetObservable.IsHermitian :=
  finite_donor_readout_hermitian suppliedNetObservable supplied_net_hermitian

theorem finite_loaded_net_norm : ‖finiteLoadedNetObservable‖ ≤ (124/1000 : ℝ) :=
  (finite_donor_readout_norm suppliedNetObservable supplied_net_hermitian).trans supplied_net_norm

theorem source_finite_donor_net_cost :
    |(Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceEleven)-Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceNine))-
      energy finiteLoadedNetObservable Source.received.joint| ≤ (24/10^7 : ℝ) := by
  rw [Prepared.source_loaded_net_read]
  have bound := original_finite_donor_energy_error suppliedNetObservable
  exact bound.trans ((mul_le_mul_of_nonneg_left supplied_net_norm (show (0 : ℝ) ≤ 19208/10^9 by norm_num)).trans (by norm_num))

def finiteDonorNetGain : ℝ :=
  energy (Quantum.conjugation installedLoadFrame finiteLoadedNetObservable) Actions.finiteReceivedBody

theorem finite_donor_input_net_cost :
    |energy finiteLoadedNetObservable Source.received.joint-finiteDonorNetGain| ≤ (7/10^7 : ℝ) := by
  have paid := Actions.original_finite_received_energy_error finiteLoadedNetObservable finite_loaded_net_hermitian
  exact paid.trans ((mul_le_mul_of_nonneg_left finite_loaded_net_norm (show (0 : ℝ) ≤ 53/10^7 by norm_num)).trans (by norm_num))

theorem original_finite_donor_net_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      finiteDonorNetGain| ≤ (102/10^7 : ℝ) := by
  have first := abs_sub_le
    (Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))
    (Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceEleven)-Resource.pcEnergyOf (bodyRead SquareRoot.Full.sourceNine))
    (energy finiteLoadedNetObservable Source.received.joint)
  have second := abs_sub_le
    (Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))
    (energy finiteLoadedNetObservable Source.received.joint) finiteDonorNetGain
  linarith [SquareRoot.Full.source_original_PC_gain_error,source_finite_donor_net_cost,finite_donor_input_net_cost]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
