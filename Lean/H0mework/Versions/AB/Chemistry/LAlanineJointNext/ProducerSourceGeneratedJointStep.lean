import H0mework.Versions.AB.Chemistry.LAlanineJointNext.ProducerNuclear
import H0mework.Versions.AB.Chemistry.LAlanineJointNext.ProducerNuclearKinetic
import H0mework.Versions.AB.Chemistry.LAlanineJointNext.ProducerElectronicError
import H0mework.Chemistry.LAlanineJointNext.RegressionRealEvolution

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

noncomputable section

/-- One source-fixed discrete joint step, with a faithful exact state and its separately accounted realization. -/
def jointClosure : Prop :=
  nuclearClosure ∧
  type_of% targetKineticResidual_bound ∧
  type_of% currentKinetic_reuses_parent ∧
  type_of% targetKinetic_reconstruction ∧
  type_of% targetMechanicalEnergyWholeAccount ∧
  type_of% Runtime.jointParent_actualInputs ∧
  type_of% Runtime.jointParent_installedFaces ∧
  type_of% Runtime.jointParent_firstForce_trace ∧
  type_of% Interface.targetClock_exact ∧
  type_of% Interface.one_elapsed_clock ∧
  type_of% Interface.elapsed_not_doubled ∧
  type_of% sourceHamiltonian_hermitian ∧
  type_of% sourceCross_close ∧
  type_of% targetRealized_hermitian ∧
  type_of% exactTarget_joint ∧
  type_of% exactTarget_faithful ∧
  type_of% exactTarget_trace ∧
  type_of% exactTarget_spectrum ∧
  type_of% exactTarget_hermitian ∧
  type_of% inherited_error_exact ∧
  type_of% inherited_error_bound ∧
  type_of% total_error_reconstruction ∧
  type_of% source_phase_displacement ∧
  type_of% source_geometric_displacement ∧
  type_of% new_numerical_error_bound ∧
  type_of% total_realization_error_bound ∧
  type_of% independent_operator_commutes ∧
  type_of% scalar_energy_restriction ∧
  type_of% actual_imaginary_coordinate ∧
  type_of% targetRealized_not_real_only

theorem sourceGeneratedJointStep : jointClosure :=
  ⟨sourceGeneratedNuclearJointStep,
    targetKineticResidual_bound, currentKinetic_reuses_parent,
    targetKinetic_reconstruction, targetMechanicalEnergyWholeAccount,
    Runtime.jointParent_actualInputs, Runtime.jointParent_installedFaces,
    Runtime.jointParent_firstForce_trace, Interface.targetClock_exact,
    Interface.one_elapsed_clock, Interface.elapsed_not_doubled,
    sourceHamiltonian_hermitian, sourceCross_close, targetRealized_hermitian,
    exactTarget_joint, exactTarget_faithful, exactTarget_trace, exactTarget_spectrum,
    exactTarget_hermitian, inherited_error_exact, inherited_error_bound,
    total_error_reconstruction, source_phase_displacement, source_geometric_displacement,
    new_numerical_error_bound, total_realization_error_bound,
    independent_operator_commutes, scalar_energy_restriction,
    actual_imaginary_coordinate, targetRealized_not_real_only⟩

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
