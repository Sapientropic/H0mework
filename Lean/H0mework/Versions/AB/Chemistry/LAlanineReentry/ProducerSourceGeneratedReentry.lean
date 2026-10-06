import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerNuclear
import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerElectronicError

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Producer

noncomputable section

theorem current_imaginary_coordinate : Source.currentImagNumerator 4 7 = 2517 :=
  JointNext.Producer.actual_imaginary_coordinate

theorem one_elapsed_clock : Continuation.targetClock - Runtime.reentryParentTime = Continuation.duration :=
  add_sub_cancel_left _ _

def reentryClosure : Prop :=
  nuclearClosure ∧
  type_of% Runtime.reentryParent_installed ∧
  type_of% Runtime.reentryParent_actual ∧
  type_of% Runtime.reentryParent_residual ∧
  type_of% Source.currentRealized_eq_parent ∧
  type_of% Source.currentRealized_channels ∧
  type_of% current_imaginary_coordinate ∧
  type_of% Continuation.targetClock_exact ∧
  type_of% one_elapsed_clock ∧
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
  type_of% total_error_account ∧
  type_of% source_phase_displacement ∧
  type_of% source_geometric_displacement ∧
  type_of% new_numerical_error_bound ∧
  type_of% total_realization_error_bound ∧
  type_of% independent_operator_commutes ∧
  type_of% scalar_energy_restriction ∧
  type_of% actual_imaginary_coordinate ∧
  type_of% targetRealized_not_real_only

theorem sourceGeneratedReentry : reentryClosure :=
  ⟨sourceGeneratedNuclearReentry, Runtime.reentryParent_installed, Runtime.reentryParent_actual,
    Runtime.reentryParent_residual, Source.currentRealized_eq_parent, Source.currentRealized_channels,
    current_imaginary_coordinate, Continuation.targetClock_exact, one_elapsed_clock,
    sourceHamiltonian_hermitian, sourceCross_close, targetRealized_hermitian,
    exactTarget_joint, exactTarget_faithful, exactTarget_trace, exactTarget_spectrum, exactTarget_hermitian,
    inherited_error_exact, inherited_error_bound, total_error_reconstruction, total_error_account,
    source_phase_displacement, source_geometric_displacement, new_numerical_error_bound,
    total_realization_error_bound, independent_operator_commutes, scalar_energy_restriction,
    actual_imaginary_coordinate, targetRealized_not_real_only⟩

end
end LAlanine40K2025.Reentry.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
