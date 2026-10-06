import H0mework.Versions.AB.Chemistry.LAlanineJointNext.ProducerElectronicGeometry
import H0mework.Versions.AB.Chemistry.LAlanineJointNext.ProducerCommutatorBound
import H0mework.Chemistry.LAlanineJointNext.DynamicsEvolutionBound

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_phase_displacement :
    ‖phaseTarget - HeldForce.Source.realizedHeld‖ < (373 : ℝ) / 10 ^ 12 := by
  have bound := EvolutionBound.frozen_conjugation_bound Source.hamiltonian sourceHamiltonian_hermitian
    HeldForce.Source.realizedHeld (Interface.duration : ℝ)
  change ‖phaseTarget - HeldForce.Source.realizedHeld‖ ≤ _ at bound
  have dt := actual_duration_bound
  have comm := actual_commutator_bound
  have product : |(Interface.duration : ℝ)| *
      ‖Source.hamiltonian * HeldForce.Source.realizedHeld - HeldForce.Source.realizedHeld * Source.hamiltonian‖ <
        ((432 : ℝ) / 10 ^ 6) * ((862 : ℝ) / 10 ^ 9) := by
    calc
      _ ≤ |(Interface.duration : ℝ)| * ((862 : ℝ) / 10 ^ 9) :=
        mul_le_mul_of_nonneg_left comm.le (abs_nonneg _)
      _ < _ := mul_lt_mul_of_pos_right dt (by norm_num)
  exact bound.trans_lt (product.trans (by norm_num))

theorem new_numerical_error_bound : ‖newNumericalResidual‖ < (15 : ℝ) / 10 ^ 10 := by
  have first := norm_sub_le_norm_sub_add_norm_sub Source.targetRealized HeldForce.Source.realizedHeld realizedInputTarget
  have second := norm_sub_le_norm_sub_add_norm_sub HeldForce.Source.realizedHeld phaseTarget realizedInputTarget
  rw [norm_sub_rev HeldForce.Source.realizedHeld phaseTarget, norm_sub_rev phaseTarget realizedInputTarget] at second
  change ‖Source.targetRealized - realizedInputTarget‖ < _
  linarith [target_delta_bound, source_phase_displacement, source_geometric_displacement]

theorem total_realization_error_bound : ‖totalRealizationResidual‖ < (1 : ℝ) / 10 ^ 8 := by
  linarith [total_error_account, new_numerical_error_bound]

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
