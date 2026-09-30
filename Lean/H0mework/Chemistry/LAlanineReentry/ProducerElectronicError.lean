import H0mework.Chemistry.LAlanineReentry.ProducerElectronicGeometry
import H0mework.Chemistry.LAlanineReentry.ProducerCalculationComplexCommutatorBound

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Producer

open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_phase_displacement : ‖phaseTarget - Source.currentRealized‖ < (373 : ℝ) / 10 ^ 12 := by
  have bound := JointNext.EvolutionBound.frozen_conjugation_bound Source.hamiltonian sourceHamiltonian_hermitian
    Source.currentRealized (Continuation.duration : ℝ)
  change ‖phaseTarget - Source.currentRealized‖ ≤ _ at bound
  have product : |(Continuation.duration : ℝ)| *
      ‖Source.hamiltonian * Source.currentRealized - Source.currentRealized * Source.hamiltonian‖ <
        ((432 : ℝ) / 10 ^ 6) * ((863 : ℝ) / 10 ^ 9) := by
    calc
      _ ≤ |(Continuation.duration : ℝ)| * ((863 : ℝ) / 10 ^ 9) :=
        mul_le_mul_of_nonneg_left actual_commutator_bound.le (abs_nonneg _)
      _ < _ := mul_lt_mul_of_pos_right actual_duration_bound (by norm_num)
  exact bound.trans_lt (product.trans (by norm_num))

theorem new_numerical_error_bound : ‖newNumericalResidual‖ < (22 : ℝ) / 10 ^ 10 := by
  have first := norm_sub_le_norm_sub_add_norm_sub Source.targetRealized Source.currentRealized realizedInputTarget
  have second := norm_sub_le_norm_sub_add_norm_sub Source.currentRealized phaseTarget realizedInputTarget
  rw [norm_sub_rev Source.currentRealized phaseTarget, norm_sub_rev phaseTarget realizedInputTarget] at second
  change ‖Source.targetRealized - realizedInputTarget‖ < _
  linarith [target_delta_bound, source_phase_displacement, source_geometric_displacement]

theorem total_realization_error_bound : ‖totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 := by
  linarith [total_error_account, Runtime.reentryParent_error, new_numerical_error_bound]

end
end LAlanine40K2025.Reentry.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
