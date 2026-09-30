import H0mework.Probability.MassCompletion.Transfer
import H0mework.Probability.MassCompletion.Native

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointTransfer

open SourceMassCompletion SourceOwnedObservationHistory.SourceShift SourceOwnedObservationHistory
noncomputable section

theorem residual_norm_sq (value : Joint) : ‖wholeResidual value‖ ^ 2 = ‖firstRead value 0‖ ^ 2 := by
  rw [whole_residual_source, WithLp.prod_norm_sq_eq_of_L2]
  change ‖firstRead value 0 • basis 0‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2 = _
  have unit : ‖basis 0‖ = 1 := by
    change ‖place 0 (1 : ℂ)‖ = 1
    rw [(place 0).norm_map, norm_one]
  rw [norm_smul, unit, mul_one, norm_zero, zero_pow (by decide), add_zero]

theorem whole_energy (value : Joint) :
    ‖value‖ ^ 2 = ‖wholeTransfer value‖ ^ 2 + ‖firstRead value 0‖ ^ 2 := by
  have actual := IsometricRetainedTransfer.energy_decomposition action value
  rw [residual_norm_sq] at actual
  exact actual

theorem action_range (value : Joint) :
    value ∈ action.toLinearMap.range ↔ firstRead value 0 = 0 := by
  rw [← IsometricRetainedTransfer.residual_zero_iff action value]
  constructor
  · intro zero
    have energy := residual_norm_sq value
    rw [zero, norm_zero, zero_pow (by decide)] at energy
    have normZero : ‖firstRead value 0‖ = 0 := by nlinarith [norm_nonneg (firstRead value 0)]
    exact norm_eq_zero.mp normZero
  · intro zero
    rw [whole_residual_source, zero, zero_smul]
    rfl

theorem root_unit_transfer :
    wholeTransfer (nativeRead (sourcePoint 0)) = WithLp.toLp 2 ((0 : H), (1 : ℂ)) := by
  rw [nativeRead_point, jointRead_single, one_smul, whole_transfer]
  change WithLp.toLp 2 (IsometricRetainedTransfer.transfer shift (basis 0), (1 : ℂ)) = _
  rw [adjoint_basis_zero]

theorem root_unit_residual :
    wholeResidual (nativeRead (sourcePoint 0)) = WithLp.toLp 2 (basis 0, (0 : ℂ)) := by
  rw [nativeRead_point, jointRead_single, one_smul, whole_residual_source]
  change WithLp.toLp 2 (basis 0 0 • basis 0, (0 : ℂ)) = _
  simp [basis, lp.single_apply]

theorem root_unit_not_in_range : nativeRead (sourcePoint 0) ∉ action.toLinearMap.range := by
  rw [action_range, nativeRead_point, jointRead_single, one_smul]
  change basis 0 0 ≠ 0
  simp [basis, lp.single_apply]

end
end SourceJointTransfer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
