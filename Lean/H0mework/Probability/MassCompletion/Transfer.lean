import H0mework.Probability.MassCompletion.Action

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointTransfer

open SourceMassCompletion SourceOwnedObservationHistory.SourceShift
open scoped InnerProductSpace
noncomputable section

abbrev wholeTransfer : Joint →L[ℂ] Joint := IsometricRetainedTransfer.transfer action
abbrev wholeResidual : Joint →L[ℂ] Joint := IsometricRetainedTransfer.residual action

theorem transfer_coordinate (value : H) (index : Nat) :
    IsometricRetainedTransfer.transfer shift value index = value (index + 1) := by
  have actual := ContinuousLinearMap.adjoint_inner_right shift.toContinuousLinearMap (basis index) value
  change ⟪basis index, IsometricRetainedTransfer.transfer shift value⟫_ℂ = ⟪shift (basis index), value⟫_ℂ at actual
  rw [shift_basis] at actual
  simp only [basis, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] at actual
  exact actual

theorem shift_coordinate (value : H) (index : Nat) : shift value (index + 1) = value index := by
  have actual := congrArg (fun point : H => point index) (IsometricRetainedTransfer.transfer_pullback shift value)
  rw [transfer_coordinate] at actual
  exact actual

theorem whole_transfer (value : Joint) :
    wholeTransfer value = WithLp.toLp 2
      (IsometricRetainedTransfer.transfer shift (firstRead value), massRead value) := by
  apply ext_inner_left ℂ
  intro left
  rw [wholeTransfer, IsometricRetainedTransfer.transfer, ContinuousLinearMap.adjoint_inner_right,
    WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  change ⟪shift (firstRead left), firstRead value⟫_ℂ + ⟪massRead left, massRead value⟫_ℂ =
    ⟪firstRead left, IsometricRetainedTransfer.transfer shift (firstRead value)⟫_ℂ + ⟪massRead left, massRead value⟫_ℂ
  rw [IsometricRetainedTransfer.transfer, ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem whole_residual (value : Joint) :
    wholeResidual value = WithLp.toLp 2
      (IsometricRetainedTransfer.residual shift (firstRead value), (0 : ℂ)) := by
  change value - action (wholeTransfer value) = _
  rw [whole_transfer]
  apply (WithLp.linearEquiv 2 ℂ (H × ℂ)).injective
  apply Prod.ext
  · rfl
  · change massRead value - massRead value = 0
    exact sub_self _

theorem shift_residual (value : H) :
    IsometricRetainedTransfer.residual shift value = value 0 • basis 0 := by
  apply lp.ext
  funext index
  change (value - shift (IsometricRetainedTransfer.transfer shift value)) index = _
  rw [lp.coeFn_sub, Pi.sub_apply]
  cases index with
  | zero => simp [basis, shift_zero_coordinate, lp.single_apply]
  | succ index =>
      rw [shift_coordinate, transfer_coordinate, sub_self]
      simp [basis, lp.single_apply]

theorem whole_residual_source (value : Joint) :
    wholeResidual value = WithLp.toLp 2 (firstRead value 0 • basis 0, (0 : ℂ)) := by
  rw [whole_residual, shift_residual]

end
end SourceJointTransfer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
