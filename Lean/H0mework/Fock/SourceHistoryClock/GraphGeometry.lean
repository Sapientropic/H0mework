import H0mework.Fock.SourceHistoryClock.GraphAction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointClockGraph

open SourceJointTransfer SourceOwnedObservationHistory SourceOwnedObservationHistory.SourceShift
open scoped InnerProductSpace
noncomputable section

theorem norm_sq (value : Carrier) : ‖value‖ ^ 2 = ‖joint value‖ ^ 2 + ‖clock value‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 value

theorem action_energy (value : Carrier) :
    ‖action value‖ ^ 2 = ‖value‖ ^ 2 + ‖SourceMassCompletion.massRead (joint value)‖ ^ 2 +
      2 * (inner ℂ (clock value) (SourceMassCompletion.massRead (joint value))).re := by
  rw [action_apply, WithLp.prod_norm_sq_eq_of_L2]
  change ‖SourceMassCompletion.action (joint value)‖ ^ 2 +
    ‖clock value + SourceMassCompletion.massRead (joint value)‖ ^ 2 = _
  rw [SourceMassCompletion.action.norm_map, norm_add_sq (𝕜 := ℂ), SourceJointClockGraph.norm_sq value]
  change ‖joint value‖ ^ 2 + (‖clock value‖ ^ 2 +
    2 * (inner ℂ (clock value) (SourceMassCompletion.massRead (joint value))).re +
      ‖SourceMassCompletion.massRead (joint value)‖ ^ 2) = _
  ring

theorem residual_norm_sq (value : Carrier) :
    ‖residual value‖ ^ 2 = ‖SourceMassCompletion.firstRead (joint value) 0‖ ^ 2 := by
  rw [residual_formula, WithLp.prod_norm_sq_eq_of_L2]
  change ‖wholeResidual (joint value)‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2 = _
  rw [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  exact SourceJointTransfer.residual_norm_sq (joint value)

theorem retained_energy (value : Carrier) :
    ‖value‖ ^ 2 = ‖action (recover value)‖ ^ 2 + ‖residual value‖ ^ 2 := by
  rw [SourceJointClockGraph.norm_sq value, action_recover,
    WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2
      (SourceMassCompletion.action (wholeTransfer (joint value)), clock value))]
  change ‖joint value‖ ^ 2 + ‖clock value‖ ^ 2 =
    (‖SourceMassCompletion.action (wholeTransfer (joint value))‖ ^ 2 + ‖clock value‖ ^ 2) + ‖residual value‖ ^ 2
  rw [SourceMassCompletion.action.norm_map, residual_norm_sq]
  have original := SourceJointTransfer.whole_energy (joint value)
  linarith only [original]

theorem clock_unit_not_finite :
    WithLp.toLp 2 ((0 : SourceMassCompletion.Joint), (1 : ℂ)) ∉ read.range := by
  rintro ⟨word, same⟩
  have first := congrArg joint same
  change SourceMassCompletion.jointRead word = 0 at first
  have zeroWord : word = 0 := SourceMassCompletion.jointRead_injective (first.trans (map_zero _).symm)
  have second := congrArg clock same
  change SourceClockComplex.clock word = 1 at second
  rw [zeroWord, map_zero] at second
  exact zero_ne_one second

theorem root_unit_recovery :
    recover (read (SourceClockComplex.ofNative (sourcePoint 0))) =
      WithLp.toLp 2 (WithLp.toLp 2 ((0 : H), (1 : ℂ)), (0 : ℂ)) := by
  rw [native_read, recover_apply]
  change WithLp.toLp 2 (wholeTransfer (SourceMassCompletion.nativeRead (sourcePoint 0)),
    (SourceClockModel.clockRead (SourceClockModel.projection (sourcePoint 0)) : ℂ) -
      SourceMassCompletion.massRead (SourceMassCompletion.nativeRead (sourcePoint 0))) = _
  rw [SourceJointTransfer.root_unit_transfer, SourceMassCompletion.massRead_native, SourceClockModel.clockRead_source]
  norm_num [sourcePoint, SourceClockModel.clock_single, SourceSuccessorBoundary.mass_single]

theorem root_unit_not_in_range :
    read (SourceClockComplex.ofNative (sourcePoint 0)) ∉ action.toLinearMap.range := by
  rw [range_joint_iff, joint_source, SourceClockComplex.joint_native]
  exact SourceJointTransfer.root_unit_not_in_range

theorem root_unit_energy_gain :
    ‖action (read (SourceClockComplex.ofNative (sourcePoint 0)))‖ ^ 2 =
      ‖read (SourceClockComplex.ofNative (sourcePoint 0))‖ ^ 2 + 3 := by
  rw [action_energy, joint_source, clock_source, SourceClockComplex.joint_native,
    SourceClockComplex.clock_native, SourceMassCompletion.massRead_native]
  norm_num [sourcePoint, SourceClockModel.clock_single, SourceSuccessorBoundary.mass_single, inner]
  ring

theorem action_not_norm_preserving : ¬ ∀ value : Carrier, ‖action value‖ = ‖value‖ := by
  intro preserved
  have actual := root_unit_energy_gain
  rw [preserved] at actual
  linarith

end
end SourceJointClockGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
