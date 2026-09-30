import H0mework.Fock.CopyGraph.Recovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyGraph

open SourceCopyProgram SourceSuccessorBoundary SourceOwnedObservationHistory.SourceShift
noncomputable section

theorem action_injective (depth : Nat) (index : Index depth) : Function.Injective (action depth index) := by
  intro left right same
  have read := congrArg (recover depth index) same
  simpa only [recover_action] using read

theorem exact_fibre (depth : Nat) (index : Index depth)
    (target proposal : SourceJointClockGraph.Carrier) :
    action depth index proposal = target ↔ proposal = recover depth index target ∧ residual depth index target = 0 := by
  constructor
  · rintro rfl
    refine ⟨(recover_action depth index proposal).symm, ?_⟩
    change action depth index proposal - action depth index (recover depth index (action depth index proposal)) = 0
    rw [recover_action, sub_self]
  · rintro ⟨rfl, vanished⟩
    simpa only [vanished, add_zero] using reconstruction depth index target

theorem action_range (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    value ∈ (action depth index).range ↔
      SourceMassCompletion.firstRead (SourceJointClockGraph.joint value) ∈ (hilbertAction depth index).toLinearMap.range := by
  constructor
  · rintro ⟨source, rfl⟩
    exact ⟨SourceMassCompletion.firstRead (SourceJointClockGraph.joint source), rfl⟩
  · rintro ⟨source, same⟩
    change hilbertAction depth index source = SourceMassCompletion.firstRead (SourceJointClockGraph.joint value) at same
    refine ⟨WithLp.toLp 2 (WithLp.toLp 2 (source, SourceMassCompletion.massRead (SourceJointClockGraph.joint value)),
      (scale depth index : ℂ)⁻¹ * SourceJointClockGraph.clock value), ?_⟩
    change action depth index (WithLp.toLp 2
      (WithLp.toLp 2 (source, SourceMassCompletion.massRead (SourceJointClockGraph.joint value)),
        (scale depth index : ℂ)⁻¹ * SourceJointClockGraph.clock value)) = value
    rw [action_apply, joint_apply]
    change WithLp.toLp 2 (WithLp.toLp 2 (hilbertAction depth index source, SourceMassCompletion.massRead (SourceJointClockGraph.joint value)),
      (scale depth index : ℂ) * ((scale depth index : ℂ)⁻¹ * SourceJointClockGraph.clock value)) = value
    rw [same, mul_inv_cancel_left₀ (scale_nonzero depth index)]
    exact WithLp.toLp_ofLp 2 value

theorem residual_norm_sq (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    ‖residual depth index value‖ ^ 2 =
      ‖hilbertResidual depth index (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value))‖ ^ 2 := by
  rw [residual_apply, WithLp.prod_norm_sq_eq_of_L2]
  change ‖WithLp.toLp 2 (_, (0 : ℂ))‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change (‖hilbertResidual depth index (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value))‖ ^ 2 +
    ‖(0 : ℂ)‖ ^ 2) + ‖(0 : ℂ)‖ ^ 2 = _
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

theorem retained_energy (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    ‖value‖ ^ 2 = ‖action depth index (recover depth index value)‖ ^ 2 + ‖residual depth index value‖ ^ 2 := by
  rw [action_recover, residual_norm_sq]
  simp only [WithLp.prod_norm_sq_eq_of_L2]
  change (‖SourceMassCompletion.firstRead (SourceJointClockGraph.joint value)‖ ^ 2 +
      ‖SourceMassCompletion.massRead (SourceJointClockGraph.joint value)‖ ^ 2) + ‖SourceJointClockGraph.clock value‖ ^ 2 =
    (‖hilbertAction depth index (hilbertRecover depth index (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value)))‖ ^ 2 +
      ‖SourceMassCompletion.massRead (SourceJointClockGraph.joint value)‖ ^ 2) + ‖SourceJointClockGraph.clock value‖ ^ 2 +
      ‖hilbertResidual depth index (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value))‖ ^ 2
  rw [(hilbertAction depth index).norm_map]
  have original := IsometricRetainedTransfer.energy_decomposition (hilbertAction depth index)
    (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value))
  linarith only [original]

theorem source_norm_le (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    ‖value‖ ≤ ‖action depth index value‖ := by
  have positive : (1 : ℝ) ≤ scale depth index := by exact_mod_cast scale_pos depth index
  have extra : 0 ≤ ((scale depth index : ℝ) ^ 2 - 1) * ‖SourceJointClockGraph.clock value‖ ^ 2 :=
    mul_nonneg (by nlinarith) (sq_nonneg _)
  have energy := action_energy depth index value
  nlinarith [norm_nonneg value, norm_nonneg (action depth index value)]

end
end SourceCopyGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
