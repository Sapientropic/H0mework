import H0mework.Versions.X.Fock.CopyGraph.Adjoint

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyGraph

open SourceCopyProgram SourceSuccessorBoundary SourceOwnedObservationHistory.SourceShift
noncomputable section

def jointRecover (depth : Nat) (index : Index depth) : SourceMassCompletion.Joint →L[ℂ] SourceMassCompletion.Joint :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).symm.toContinuousLinearMap.comp
    (((hilbertRecover depth index).comp SourceMassCompletion.firstRead).prod SourceMassCompletion.massRead)

def recover (depth : Nat) (index : Index depth) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ SourceMassCompletion.Joint ℂ).symm.toContinuousLinearMap.comp
    (((jointRecover depth index).comp SourceJointClockGraph.joint).prod
      (((scale depth index : ℂ)⁻¹) • SourceJointClockGraph.clock))

def residual (depth : Nat) (index : Index depth) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  ContinuousLinearMap.id ℂ _ - (action depth index).comp (recover depth index)

theorem scale_nonzero (depth : Nat) (index : Index depth) : (scale depth index : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (scale_pos depth index).ne'

theorem recover_apply (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    recover depth index value = WithLp.toLp 2
      (WithLp.toLp 2 (hilbertRecover depth index (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value)),
        SourceMassCompletion.massRead (SourceJointClockGraph.joint value)),
        (scale depth index : ℂ)⁻¹ * SourceJointClockGraph.clock value) := rfl

theorem recover_action (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    recover depth index (action depth index value) = value := by
  rw [recover_apply, action_apply, joint_apply]
  change WithLp.toLp 2 (WithLp.toLp 2
    (hilbertRecover depth index (hilbertAction depth index (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value))),
      SourceMassCompletion.massRead (SourceJointClockGraph.joint value)),
    (scale depth index : ℂ)⁻¹ * ((scale depth index : ℂ) * SourceJointClockGraph.clock value)) = value
  rw [IsometricRetainedTransfer.transfer_pullback, inv_mul_cancel_left₀ (scale_nonzero depth index)]
  exact WithLp.toLp_ofLp 2 value

theorem action_recover (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    action depth index (recover depth index value) = WithLp.toLp 2
      (WithLp.toLp 2
        (hilbertAction depth index (hilbertRecover depth index (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value))),
          SourceMassCompletion.massRead (SourceJointClockGraph.joint value)), SourceJointClockGraph.clock value) := by
  rw [action_apply, recover_apply, joint_apply]
  change WithLp.toLp 2 (WithLp.toLp 2
    (hilbertAction depth index (hilbertRecover depth index (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value))),
      SourceMassCompletion.massRead (SourceJointClockGraph.joint value)),
    (scale depth index : ℂ) * ((scale depth index : ℂ)⁻¹ * SourceJointClockGraph.clock value)) = _
  rw [mul_inv_cancel_left₀ (scale_nonzero depth index)]

theorem residual_apply (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    residual depth index value = WithLp.toLp 2
      (WithLp.toLp 2 (hilbertResidual depth index (SourceMassCompletion.firstRead (SourceJointClockGraph.joint value)), (0 : ℂ)), (0 : ℂ)) := by
  change value - action depth index (recover depth index value) = _
  rw [action_recover]
  change WithLp.toLp 2 (WithLp.ofLp value) - WithLp.toLp 2 _ = _
  rw [← WithLp.toLp_sub]
  change WithLp.toLp 2
    (SourceJointClockGraph.joint value - WithLp.toLp 2 _, SourceJointClockGraph.clock value - SourceJointClockGraph.clock value) = _
  rw [sub_self]
  change WithLp.toLp 2 (WithLp.toLp 2 (WithLp.ofLp (SourceJointClockGraph.joint value)) - WithLp.toLp 2 _, (0 : ℂ)) = _
  rw [← WithLp.toLp_sub]
  change WithLp.toLp 2 (WithLp.toLp 2 (_, SourceMassCompletion.massRead (SourceJointClockGraph.joint value) -
    SourceMassCompletion.massRead (SourceJointClockGraph.joint value)), (0 : ℂ)) = _
  rw [sub_self]
  rfl

theorem reconstruction (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    action depth index (recover depth index value) + residual depth index value = value := by
  change action depth index (recover depth index value) + (value - action depth index (recover depth index value)) = value
  rw [add_comm]
  exact sub_add_cancel _ _

end
end SourceCopyGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
