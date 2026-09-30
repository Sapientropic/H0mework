import H0mework.Realization.ObservationActions.HilbertCore

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.Hilbert

open SourceGeneratedActionObservationHistory
open scoped InnerProductSpace

noncomputable section

universe r u

variable {𝕜 : Type r} [RCLike 𝕜]
variable {C B : Type u} [NormedAddCommGroup C] [InnerProductSpace 𝕜 C] [CompleteSpace C]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]
variable (action : C →L[𝕜] C) (observation : C →L[𝕜] B)

local instance actionClosedKernel :
    IsClosed (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap) : Set C) :=
  kernel_closed action observation

local instance actionCompleteKernel :
    CompleteSpace (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap)) :=
  (kernel_closed action observation).isComplete.completeSpace_coe

theorem projection_recover (model : Model action.toLinearMap observation.toLinearMap) :
    projection action.toLinearMap observation.toLinearMap (recover action observation model) = model :=
  Submodule.mk_quotientEquivOfIsCompl_apply
    (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap)).isCompl_orthogonal model

theorem norm_recover (model : Model action.toLinearMap observation.toLinearMap) :
    ‖recover action observation model‖ = ‖model‖ :=
  (realization action observation).norm_map model

theorem recover_complete_history (value : C) (stage : Nat) :
    observation ((action.toLinearMap ^ stage)
        (recover action observation (projection action.toLinearMap observation.toLinearMap value))) =
      observation ((action.toLinearMap ^ stage) value) :=
  (model_fibre_iff action.toLinearMap observation.toLinearMap _ _).mp
    (projection_recover action observation _) stage

theorem recovery_exact_iff (value : C) :
    recover action observation (projection action.toLinearMap observation.toLinearMap value) = value ↔
      residual action observation value = 0 := by
  have reconstruction := recover_residual action observation value
  constructor
  · intro same
    rw [same] at reconstruction
    exact add_right_cancel (reconstruction.trans (zero_add value).symm)
  · intro vanished
    simpa only [vanished, zero_add] using reconstruction

theorem modelAction_norm_le (model : Model action.toLinearMap observation.toLinearMap) :
    ‖modelAction action.toLinearMap observation.toLinearMap model‖ ≤ ‖action‖ * ‖model‖ := by
  have square := modelAction_source action.toLinearMap observation.toLinearMap
    (recover action observation model)
  rw [projection_recover] at square
  rw [square]
  calc
    _ ≤ ‖action (recover action observation model)‖ := Submodule.Quotient.norm_mk_le
      (LinearMap.ker (sourceMap action.toLinearMap observation.toLinearMap)) _
    _ ≤ ‖action‖ * ‖recover action observation model‖ := action.le_opNorm _
    _ = _ := by rw [norm_recover]

theorem modelReadout_norm_le (model : Model action.toLinearMap observation.toLinearMap) :
    ‖modelReadout action.toLinearMap observation.toLinearMap model‖ ≤ ‖observation‖ * ‖model‖ := by
  have square := modelReadout_projection action.toLinearMap observation.toLinearMap
    (recover action observation model)
  rw [projection_recover] at square
  rw [square]
  calc
    _ ≤ ‖observation‖ * ‖recover action observation model‖ := observation.le_opNorm _
    _ = _ := by rw [norm_recover]

theorem modelAction_continuous :
    Continuous (modelAction action.toLinearMap observation.toLinearMap) :=
  ((modelAction action.toLinearMap observation.toLinearMap).mkContinuous ‖action‖
    (modelAction_norm_le action observation)).continuous

theorem recover_action (model : Model action.toLinearMap observation.toLinearMap) :
    recover action observation (modelAction action.toLinearMap observation.toLinearMap model) =
      recover action observation (projection action.toLinearMap observation.toLinearMap
        (action (recover action observation model))) := by
  have square := modelAction_source action.toLinearMap observation.toLinearMap
    (recover action observation model)
  rw [projection_recover] at square
  exact congrArg (recover action observation) square

end
end SourceGeneratedActionObservationHistory.Hilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
