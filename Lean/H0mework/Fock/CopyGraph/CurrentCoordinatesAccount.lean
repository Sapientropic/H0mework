import H0mework.Fock.CopyGraph.CurrentCoordinatesRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section
attribute [local instance] SourceCopyCofinal.finiteComplete

theorem current_prediction_tail_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    residual runtime index steps (SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index steps target)) = 0 := by
  let prediction := SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index steps target)
  have tailZero : (SourceCopyCofinal.historyImages (inventoryBound runtime) index steps).starProjection
      (residual runtime index steps prediction) = 0 := by
    rw [SourceCopyCofinal.actual_projection, SourceCopyCofinal.advanced_action]
    change SourceCopyGraph.action (inventoryBound runtime) index
      (observer runtime index steps (residual runtime index steps prediction)) = 0
    rw [observer_zero runtime index steps _ (residual_source runtime index steps prediction), map_zero]
  have paired := Submodule.inner_starProjection_left_eq_right
    (SourceCopyCofinal.historyImages (inventoryBound runtime) index steps) target (residual runtime index steps prediction)
  rw [tailZero, inner_zero_right] at paired
  have actual := SourceCopyCofinal.actual_projection runtime index steps target
  rw [SourceCopyCofinal.advanced_action] at actual
  change (SourceCopyCofinal.historyImages (inventoryBound runtime) index steps).starProjection target = prediction at actual
  rw [actual] at paired
  have decomposed := congrArg (fun value : SourceJointClockGraph.Carrier => ⟪value, residual runtime index steps prediction⟫_ℂ)
    (reconstruction runtime index steps prediction)
  rw [inner_add_left, retained_orthogonal, zero_add] at decomposed
  exact inner_self_eq_zero.mp (decomposed.trans paired)

theorem original_residual_tail (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    residual runtime index steps (SourceRecordedEvolution.residual runtime index steps target) =
      residual runtime index steps target := by
  rw [SourceRecordedEvolution.residual, SourceCopyCofinal.advanced_action]
  change residual runtime index steps (target -
    SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index steps target)) = _
  rw [map_sub, current_prediction_tail_zero, sub_zero]

theorem original_residual_partition (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    retained runtime index steps (SourceRecordedEvolution.residual runtime index steps target) +
      residual runtime index steps target = SourceRecordedEvolution.residual runtime index steps target := by
  have source := reconstruction runtime index steps (SourceRecordedEvolution.residual runtime index steps target)
  rwa [original_residual_tail] at source

theorem original_residual_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖retained runtime index steps (SourceRecordedEvolution.residual runtime index steps target)‖ ^ 2 +
      ‖residual runtime index steps target‖ ^ 2 = ‖SourceRecordedEvolution.residual runtime index steps target‖ ^ 2 := by
  have source := energy runtime index steps (SourceRecordedEvolution.residual runtime index steps target)
  rwa [original_residual_tail] at source

theorem history_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖retained runtime index steps (SourceRecordedEvolution.residual runtime index steps target)‖ ^ 2 +
      ‖residual runtime index steps target‖ ^ 2 +
      ∑ stage ∈ Finset.range steps, ‖SourceRecordedEvolution.birth runtime index stage target‖ ^ 2 =
        ‖SourceRecordedEvolution.residual runtime index 0 target‖ ^ 2 := by
  rw [original_residual_budget]
  exact SourceRecordedEvolution.history_energy runtime index steps target

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
