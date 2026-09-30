import H0mework.Versions.X.Fock.CopyGraph.ConditionalGeometry

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraph

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyProgram (Index scale)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem copy_transferred (depth bound : Nat) (index : Index depth) (value : Space (historyPMF bound)) :
    SourceCopyGraph.action depth index (fieldRead depth bound (Actor.currentTransfer depth bound value)) =
      copyRead depth bound index value := by
  change SourceCopyGraph.action depth index
    (SourceJointClockGraph.read (word depth bound (Actor.currentTransfer depth bound value))) = _
  rw [word_from_actor]
  rfl

theorem original_compression_error (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : FieldSpace depth bound) :
    let task := Actor.currentPullback depth bound value
    let restored := Actor.currentTransfer depth bound
      (pullback (historyPMF bound) observer (transfer (historyPMF bound) observer task))
    let remaining := Actor.currentTransfer depth bound (residual (historyPMF bound) observer task)
    ‖SourceCopyGraph.action depth index (fieldRead depth bound value) -
      SourceCopyGraph.action depth index (fieldRead depth bound restored)‖ ^ 2 =
        ‖remaining‖ ^ 2 + (scale depth index : ℝ) ^ 2 * ‖SourceClockComplex.clock (word depth bound remaining)‖ ^ 2 := by
  dsimp only
  rw [copy_transferred, actor_transfer_norm, word_from_actor]
  exact compression_graph_error depth bound index observer (Actor.currentPullback depth bound value)

theorem original_residual_mass (depth bound : Nat) (observer : Fin (bound + 1) → Observed)
    (value : FieldSpace depth bound) :
    SourceSuccessorBoundary.mass ℂ (word depth bound (Actor.currentTransfer depth bound
      (residual (historyPMF bound) observer (Actor.currentPullback depth bound value)))) = 0 := by
  rw [word_from_actor]
  exact residual_mass bound observer _

theorem original_clock_conditional (depth bound : Nat) (observer : Fin (bound + 1) → Observed) (atom : Observed)
    (supported : atom ∈ (observed (historyPMF bound) observer).support) :
    transfer (historyPMF bound) observer
      (Actor.currentPullback depth bound (SourceGeneratedJointClock.currentClock depth bound)) atom =
      ∑ actor : Fin (bound + 1),
        (SourceConditionalHistory.conditional (historyPMF bound) observer atom supported actor).toReal •
          SourceGeneratedJointClock.signal bound actor := by
  rw [SourceGeneratedJointClock.currentClock, actor_transfer_samples]
  exact clock_conditional bound observer atom supported

theorem original_residual_bound (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : FieldSpace depth bound) :
    let remaining := Actor.currentTransfer depth bound
      (residual (historyPMF bound) observer (Actor.currentPullback depth bound value))
    let clockRemaining := Actor.currentTransfer depth bound
      (residual (historyPMF bound) observer (taskValue (historyPMF bound) (SourceGeneratedJointClock.signal bound)))
    ‖SourceCopyGraph.action depth index (fieldRead depth bound remaining)‖ ^ 2 ≤
      (1 + (scale depth index : ℝ) ^ 2 * (bound + 1 : ℝ) * ‖clockRemaining‖ ^ 2) * ‖remaining‖ ^ 2 := by
  dsimp only
  rw [copy_transferred, actor_transfer_norm, actor_transfer_norm]
  exact residual_graph_bound depth bound index observer (Actor.currentPullback depth bound value)

end
end SourceConditionalGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
