import H0mework.Versions.X.Fock.ReceivedStep.EncodingTime

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

def completeSamples (bound stride : Nat) (data : (Fin ((bound + 1) * (stride + 1)) → ℚ) × ℚ × ℚ) :
    SourceRationalWindowReadout.Samples bound (stride + 1) :=
  fun phase => SourceFiniteObserverCalculation.solve bound (stride + 1) (timeResponse bound stride data phase.val)

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

theorem solved_pairing (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (response : Fin (inventoryBound runtime + steps + 1) → ℚ) (actor : Fin (inventoryBound runtime + steps + 1)) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val,
      SourceCopyGraph.action (inventoryBound runtime) index
        (SourceFiniteObserverCalculation.finiteRead (inventoryBound runtime + steps)
          (fun source => (SourceFiniteObserverCalculation.solve (inventoryBound runtime + steps) (index.val + 1) response source : ℂ)))⟫_ℂ =
      (response actor : ℂ) := by
  rw [SourceFiniteObserverCalculation.finite_pairing]
  have equation := congrArg (fun value : ℚ => (value : ℂ))
    (SourceFiniteObserverCalculation.solve_equation (inventoryBound runtime + steps) (index.val + 1) response actor)
  simpa only [SourceFiniteObserverCalculation.weight, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_sum,
    Rat.cast_natCast, Rat.cast_one] using equation

theorem complete_observer (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (data : (Fin ((inventoryBound runtime + steps + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ) (phase : Fin (index.val + 2)) :
    SourceFiniteObserverCalculation.finiteRead (inventoryBound runtime + steps)
      (fun actor => (completeSamples (inventoryBound runtime + steps) index.val data phase actor : ℂ)) =
        observer runtime index steps (SourceCopyTimeModel.time phase.val (completeValue runtime index steps data)) := by
  rw [SourceFiniteObservationMinimum.observer_frame]
  apply SourceFiniteObserverCalculation.finite_unique runtime index steps
  intro actor
  rw [show completeSamples (inventoryBound runtime + steps) index.val data phase =
      SourceFiniteObserverCalculation.solve (inventoryBound runtime + steps) (index.val + 1)
        (timeResponse (inventoryBound runtime + steps) index.val data phase.val) from rfl,
    solved_pairing, time_response_source]
  have original := SourceCopySharedNext.observed_columns runtime index steps actor
    (SourceCopyTimeModel.time phase.val (completeValue runtime index steps data))
  rw [SourceFiniteObservationMinimum.observer_frame] at original
  exact original.symm

theorem complete_samples_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (data : (Fin ((inventoryBound runtime + steps + 1) * (index.val + 1)) → ℚ) × ℚ × ℚ) :
    SourceRationalWindowReadout.embed runtime index steps (completeSamples (inventoryBound runtime + steps) index.val data) =
      SourceCopyTemporalBoundary.recordedPrefix runtime index steps (index.val + 1) (completeValue runtime index steps data) := by
  funext phase
  change SourceFiniteObserverCalculation.finiteRead _ _ = _
  rw [complete_observer, SourceCopyTemporalBoundary.prefix_source]

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
