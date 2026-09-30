import H0mework.Fock.HistoryConditional.MergeLossClock
import H0mework.Fock.HistoryConditional.NativeMergeActual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeMerge

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open SourceConditionalModel (Actors NextModel nextRead dynamicRead fullRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def decoder (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity) : SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
    (SourceConditionalNativeKeys.embed (inventoryBound runtime) depth (state (inventoryBound runtime)) value).2)

theorem decoder_original (runtime : LivingRuntimeState process) (depth : Nat) :
    decoder runtime depth = SourceConditionalNativeKeys.decoder runtime depth := by
  funext value
  rw [decoder, state_original]
  rfl

theorem compression_loss (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalVector.dynamicError runtime depth (decoder runtime depth) =
      (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          SourceConditionalNativeObservers.decoder runtime (fullRead runtime actor)‖ ^ 2) +
      (∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖SourceConditionalNativeObservers.decoder runtime (fullRead runtime actor) - decoder runtime depth (dynamicRead runtime depth actor)‖ ^ 2) := by
  simp only [decoder_original]
  exact SourceConditionalMergeLoss.clock_loss runtime depth

theorem information_cost (runtime : LivingRuntimeState process) (depth : Nat) :
    type_of% (SourceInformationReadback.model_decoder_cost runtime depth (decoder runtime depth)) :=
  SourceInformationReadback.model_decoder_cost runtime depth _

theorem compression_positive (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) (depth : Nat) :
    0 < SourceConditionalVector.dynamicError runtime depth (decoder runtime depth) := by
  have lower := SourceConditionalVector.dynamic_error_lower runtime enough depth (decoder runtime depth)
  have positive : 0 < (3 : ℝ) / (inventoryBound runtime + 1) := by positivity
  exact positive.trans_le lower

theorem full_mixture (runtime : LivingRuntimeState process) (key : ZMod 2)
    (supported : key ∈ (SourceConditionalHistory.observed
      (SourceConditionalHistory.observed (historyPMF (inventoryBound runtime)) (fullRead runtime)) forgetClock).support)
    (actor : Actors runtime) :
    ((state (inventoryBound runtime) key).2 actor : ℝ) =
      (SourceConditionalHistory.Coarsening.mixture (historyPMF (inventoryBound runtime)) (fullRead runtime)
        forgetClock key supported actor).toReal := by
  have same : (fun index : Actors runtime => SourceConditionalNativeObservers.clockRead 0 index.val) = fullRead runtime :=
    funext (fun index => (SourceConditionalNativeObservers.full_source runtime index).symm)
  have paid := mixture_weight (SourceConditionalNativeObservers.clockRead 0) forgetClock (inventoryBound runtime) key
    (by rw [same]; exact supported) actor
  simpa only [same, state] using paid

theorem actual_update (runtime : LivingRuntimeState process) :
    merge (SourceConditionalNativeObservers.clockRead 0) forgetClock (inventoryBound runtime.tick.next)
      (SourceConditionalNativeObservers.updated runtime) = state (inventoryBound runtime.tick.next) := by
  rw [← SourceConditionalNativeObservers.state_next]
  rfl

theorem table_next (runtime : LivingRuntimeState process) (depth : Nat) :
    SourceConditionalNativeKeys.embed (inventoryBound runtime.tick.next) depth (state (inventoryBound runtime.tick.next)) =
      SourceConditionalRationalStream.advance (inventoryBound runtime) depth
        (SourceConditionalNativeKeys.embed (inventoryBound runtime) depth (state (inventoryBound runtime))) := by
  rw [state_original, state_original]
  exact SourceConditionalNativeKeys.table_current_next runtime depth

end
end SourceConditionalNativeMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
