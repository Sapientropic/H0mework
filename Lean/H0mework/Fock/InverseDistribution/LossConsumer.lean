import H0mework.Fock.InverseDistribution.LossSource
import H0mework.Fock.HistoryConditional.NativePosteriorField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionLoss

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem conditional_cost {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    (∑ actor : Actors runtime, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime read key))‖ ^ 2) =
    (∑ actor : Actors runtime, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - SourceConditionalNativePosterior.decoder runtime read key‖ ^ 2) +
    ∑ actor : Actors runtime,
      ‖(((SourceInverseDistributionAction.generate read (word.map SourceCopyNativeWord.encode) (inventoryBound runtime) key).2 actor).2 : ℂ)‖ ^ 2 := by
  rw [← generated_residual_norm runtime depth word read key]
  exact SourceConditionalNativePosterior.error_decomposition runtime read key supported _

theorem field_cost (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support) :
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - SourceCompiledGWord.effect depth word
        (SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) key))‖ ^ 2) =
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalNativeKeys.observed depth key)‖ ^ 2) +
    ∑ actor : Actors runtime,
      ‖(((SourceInverseDistributionAction.generate (fun index : Nat => (index : ZMod 2))
        (word.map SourceCopyNativeWord.encode) (inventoryBound runtime) key).2 actor).2 : ℂ)‖ ^ 2 := by
  rw [← generated_residual_norm runtime depth word (fun index : Nat => (index : ZMod 2)) key]
  have paid := SourceConditionalNativePosterior.field_error runtime depth key supported
    (SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word
      (SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) key)))
  rw [SourceConditionalNativePosterior.parity_decoder] at paid ⊢
  exact paid

theorem model_feedback {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    SourceCopyNativeSharedUpdate.modelStep runtime.tick.next
      (SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
        (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next)
        (SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime read key)) +
          SourceGWordInverse.residual depth word (SourceConditionalNativePosterior.decoder runtime read key))) =
      SourceConditionalNativePosterior.effect runtime read key := by
  rw [SourceGWordInverse.reconstruction, SourceConditionalNativePosterior.decoder, SourceConditionalStream.project_realization]
  rfl

end
end SourceInverseDistributionLoss
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
