import H0mework.Fock.HistoryConditional.InverseObservationHistoryModel
import H0mework.Fock.InverseDistribution.Positive

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationHistory

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem conditional_gain {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    (∑ actor : Actors runtime, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        SourceCompiledGWord.effect depth word (SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime read key))‖ ^ 2) =
    (∑ actor : Actors runtime, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        readWindow (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) (SourceCompiledWordOperator.slope_positive _)
          (window depth word (SourceConditionalNativePosterior.decoder runtime read key))‖ ^ 2) +
    ∑ actor : Actors runtime,
      ‖(((SourceInverseDistributionAction.generate read (word.map SourceCopyNativeWord.encode) (inventoryBound runtime) key).2 actor).2 : ℂ)‖ ^ 2 := by
  rw [read_window]
  exact SourceInverseDistributionLoss.conditional_cost runtime depth word read key supported

theorem double_shift_strict {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (read : Nat → Key)
    (supported : read 0 ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    (∑ actor : Actors runtime, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read 0)).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        readWindow (SourceCopyWordAffine.compile [none, none]) (by decide)
          (window depth [.inl ⟨⟩, .inl ⟨⟩] (SourceConditionalNativePosterior.decoder runtime read (read 0)))‖ ^ 2) <
    (∑ actor : Actors runtime, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read 0)).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        SourceCompiledGWord.effect depth [.inl ⟨⟩, .inl ⟨⟩]
          (SourceGWordInverse.recover depth [.inl ⟨⟩, .inl ⟨⟩] (SourceConditionalNativePosterior.decoder runtime read (read 0)))‖ ^ 2) := by
  have paid := conditional_gain runtime depth [.inl ⟨⟩, .inl ⟨⟩] read (read 0) supported
  have positive := SourceInverseDistributionLoss.double_shift_loss_positive read (inventoryBound runtime)
  change _ = _ + ∑ actor : Actors runtime,
    ‖(((SourceInverseDistributionAction.generate read [none, none] (inventoryBound runtime) (read 0)).2 actor).2 : ℂ)‖ ^ 2 at paid
  exact (lt_add_of_pos_right _ positive).trans_eq paid.symm

theorem model_feedback {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    SourceCopyNativeSharedUpdate.modelStep runtime.tick.next
      (SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
        (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next)
        (readWindow (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) (SourceCompiledWordOperator.slope_positive _)
          (window depth word (SourceConditionalNativePosterior.decoder runtime read key)))) =
      SourceConditionalNativePosterior.effect runtime read key := by
  rw [read_window, SourceConditionalNativePosterior.decoder, SourceConditionalStream.project_realization]
  rfl

theorem model_effect {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    restore depth word (SourceGeneratedActionObservationHistory.modelAction SourceJointClockGraph.action.toLinearMap
      (SourceGWordInverse.recover depth word).toLinearMap
      (SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
        (SourceGWordInverse.recover depth word).toLinearMap (SourceConditionalNativePosterior.decoder runtime read key))) =
      SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalNativePosterior.effect runtime read key) := by
  rw [model_action_restore, restore_projection, SourceConditionalNativePosterior.effect_realization]

theorem field_gain (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support) :
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - SourceCompiledGWord.effect depth word
        (SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) key))‖ ^ 2) =
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        readWindow (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)) (SourceCompiledWordOperator.slope_positive _)
          (window depth word (SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalNativeKeys.observed depth key)))‖ ^ 2) +
    ∑ actor : Actors runtime,
      ‖(((SourceInverseDistributionAction.generate (fun index : Nat => (index : ZMod 2))
        (word.map SourceCopyNativeWord.encode) (inventoryBound runtime) key).2 actor).2 : ℂ)‖ ^ 2 := by
  rw [read_window]
  exact SourceInverseDistributionLoss.field_cost runtime depth word key supported

end
end SourceInverseObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
