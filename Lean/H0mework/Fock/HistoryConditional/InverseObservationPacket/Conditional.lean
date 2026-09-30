import H0mework.Fock.HistoryConditional.InverseObservationPacket.Consumer
import H0mework.Fock.HistoryConditional.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationPacket

open SourceGeneratedActionWords SourceCopyTimeModel SourceCopyTimeEnergy
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem conditional_budget {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support)
    (samples : SourceCopyTimeModel.Packet ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 - 1)
      (copyIndex (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1)) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let residual := packet depth word (SourceConditionalNativePosterior.decoder runtime read key) - samples
    (∑ actor : Actors runtime, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - restore (program.1 - 1) (copyIndex program.1) samples‖ ^ 2) +
      axisCost (program.1 - 1) (copyIndex program.1) residual =
    (∑ actor : Actors runtime, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - SourceConditionalNativePosterior.decoder runtime read key‖ ^ 2) +
      copyCost (program.1 - 1) (copyIndex program.1) residual +
        ‖mergedMass (program.1 - 1) (copyIndex program.1) residual‖ ^ 2 +
        ‖mergedClock (program.1 - 1) (copyIndex program.1) residual‖ ^ 2 := by
  dsimp only
  rw [SourceConditionalNativePosterior.error_decomposition runtime read key supported, add_assoc, error_budget]
  ring

theorem model_feedback {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceCopyNativeSharedUpdate.modelStep runtime.tick.next
      (SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
        (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next)
        (restore (program.1 - 1) (copyIndex program.1) (packet depth word (SourceConditionalNativePosterior.decoder runtime read key)))) =
      SourceConditionalNativePosterior.effect runtime read key := by
  dsimp only
  rw [recovered, SourceConditionalNativePosterior.decoder, SourceConditionalStream.project_realization]
  rfl

theorem model_effect {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    restore (program.1 - 1) (copyIndex program.1)
      (next (program.1 - 1) (copyIndex program.1) (packet depth word (SourceConditionalNativePosterior.decoder runtime read key))) =
      SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalNativePosterior.effect runtime read key) := by
  dsimp only
  rw [next_recovered, SourceConditionalNativePosterior.effect_realization]

theorem field_budget (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support)
    (samples : SourceCopyTimeModel.Packet ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 - 1)
      (copyIndex (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1)) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let residual := packet depth word (SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalNativeKeys.observed depth key)) - samples
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - restore (program.1 - 1) (copyIndex program.1) samples‖ ^ 2) +
      axisCost (program.1 - 1) (copyIndex program.1) residual =
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalNativeKeys.observed depth key)‖ ^ 2) +
      copyCost (program.1 - 1) (copyIndex program.1) residual +
        ‖mergedMass (program.1 - 1) (copyIndex program.1) residual‖ ^ 2 +
        ‖mergedClock (program.1 - 1) (copyIndex program.1) residual‖ ^ 2 := by
  dsimp only
  rw [SourceConditionalNativePosterior.parity_decoder]
  exact conditional_budget runtime depth word (fun index : Nat => (index : ZMod 2)) key supported samples

end
end SourceInverseObservationPacket
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
