import H0mework.Fock.SourceHistory.InverseObservationNative.Packet

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationNative

open SourceGeneratedActionWords SourceCopyTimeModel SourceCopyTimeEnergy
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem model_feedback {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceCopyNativeSharedUpdate.modelStep runtime.tick.next
      (SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
        (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next)
        (restore (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) (packet runtime depth word read key))) =
      SourceConditionalNativePosterior.effect runtime read key := by
  dsimp only
  rw [packet_source]
  exact SourceInverseObservationPacket.model_feedback runtime depth word read key

theorem field_budget (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support)
    (samples : SourceCopyTimeModel.Packet ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 - 1)
      (SourceInverseObservationPacket.copyIndex (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1)) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let residual := packet runtime depth word (fun index : Nat => (index : ZMod 2)) key - samples
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - restore (program.1 - 1)
        (SourceInverseObservationPacket.copyIndex program.1) samples‖ ^ 2) +
      axisCost (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) residual =
    (∑ actor : Actors runtime, ((SourceConditionalNativeKeys.generate (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        SourceConditionalNativeKeys.decoder runtime depth (SourceConditionalNativeKeys.observed depth key)‖ ^ 2) +
      copyCost (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) residual +
        ‖mergedMass (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) residual‖ ^ 2 +
        ‖mergedClock (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) residual‖ ^ 2 := by
  dsimp only
  rw [packet_source, ← SourceConditionalNativePosterior.parity_decoder runtime depth key]
  exact SourceInverseObservationPacket.field_budget runtime depth word key supported samples

theorem next_budget {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key)
    (samples : SourceCopyTimeModel.Packet ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 - 1)
      (SourceInverseObservationPacket.copyIndex (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1)) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let residual := packet runtime depth word read key - samples
    ‖SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalNativePosterior.effect runtime read key) -
      restore (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1)
        (next (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) samples)‖ ^ 2 +
      axisCost (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1)
        (next (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) residual) =
    copyCost (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) residual +
      clockWork (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) (residual 0) +
      ‖mergedMass (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1)
        (next (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) residual)‖ ^ 2 +
      ‖mergedClock (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1)
        (next (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) residual)‖ ^ 2 := by
  dsimp only
  rw [packet_source, SourceConditionalNativePosterior.effect_realization]
  exact SourceInverseObservationPacket.next_error_budget depth word _ samples

end
end SourceInverseObservationNative
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
