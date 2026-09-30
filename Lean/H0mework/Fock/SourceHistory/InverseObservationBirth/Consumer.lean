import H0mework.Fock.SourceHistory.InverseObservationBirth.Update

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationBirth

open SourceGeneratedActionWords SourceCopyTimeModel SourceCopyTimeEnergy
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem field_budget (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (key : ZMod 2)
    (supported : key ∈ ((historyPMF (inventoryBound runtime.tick.next)).map
      (fun actor : Actors runtime.tick.next => (actor.val : ZMod 2))).support)
    (samples : SourceCopyTimeModel.Packet ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 - 1)
      (SourceInverseObservationPacket.copyIndex (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1)) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let residual := packet runtime depth word (fun index : Nat => (index : ZMod 2)) key - samples
    (∑ actor : Actors runtime.tick.next, ((SourceConditionalNativeKeys.generate (inventoryBound runtime.tick.next) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime.tick.next (nextRead runtime.tick.next actor) - restore (program.1 - 1)
        (SourceInverseObservationPacket.copyIndex program.1) samples‖ ^ 2) +
      axisCost (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) residual =
    (∑ actor : Actors runtime.tick.next, ((SourceConditionalNativeKeys.generate (inventoryBound runtime.tick.next) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime.tick.next (nextRead runtime.tick.next actor) -
        SourceConditionalNativeKeys.decoder runtime.tick.next depth (SourceConditionalNativeKeys.observed depth key)‖ ^ 2) +
      copyCost (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) residual +
        ‖mergedMass (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) residual‖ ^ 2 +
        ‖mergedClock (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) residual‖ ^ 2 := by
  dsimp only
  rw [packet_next]
  exact SourceInverseObservationNative.field_budget runtime.tick.next depth word key supported samples

theorem next_budget {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key)
    (samples : SourceCopyTimeModel.Packet ((SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1 - 1)
      (SourceInverseObservationPacket.copyIndex (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)).1)) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    let residual := packet runtime depth word read key - samples
    ‖SourceConditionalVector.realizeModel runtime.tick.next.tick.next (SourceConditionalNativePosterior.effect runtime.tick.next read key) -
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
  rw [packet_next]
  exact SourceInverseObservationNative.next_budget runtime.tick.next depth word read key samples

end
end SourceInverseObservationBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
