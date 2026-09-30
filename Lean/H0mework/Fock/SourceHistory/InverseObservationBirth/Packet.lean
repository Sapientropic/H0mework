import H0mework.Fock.SourceHistory.InverseObservationBirth.Source
import H0mework.Fock.SourceHistory.InverseObservationNative.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationBirth

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def packet {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceCopyTimeModel.Packet (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) :=
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  let bound := inventoryBound runtime
  fun phase => SourceInverseObservationNative.realize (bound + 1) program (program.2 + phase.val)
    (birth read bound program (program.2 + phase.val)
      (SourceInverseObservationNative.generate read (word.map SourceCopyNativeWord.encode) bound phase.val) key).2

theorem packet_next {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    packet runtime depth word read key = SourceInverseObservationNative.packet runtime.tick.next depth word read key := by
  funext phase
  dsimp only [packet, SourceInverseObservationNative.packet]
  rw [birth_generated, SourceActualImageStep.next_bound]

theorem recovered {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceCopyTimeModel.restore (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1)
      (packet runtime depth word read key) = SourceConditionalNativePosterior.decoder runtime.tick.next read key := by
  dsimp only
  rw [packet_next, SourceInverseObservationNative.recovered]

theorem model_feedback {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceCopyNativeSharedUpdate.modelStep runtime.tick.next.tick.next
      (SourceGeneratedActionObservationHistory.projection SourceJointClockGraph.action.toLinearMap
        (SourceCopyCurrentCoordinates.jointObserver runtime.tick.next.tick.next)
        (SourceCopyTimeModel.restore (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1)
          (packet runtime depth word read key))) = SourceConditionalNativePosterior.effect runtime.tick.next read key := by
  dsimp only
  rw [packet_next]
  exact SourceInverseObservationNative.model_feedback runtime.tick.next depth word read key

end
end SourceInverseObservationBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
