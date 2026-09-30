import H0mework.Fock.SourceHistory.InverseObservationNative.Moments
import H0mework.Fock.HistoryConditional.InverseObservationPacket.Conditional

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationNative

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def packet {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceCopyTimeModel.Packet (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1) :=
  let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
  fun phase => realize (inventoryBound runtime) program (program.2 + phase.val)
    (generate read (word.map SourceCopyNativeWord.encode) (inventoryBound runtime) phase.val key).2

theorem packet_source {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    packet runtime depth word read key =
      SourceInverseObservationPacket.packet depth word (SourceConditionalNativePosterior.decoder runtime read key) := by
  funext phase
  change realize (inventoryBound runtime) _ _
    (generate read (word.map SourceCopyNativeWord.encode) (inventoryBound runtime) phase.val key).2 = _
  rw [generated_source, realize_fromState, SourceConditionalNativeBirth.decoder_word]
  rfl

theorem recovered {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceCopyTimeModel.restore (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1)
      (packet runtime depth word read key) = SourceConditionalNativePosterior.decoder runtime read key := by
  dsimp only
  rw [packet_source, SourceInverseObservationPacket.recovered]

theorem model_effect {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    let program := SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode)
    SourceCopyTimeModel.restore (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1)
      (SourceCopyTimeModel.next (program.1 - 1) (SourceInverseObservationPacket.copyIndex program.1)
        (packet runtime depth word read key)) =
      SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalNativePosterior.effect runtime read key) := by
  dsimp only
  rw [packet_source]
  exact SourceInverseObservationPacket.model_effect runtime depth word read key

end
end SourceInverseObservationNative
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
